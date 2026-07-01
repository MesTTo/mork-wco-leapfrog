//! Zipper-native worst-case-optimal unification leapfrog over variable-width MORK terms.
//!
//! Upstream MORK answers a conjunctive query with the ProductZipper, a product/nested join that
//! materializes intermediate results before pruning them. This module instead seeks directly,
//! variable-at-a-time, on the PathMap byte-trie: a join variable's
//! value is a variable-width subterm, found by descending the trie with `child_mask` +
//! `descend_to_byte`, its boundary tracked by a parse stack, and a stored variable in the data
//! is a wildcard that unifies. No domain is materialized.
//!
//! Built bottom-up, each layer validated before the next: the byte-scan and the subterm parser
//! here, then the zipper subterm cursor, then the unification leapfrog, gated against the
//! ProductZipper.

use pathmap::utils::ByteMask;
use pathmap::zipper::{Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving};
use pathmap::PathMap;
use std::collections::BTreeSet;

// MORK tag bytes (top two bits select the tag).
const TOP2: u8 = 0b1100_0000;
const TAG_ARITY: u8 = 0b0000_0000;
const TAG_VARREF: u8 = 0b1000_0000;
const TAG_SYMSIZE: u8 = 0b1100_0000;
const NEWVAR_BYTE: u8 = 0b1100_0000;
const LOW6: u8 = 0b0011_1111;

/// The least byte present in `mask` that is `>= k`, or `None` if every set bit is below `k`.
/// `ByteMask::next_bit` returns the least bit strictly above its argument, so test `k` itself
/// first. This is the per-byte leapfrog seek on a trie node's children.
#[inline]
pub fn least_ge(mask: &ByteMask, k: u8) -> Option<u8> {
    if (mask.0[(k >> 6) as usize] >> (k & 63)) & 1 == 1 {
        Some(k)
    } else {
        mask.next_bit(k)
    }
}

/// Parse the first complete subterm at `bytes[0..]`, returning its byte length and whether it is
/// ground. The encoding is prefix-free: an `Arity(k)` consumes the next `k` subterms, a
/// `SymbolSize(s)` consumes `s` payload bytes, a `VarRef`/`NewVar` is one byte. Walking a "need one
/// more complete term" counter to zero gives the span. Panics on a truncated term.
#[inline]
fn parse_first_subterm(bytes: &[u8]) -> (usize, bool) {
    let mut i = 0usize;
    let mut remaining = 1usize;
    let mut ground = true;
    while remaining > 0 {
        let b = bytes[i];
        i += 1;
        remaining -= 1;
        match b & TOP2 {
            TAG_ARITY => remaining += (b & LOW6) as usize,
            TAG_VARREF => ground = false,
            _ => {
                // 0b11xxxxxx: NewVar (exactly 0xC0) is a one-byte variable; SymbolSize carries `s`
                // payload bytes.
                if b == NEWVAR_BYTE {
                    ground = false;
                } else {
                    i += (b & LOW6) as usize;
                }
            }
        }
    }
    (i, ground)
}

/// Byte length of the first complete subterm at `bytes[0..]`.
pub fn first_subterm_len(bytes: &[u8]) -> usize {
    parse_first_subterm(bytes).0
}

/// Whether the first complete subterm at `bytes[0..]` is ground (contains no variable).
pub fn first_subterm_is_ground(bytes: &[u8]) -> bool {
    parse_first_subterm(bytes).1
}

/// One step of the incremental parse: consume byte `b`, updating how many complete subterms are
/// still owed (`subterms`) and how many raw symbol-payload bytes are still owed (`payload`). A
/// payload byte completes nothing; a tag byte completes one slot, then an `Arity(k)` owes `k` more
/// subterms and a `SymbolSize(s)` owes `s` payload bytes.
#[inline]
fn step_parse(b: u8, subterms: &mut usize, payload: &mut usize) {
    if *payload > 0 {
        *payload -= 1;
    } else {
        *subterms -= 1;
        match b & TOP2 {
            TAG_ARITY => *subterms += (b & LOW6) as usize,
            TAG_VARREF => {}
            _ => {
                if b != NEWVAR_BYTE {
                    *payload += (b & LOW6) as usize;
                }
            }
        }
    }
}

/// Whether `bytes` (from the column-start focus) spell exactly one complete subterm. Recomputed
/// per descent step; subterms are short, so the O(len) replay is cheap and keeps the navigation
/// free of incremental-state bugs.
#[inline]
fn is_complete(bytes: &[u8]) -> bool {
    let (mut subterms, mut payload) = (1usize, 0usize);
    for &b in bytes {
        step_parse(b, &mut subterms, &mut payload);
    }
    subterms == 0 && payload == 0
}

#[inline]
fn has_bit(mask: &ByteMask, b: u8) -> bool {
    (mask.0[(b >> 6) as usize] >> (b & 63)) & 1 == 1
}

/// A cursor over the complete variable-width subterms branching from a PathMap zipper's focus, in
/// ascending lexicographic order, with a leapfrog `seek`. This is the zipper-native replacement for
/// a materialized per-variable domain: it seeks on the live byte-trie instead of scanning a `Vec`.
///
/// `key` holds the bytes of the current subterm relative to the focus the cursor was built at
/// (its "floor"). The cursor descends with `descend_to_byte` and ascends with `ascend_byte`, never
/// above the floor (it stops when `key` is empty), so the zipper is left at the floor between
/// re-seeks and at the subterm boundary while positioned.
pub struct SubtermCursor<Z> {
    z: Z,
    key: Vec<u8>,
    at_end: bool,
}

impl<Z: Zipper + ZipperMoving> SubtermCursor<Z> {
    /// Build a cursor at the zipper's current focus. Not positioned until `first`/`seek` is called.
    pub fn new(z: Z) -> Self {
        SubtermCursor { z, key: Vec::new(), at_end: true }
    }

    /// Ascend back to the floor (column start), clearing the key.
    fn reset_to_floor(&mut self) {
        while self.key.pop().is_some() {
            self.z.ascend_byte();
        }
        self.at_end = false;
    }

    /// Descend the least child at each step until the key forms a complete subterm. Returns false
    /// if a node runs out of children before completion (malformed/empty branch).
    fn complete_leftmost(&mut self) -> bool {
        while !is_complete(&self.key) {
            let mask = self.z.child_mask();
            match least_ge(&mask, 0) {
                Some(b) => {
                    self.z.descend_to_byte(b);
                    self.key.push(b);
                }
                None => return false,
            }
        }
        true
    }

    /// From the current complete subterm, move to the least subterm strictly greater: ascend until a
    /// level offers a larger sibling, take the least such, then complete leftmost. False = exhausted.
    fn backtrack_then_leftmost(&mut self) -> bool {
        loop {
            let Some(last) = self.key.pop() else {
                return false;
            };
            self.z.ascend_byte();
            let mask = self.z.child_mask();
            if let Some(b) = mask.next_bit(last) {
                self.z.descend_to_byte(b);
                self.key.push(b);
                return self.complete_leftmost();
            }
        }
    }

    /// Position at the least subterm.
    pub fn first(&mut self) {
        self.reset_to_floor();
        if !self.complete_leftmost() {
            self.at_end = true;
        }
    }

    /// Advance to the next subterm.
    pub fn next(&mut self) {
        if self.at_end {
            return;
        }
        if !self.backtrack_then_leftmost() {
            self.at_end = true;
        }
    }

    /// The current subterm bytes, or `None` when exhausted.
    pub fn key(&self) -> Option<&[u8]> {
        if self.at_end {
            None
        } else {
            Some(&self.key)
        }
    }

    pub fn at_end(&self) -> bool {
        self.at_end
    }

    /// Position at the least subterm `>= target`. `target` must itself be a complete subterm (the
    /// leapfrog only ever seeks to another factor's bound subterm value). Because the encoding is
    /// prefix-free and `target` is complete, a completed descent matches `target` exactly; any
    /// divergence is handled by taking the least larger child (then completing leftmost) or, when no
    /// larger child exists at that level, backtracking to an ancestor that offers one.
    pub fn seek(&mut self, target: &[u8]) {
        self.reset_to_floor();
        let mut ti = 0usize;
        loop {
            if is_complete(&self.key) {
                self.at_end = false;
                return;
            }
            let mask = self.z.child_mask();
            if ti < target.len() {
                let t = target[ti];
                if has_bit(&mask, t) {
                    self.z.descend_to_byte(t);
                    self.key.push(t);
                    ti += 1;
                    continue;
                }
                match mask.next_bit(t) {
                    Some(b) => {
                        self.z.descend_to_byte(b);
                        self.key.push(b);
                        if !self.complete_leftmost() {
                            self.at_end = true;
                        }
                        return;
                    }
                    None => {
                        if !self.backtrack_then_leftmost() {
                            self.at_end = true;
                        }
                        return;
                    }
                }
            } else {
                if !self.complete_leftmost() {
                    self.at_end = true;
                }
                return;
            }
        }
    }
}

/// Leapfrog intersection of several subterm cursors: the subterm values present in ALL of them, in
/// ascending order. The textbook leapfrog step seeks every cursor to the current maximum key; when
/// they all agree, that key is in the intersection, then one cursor steps past it. Each step either
/// emits a match and advances, or jumps a cursor forward, so it terminates and is worst-case-optimal
/// on the cursors' sizes.
fn intersect<Z: Zipper + ZipperMoving>(cursors: &mut [SubtermCursor<Z>]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    if cursors.is_empty() {
        return out;
    }
    for c in cursors.iter_mut() {
        c.first();
        if c.at_end() {
            return out;
        }
    }
    loop {
        let max = cursors.iter().map(|c| c.key().unwrap()).max().unwrap().to_vec();
        let mut all_match = true;
        for c in cursors.iter_mut() {
            if c.key().unwrap() != max.as_slice() {
                c.seek(&max);
                if c.at_end() {
                    return out;
                }
                if c.key().unwrap() != max.as_slice() {
                    all_match = false;
                }
            }
        }
        if all_match {
            out.push(max);
            cursors[0].next();
            if cursors[0].at_end() {
                return out;
            }
        }
    }
}

/// A query factor: its relation prefix in the PathMap, and the global variable index bound at each
/// of its argument columns, in syntactic column order.
#[derive(Clone, Debug)]
pub struct Factor {
    pub prefix: Vec<u8>,
    pub cols: Vec<usize>,
}

/// Ground worst-case-optimal join over PathMap factors, seeking variable-width subterms directly on
/// the byte-trie with no materialized domain. `var_order` lists the global variables in binding
/// order; it must be compatible with every factor's column order (each factor's variables, in
/// `var_order`, occur in column order), which holds for any acyclic query under a suitable order.
/// Cyclic queries that admit no compatible order are handled by re-indexing in a later layer.
///
/// Returns one row per answer: `row[v]` is the bound subterm bytes for global variable `v`.
pub fn ground_join(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> Vec<Vec<Vec<u8>>> {
    let mut state = GroundJoin {
        map,
        factors,
        var_order,
        bound: vec![Vec::new(); factors.len()],
        next_col: vec![0; factors.len()],
        binding: vec![Vec::new(); nvars],
        out: Vec::new(),
    };
    state.recurse(0);
    state.out
}

struct GroundJoin<'a> {
    map: &'a PathMap<()>,
    factors: &'a [Factor],
    var_order: &'a [usize],
    bound: Vec<Vec<u8>>,
    next_col: Vec<usize>,
    binding: Vec<Vec<u8>>,
    out: Vec<Vec<Vec<u8>>>,
}

impl GroundJoin<'_> {
    fn recurse(&mut self, i: usize) {
        if i == self.var_order.len() {
            self.out.push(self.binding.clone());
            return;
        }
        let v = self.var_order[i];
        let parts: Vec<usize> = (0..self.factors.len())
            .filter(|&f| {
                let nc = self.next_col[f];
                nc < self.factors[f].cols.len() && self.factors[f].cols[nc] == v
            })
            .collect();

        // Open one cursor per participating factor at its current position (relation prefix plus the
        // bytes of its already-bound columns), then leapfrog-intersect their next-column subterms.
        let mut cursors: Vec<_> = parts
            .iter()
            .map(|&f| {
                let mut path = self.factors[f].prefix.clone();
                path.extend_from_slice(&self.bound[f]);
                SubtermCursor::new(self.map.read_zipper_at_path(&path))
            })
            .collect();
        let vals = intersect(&mut cursors);
        drop(cursors);

        for val in vals {
            for &f in &parts {
                self.bound[f].extend_from_slice(&val);
                self.next_col[f] += 1;
            }
            self.binding[v] = val.clone();

            // Catch-up validation. A factor whose next column is a variable already bound (because
            // the query orders that variable before this one, the cyclic/coreferent case) must agree
            // with the existing binding: seek it in the factor's trie and prune the branch if absent.
            // Only factors that just advanced can have a freshly-already-bound next column.
            let mut catchup: Vec<(usize, usize)> = Vec::new();
            let mut pruned = false;
            'factors: for &f in &parts {
                loop {
                    let nc = self.next_col[f];
                    if nc >= self.factors[f].cols.len() {
                        break;
                    }
                    let cv = self.factors[f].cols[nc];
                    if self.binding[cv].is_empty() {
                        break;
                    }
                    let target = self.binding[cv].clone();
                    let mut path = self.factors[f].prefix.clone();
                    path.extend_from_slice(&self.bound[f]);
                    let mut cur = SubtermCursor::new(self.map.read_zipper_at_path(&path));
                    cur.seek(&target);
                    if cur.key() == Some(target.as_slice()) {
                        self.bound[f].extend_from_slice(&target);
                        self.next_col[f] += 1;
                        catchup.push((f, target.len()));
                    } else {
                        pruned = true;
                        break 'factors;
                    }
                }
            }

            if !pruned {
                self.recurse(i + 1);
            }

            for (f, added) in catchup.into_iter().rev() {
                let len = self.bound[f].len() - added;
                self.bound[f].truncate(len);
                self.next_col[f] -= 1;
            }
            self.binding[v].clear();
            for &f in &parts {
                let len = self.bound[f].len() - val.len();
                self.bound[f].truncate(len);
                self.next_col[f] -= 1;
            }
        }
    }
}

// ---- unification layer: schematic data (stored variables in facts act as wildcards) ----
//
// In the routed scope the gate excludes non-ground compounds, so every term is either a ground
// byte-slice or a variable. Unification therefore degenerates to union-find over variables with
// ground byte-slice values, with no structural recursion. This `Env` is that trail union-find.

/// A variable's binding: a ground value (its bytes) or an alias to another variable.
#[derive(Clone)]
enum Bind {
    Ground(Vec<u8>),
    Alias(usize),
}

/// What a variable resolves to: still a free variable (its representative id) or a ground value.
enum Resolved {
    Var(usize),
    Ground(Vec<u8>),
}

/// Trail-based union-find unifier. Query variables hold ids `0..nvars`; stored data variables get
/// fresh ids past that, allocated per fact-descent so they are renamed apart across facts. `mark`
/// and `rollback` give O(1)-per-binding backtracking for the leapfrog.
struct Env {
    slots: Vec<Option<Bind>>,
    trail: Vec<usize>,
}

impl Env {
    fn new(nvars: usize) -> Env {
        Env { slots: vec![None; nvars], trail: Vec::new() }
    }

    /// Allocate a fresh (unbound) variable id, for a stored data variable.
    fn fresh(&mut self) -> usize {
        self.slots.push(None);
        self.slots.len() - 1
    }

    fn mark(&self) -> usize {
        self.trail.len()
    }

    fn rollback(&mut self, m: usize) {
        while self.trail.len() > m {
            let id = self.trail.pop().unwrap();
            self.slots[id] = None;
        }
    }

    fn resolve(&self, mut id: usize) -> Resolved {
        loop {
            match &self.slots[id] {
                None => return Resolved::Var(id),
                Some(Bind::Alias(j)) => id = *j,
                Some(Bind::Ground(g)) => return Resolved::Ground(g.clone()),
            }
        }
    }

    fn bind_ground(&mut self, id: usize, g: Vec<u8>) {
        self.slots[id] = Some(Bind::Ground(g));
        self.trail.push(id);
    }

    fn bind_alias(&mut self, id: usize, j: usize) {
        self.slots[id] = Some(Bind::Alias(j));
        self.trail.push(id);
    }

    /// Unify variable `id` with a ground value `g`. False on a ground/ground clash.
    fn unify_var_ground(&mut self, id: usize, g: &[u8]) -> bool {
        match self.resolve(id) {
            Resolved::Var(r) => {
                self.bind_ground(r, g.to_vec());
                true
            }
            Resolved::Ground(existing) => existing == g,
        }
    }

    /// Unify two variables. False on a ground/ground clash.
    fn unify_var_var(&mut self, a: usize, b: usize) -> bool {
        match (self.resolve(a), self.resolve(b)) {
            (Resolved::Var(ra), Resolved::Var(rb)) => {
                if ra != rb {
                    self.bind_alias(ra, rb);
                }
                true
            }
            (Resolved::Var(ra), Resolved::Ground(g)) => {
                self.bind_ground(ra, g);
                true
            }
            (Resolved::Ground(g), Resolved::Var(rb)) => {
                self.bind_ground(rb, g);
                true
            }
            (Resolved::Ground(ga), Resolved::Ground(gb)) => ga == gb,
        }
    }

    /// The ground value a query variable resolved to, or `None` if it is still free (a non-ground
    /// answer component, which the live route renders fresh and drops).
    fn ground_of(&self, id: usize) -> Option<Vec<u8>> {
        match self.resolve(id) {
            Resolved::Ground(g) => Some(g),
            Resolved::Var(_) => None,
        }
    }
}

/// A candidate child at a factor's column: a ground subterm value, or a stored-variable wildcard
/// (its one tag byte: NewVar `0xC0` or VarRef `0x80|i`).
enum Cand {
    Ground(Vec<u8>),
    Wild(u8),
}

#[inline]
fn is_wildcard_byte(k: &[u8]) -> bool {
    k.len() == 1 && (0x80..=0xC0).contains(&k[0])
}

/// The children of a factor's current column that can unify with the join variable's binding `vb`.
/// If `vb` is a ground value, seek that value (the worst-case-optimal step) and add the wildcard
/// children, which all unify with it; the wildcards live in the isolated `[0x80,0xC0]` byte range,
/// so they are a short scan, not a full enumeration. If `vb` is still free this is the lead, which
/// enumerates the whole column (ground children and wildcards alike).
fn candidates<Z: Zipper + ZipperMoving>(cur: &mut SubtermCursor<Z>, vb: &Resolved) -> Vec<Cand> {
    let mut out = Vec::new();
    match vb {
        Resolved::Ground(g) => {
            cur.seek(g);
            if cur.key() == Some(g.as_slice()) {
                out.push(Cand::Ground(g.clone()));
            }
            cur.seek(&[0x80]);
            while let Some(k) = cur.key() {
                if is_wildcard_byte(k) {
                    out.push(Cand::Wild(k[0]));
                    cur.next();
                } else {
                    break;
                }
            }
        }
        Resolved::Var(_) => {
            cur.first();
            while let Some(k) = cur.key() {
                if is_wildcard_byte(k) {
                    out.push(Cand::Wild(k[0]));
                } else {
                    out.push(Cand::Ground(k.to_vec()));
                }
                cur.next();
            }
        }
    }
    out
}

/// A factor is inverted when its columns are not in `var_order` order, so the join cannot seek it
/// forward (a later column's variable is bound before an earlier one). The triangle's third factor
/// `(e $z $x)` under order `$x,$y,$z` is the case: its `$x` column comes second but binds first.
fn is_inverted(factor: &Factor, var_pos: &[usize]) -> bool {
    factor.cols.windows(2).any(|w| var_pos[w[0]] > var_pos[w[1]])
}

/// One position in a re-emitted subterm: a literal byte, or a variable identified by its original
/// id (so the re-index can renumber it canonically in the new column order).
enum Item {
    Byte(u8),
    Var(usize),
}

/// Split a fact's column bytes (everything after the relation prefix) into its `ncols` subterms.
fn split_columns(bytes: &[u8], ncols: usize) -> Vec<&[u8]> {
    let mut cols = Vec::with_capacity(ncols);
    let mut i = 0;
    for _ in 0..ncols {
        let len = first_subterm_len(&bytes[i..]);
        cols.push(&bytes[i..i + len]);
        i += len;
    }
    cols
}

/// Decode each column into items, tagging every variable with its original id. NewVar takes the next
/// id in encounter order across the whole fact; VarRef(i) refers to id `i`. This is what lets the
/// re-index renumber a coreferent schematic fact, say `(e $u $u)`, correctly after its columns move.
fn columns_to_items(cols: &[&[u8]]) -> Vec<Vec<Item>> {
    let mut next_orig = 0usize;
    let mut out = Vec::with_capacity(cols.len());
    for col in cols {
        let mut items = Vec::new();
        let mut i = 0;
        while i < col.len() {
            let b = col[i];
            i += 1;
            match b & TOP2 {
                TAG_ARITY => items.push(Item::Byte(b)),
                TAG_VARREF => items.push(Item::Var((b & LOW6) as usize)),
                _ => {
                    if b == NEWVAR_BYTE {
                        items.push(Item::Var(next_orig));
                        next_orig += 1;
                    } else {
                        items.push(Item::Byte(b));
                        for _ in 0..(b & LOW6) as usize {
                            items.push(Item::Byte(col[i]));
                            i += 1;
                        }
                    }
                }
            }
        }
        out.push(items);
    }
    out
}

/// Re-emit the columns in `new_order`, renumbering variables so the first reference to each original
/// id (in the new order) is a NewVar and later references are a VarRef of its new index. Produces a
/// canonical, self-consistent encoding for the re-indexed key.
fn emit_reordered(items_by_col: &[Vec<Item>], new_order: &[usize]) -> Vec<u8> {
    use std::collections::HashMap;
    let mut out = Vec::new();
    let mut renum: HashMap<usize, usize> = HashMap::new();
    for &c in new_order {
        for item in &items_by_col[c] {
            match item {
                Item::Byte(b) => out.push(*b),
                Item::Var(orig) => match renum.get(orig) {
                    Some(&new_id) => out.push(TAG_VARREF | new_id as u8),
                    None => {
                        renum.insert(*orig, renum.len());
                        out.push(NEWVAR_BYTE);
                    }
                },
            }
        }
    }
    out
}

/// Re-index an inverted factor: copy its facts into a fresh PathMap with the columns permuted into
/// `var_order` position order (variables renumbered to stay canonical). Returns that map and the new
/// column-variable list, now non-decreasing, so the join seeks it like any compatible factor. This
/// is the one partial materialization the cyclic case needs, and only the inverted factor pays it;
/// re-keying into another attribute order is the standard worst-case-optimal answer to a cycle.
fn build_reindex(map: &PathMap<()>, factor: &Factor, var_pos: &[usize]) -> (PathMap<()>, Vec<usize>) {
    let ncols = factor.cols.len();
    let mut new_order: Vec<usize> = (0..ncols).collect();
    new_order.sort_by_key(|&c| var_pos[factor.cols[c]]);
    let new_cols: Vec<usize> = new_order.iter().map(|&c| factor.cols[c]).collect();

    let mut reindex = PathMap::<()>::new();
    let plen = factor.prefix.len();
    let mut rz = map.read_zipper_at_path(&factor.prefix);
    while rz.to_next_val() {
        let full = rz.origin_path();
        let cols = split_columns(&full[plen..], ncols);
        let items = columns_to_items(&cols);
        reindex.insert(&emit_reordered(&items, &new_order), ());
    }
    (reindex, new_cols)
}

/// Worst-case-optimal leapfrog-UNIFICATION join directly on the PathMap byte-trie, returning the
/// fully-ground answer rows (`row[v]` = global variable `v`'s value). A row with any still-free query
/// variable is dropped here; the live route uses [`unify_join_zipper_partial`] instead, to keep it
/// and bind only its ground components, exactly as the materialized route does.
pub fn unify_join_zipper(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> BTreeSet<Vec<Vec<u8>>> {
    unify_join_zipper_partial(map, factors, var_order, nvars)
        .into_iter()
        .filter_map(|row| row.into_iter().collect::<Option<Vec<Vec<u8>>>>())
        .collect()
}

/// As [`unify_join_zipper`], but each answer component is `Some(bytes)` when the query variable bound
/// a ground value and `None` when it stayed free (bound only to stored wildcards). Generalizes
/// [`ground_join`]: a stored variable in the data is a wildcard that unifies with the join variable
/// through the trail. Inverted factors (a cyclic query has one) are re-indexed up front so the join
/// can seek them; every other factor stays zero-copy on the live map.
pub fn unify_join_zipper_partial(
    map: &PathMap<()>,
    factors: &[Factor],
    var_order: &[usize],
    nvars: usize,
) -> BTreeSet<Vec<Option<Vec<u8>>>> {
    let nf = factors.len();
    let mut var_pos = vec![0usize; nvars];
    for (pos, &v) in var_order.iter().enumerate() {
        var_pos[v] = pos;
    }

    // Re-index inverted factors so the join can seek them in var_order; a compatible factor keeps its
    // live-map prefix and pays nothing. `factor_src[f]` selects which map factor `f` reads from.
    let mut owned: Vec<Factor> = Vec::with_capacity(nf);
    let mut reindexes: Vec<PathMap<()>> = Vec::new();
    let mut factor_src: Vec<Option<usize>> = Vec::with_capacity(nf);
    for factor in factors {
        if is_inverted(factor, &var_pos) {
            let (ri, new_cols) = build_reindex(map, factor, &var_pos);
            factor_src.push(Some(reindexes.len()));
            reindexes.push(ri);
            owned.push(Factor { prefix: Vec::new(), cols: new_cols });
        } else {
            factor_src.push(None);
            owned.push(factor.clone());
        }
    }

    let mut state = UnifyJoin {
        map,
        reindexes,
        factor_src,
        factors: owned,
        var_order,
        var_pos,
        nvars,
        bound: vec![Vec::new(); nf],
        next_col: vec![0; nf],
        stored_slots: vec![Vec::new(); nf],
        env: Env::new(nvars),
        out: BTreeSet::new(),
    };
    state.recurse(0);
    state.out
}

/// Parse an encoded conjunction body `(, p1 .. pk)` into factors, threading the body's variable
/// numbering (a NewVar takes the next id in first-occurrence order, a VarRef back-references one).
/// Returns the factors and the variable count, or None if a pattern carries a column the factor
/// model does not (a non-leading constant or a compound argument), so the caller can fall back to the
/// materialized join. Leading ground arguments fold into the relation prefix.
pub fn parse_body_factors(body: &[u8]) -> Option<(Vec<Factor>, usize)> {
    if body.is_empty() || body[0] & TOP2 != TAG_ARITY {
        return None;
    }
    let nconj = (body[0] & LOW6) as usize;
    if nconj == 0 {
        return None;
    }
    let mut i = 1;
    i += first_subterm_len(&body[i..]); // skip the `,` conjunction head
    let mut factors = Vec::with_capacity(nconj - 1);
    let mut nvars = 0usize;
    for _ in 0..nconj - 1 {
        let plen = first_subterm_len(&body[i..]);
        factors.push(parse_pattern_factor(&body[i..i + plen], &mut nvars)?);
        i += plen;
    }
    Some((factors, nvars))
}

/// One conjunct `(rel arg..)` to a factor. The relation symbol and any leading ground arguments are
/// the prefix; each remaining argument must be a single variable column.
fn parse_pattern_factor(pat: &[u8], nvars: &mut usize) -> Option<Factor> {
    if pat[0] & TOP2 != TAG_ARITY {
        return None;
    }
    let mut args_left = (pat[0] & LOW6) as usize - 1;
    let mut j = 1 + first_subterm_len(&pat[1..]); // past the arity byte and the head symbol
    while args_left > 0 && first_subterm_is_ground(&pat[j..]) {
        j += first_subterm_len(&pat[j..]);
        args_left -= 1;
    }
    let prefix = pat[0..j].to_vec();
    let mut cols = Vec::with_capacity(args_left);
    while args_left > 0 {
        let b = pat[j];
        if first_subterm_len(&pat[j..]) != 1 || !(0x80..=0xC0).contains(&b) {
            return None; // a non-leading constant or a compound column: outside the factor model
        }
        cols.push(if b == NEWVAR_BYTE {
            let id = *nvars;
            *nvars += 1;
            id
        } else {
            (b & LOW6) as usize
        });
        j += 1;
        args_left -= 1;
    }
    Some(Factor { prefix, cols })
}

/// Live-route entry: parse the conjunction body into factors and run the join on the live map.
/// Variables bind in first-occurrence order, the order the emit numbers the answer components in.
/// None if a pattern is outside the factor model, so the caller falls back to the materialized join.
pub fn unify_join_zipper_body(map: &PathMap<()>, body: &[u8]) -> Option<BTreeSet<Vec<Vec<u8>>>> {
    let (factors, nvars) = parse_body_factors(body)?;
    let var_order: Vec<usize> = (0..nvars).collect();
    Some(unify_join_zipper(map, &factors, &var_order, nvars))
}

struct UnifyJoin<'a> {
    map: &'a PathMap<()>,
    /// Re-indexed copies of inverted factors; `factor_src[f] = Some(i)` reads `reindexes[i]`.
    reindexes: Vec<PathMap<()>>,
    factor_src: Vec<Option<usize>>,
    /// Owned because a re-indexed factor's prefix and columns differ from the input factor's.
    factors: Vec<Factor>,
    var_order: &'a [usize],
    /// `var_pos[v]` = position of global variable `v` in `var_order`, for the catch-up test.
    var_pos: Vec<usize>,
    nvars: usize,
    bound: Vec<Vec<u8>>,
    next_col: Vec<usize>,
    stored_slots: Vec<Vec<usize>>,
    env: Env,
    /// Answer rows, one `Option` per query variable: `Some(bytes)` ground, `None` non-ground. The
    /// all-ground entry filters to fully-ground rows; the live emit binds the ground components.
    out: BTreeSet<Vec<Option<Vec<u8>>>>,
}

impl UnifyJoin<'_> {
    fn recurse(&mut self, i: usize) {
        if i == self.var_order.len() {
            // Keep every component, ground or not. A non-ground component (a query variable bound
            // only to stored wildcards) is None; the live emit binds only the ground ones, exactly
            // as the materialized route does, and the all-ground entry point filters the rest out.
            let row: Vec<Option<Vec<u8>>> =
                (0..self.nvars).map(|v| self.env.ground_of(v)).collect();
            self.out.insert(row);
            return;
        }
        let v = self.var_order[i];
        let mut parts: Vec<usize> = (0..self.factors.len())
            .filter(|&f| {
                let nc = self.next_col[f];
                nc < self.factors[f].cols.len() && self.factors[f].cols[nc] == v
            })
            .collect();
        if parts.is_empty() {
            self.recurse(i + 1);
            return;
        }
        // The leapfrog principle: lead with the smallest domain so the leading factor enumerates
        // few candidates and the rest seek. A bounded subterm count under each factor's current
        // position is the estimate. This is what makes a selective factor, say (e a $y) with a few
        // edges, drive the join instead of the whole relation.
        parts.sort_by_key(|&f| self.domain_estimate(f));
        self.intersect_unify(&parts, 0, v, i);
    }

    /// Domain-size estimate for lead selection, bounded so it is independent of the space size.
    /// Count the distinct subterm values under the factor's current position, but stop at a small
    /// cap. The leapfrog only needs to know which factor has the fewest candidates, not the exact
    /// count, so a bounded count suffices and stays O(cap). A full `val_count` is O(subtree), which
    /// would make a selective join's cost climb with the whole relation rather than the answer.
    /// The map factor `f` reads from: its re-indexed copy if it was inverted, else the live map.
    fn src_map(&self, f: usize) -> &PathMap<()> {
        match self.factor_src[f] {
            Some(ri) => &self.reindexes[ri],
            None => self.map,
        }
    }

    fn domain_estimate(&self, f: usize) -> usize {
        const CAP: usize = 32;
        let mut path = self.factors[f].prefix.clone();
        path.extend_from_slice(&self.bound[f]);
        let mut cur = SubtermCursor::new(self.src_map(f).read_zipper_at_path(&path));
        cur.first();
        let mut n = 0;
        while !cur.at_end() && n < CAP {
            n += 1;
            cur.next();
        }
        n
    }

    /// The candidates at factor `f`'s current column that can unify with query variable `qvar`.
    fn open_candidates(&self, f: usize, qvar: usize) -> Vec<Cand> {
        let mut path = self.factors[f].prefix.clone();
        path.extend_from_slice(&self.bound[f]);
        let mut cur = SubtermCursor::new(self.src_map(f).read_zipper_at_path(&path));
        let vb = self.env.resolve(qvar);
        candidates(&mut cur, &vb)
    }

    /// Unify `qvar` with a candidate child of factor `f`, returning whether it held and the trie
    /// bytes to descend. A NewVar wildcard allocates a fresh stored variable (pushed to `f`'s slots
    /// so a later VarRef in the same fact corefers); a VarRef reads the slot it introduced.
    fn apply_cand(&mut self, qvar: usize, cand: &Cand, f: usize) -> (bool, Vec<u8>) {
        match cand {
            Cand::Ground(g) => (self.env.unify_var_ground(qvar, g), g.clone()),
            Cand::Wild(w) => {
                let id = if *w == 0xC0 {
                    let id = self.env.fresh();
                    self.stored_slots[f].push(id);
                    id
                } else {
                    self.stored_slots[f][(*w & 0x3F) as usize]
                };
                (self.env.unify_var_var(qvar, id), vec![*w])
            }
        }
    }

    fn intersect_unify(&mut self, parts: &[usize], pi: usize, v: usize, i: usize) {
        if pi == parts.len() {
            self.catch_up(parts, 0, i);
            return;
        }
        let f = parts[pi];
        let cands = self.open_candidates(f, v);
        for cand in cands {
            let mark = self.env.mark();
            let slots_len = self.stored_slots[f].len();
            let (ok, bytes) = self.apply_cand(v, &cand, f);
            if ok {
                self.bound[f].extend_from_slice(&bytes);
                self.next_col[f] += 1;
                self.intersect_unify(parts, pi + 1, v, i);
                let l = self.bound[f].len() - bytes.len();
                self.bound[f].truncate(l);
                self.next_col[f] -= 1;
            }
            self.stored_slots[f].truncate(slots_len);
            self.env.rollback(mark);
        }
    }

    /// After binding variable `var_order[i]`, advance each factor that just participated past any
    /// further column that names an already-bound variable (the cyclic/coreferent case), unifying
    /// it. Under unification this can branch (a wildcard child unifies as well as the ground value),
    /// so it is a recursion, not a plain validate. For acyclic queries every next column is a future
    /// variable, so this is a no-op and the join stays the pure forward leapfrog.
    fn catch_up(&mut self, parts: &[usize], pj: usize, i: usize) {
        if pj == parts.len() {
            self.recurse(i + 1);
            return;
        }
        let f = parts[pj];
        let nc = self.next_col[f];
        let already =
            nc < self.factors[f].cols.len() && self.var_pos[self.factors[f].cols[nc]] <= i;
        if !already {
            self.catch_up(parts, pj + 1, i);
            return;
        }
        let vp = self.factors[f].cols[nc];
        let cands = self.open_candidates(f, vp);
        for cand in cands {
            let mark = self.env.mark();
            let slots_len = self.stored_slots[f].len();
            let (ok, bytes) = self.apply_cand(vp, &cand, f);
            if ok {
                self.bound[f].extend_from_slice(&bytes);
                self.next_col[f] += 1;
                self.catch_up(parts, pj, i);
                let l = self.bound[f].len() - bytes.len();
                self.bound[f].truncate(l);
                self.next_col[f] -= 1;
            }
            self.stored_slots[f].truncate(slots_len);
            self.env.rollback(mark);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mask_of(bytes: &[u8]) -> ByteMask {
        let mut m = [0u64; 4];
        for &b in bytes {
            m[(b >> 6) as usize] |= 1u64 << (b & 63);
        }
        ByteMask(m)
    }

    fn sym(s: &str) -> Vec<u8> {
        let mut v = vec![TAG_SYMSIZE | s.len() as u8];
        v.extend_from_slice(s.as_bytes());
        v
    }

    /// `(rel a0 a1 ...)` encoded: Arity(1+n), Sym(rel), then each arg's bytes.
    fn nest(rel: &str, args: &[Vec<u8>]) -> Vec<u8> {
        let mut v = vec![TAG_ARITY | (1 + args.len()) as u8];
        v.extend(sym(rel));
        for a in args {
            v.extend_from_slice(a);
        }
        v
    }

    /// The stored-path prefix for a relation of the given total arity (head + args).
    fn relation_prefix(rel: &str, total_arity: usize) -> Vec<u8> {
        let mut v = vec![TAG_ARITY | total_arity as u8];
        v.extend(sym(rel));
        v
    }

    #[test]
    fn subterm_cursor_enumerates_and_seeks_arg1() {
        // First arguments of various shapes: a compound (sorts first, tag 0x02 < symbol tag 0xC1),
        // several one-byte-length symbols, and a two-byte-length one (sorts last, 0xC2 > 0xC1).
        let a_terms: Vec<Vec<u8>> = vec![
            sym("a"),
            sym("b"),
            sym("c"),
            sym("z"),
            sym("bb"),
            nest("k", &[sym("v")]),
        ];
        // Each arg1 appears in two facts (distinct arg2) to exercise trie merging / distinctness.
        let mut facts = Vec::new();
        for (i, a) in a_terms.iter().enumerate() {
            facts.push(nest("e", &[a.clone(), sym(&format!("p{i}"))]));
            facts.push(nest("e", &[a.clone(), sym(&format!("q{i}"))]));
        }
        // A different relation under the same map, to confirm the prefix scopes the cursor.
        facts.push(nest("h", &[sym("a"), sym("a")]));

        let mut map = PathMap::<()>::new();
        for f in &facts {
            map.insert(f, ());
        }
        let pfx = relation_prefix("e", 3);

        // Oracle: distinct arg1 subterms in byte-lex order.
        let mut want: Vec<Vec<u8>> = a_terms.clone();
        want.sort();
        want.dedup();

        let mut cur = SubtermCursor::new(map.read_zipper_at_path(&pfx));
        cur.first();
        let mut got = Vec::new();
        while let Some(k) = cur.key() {
            got.push(k.to_vec());
            cur.next();
        }
        assert_eq!(got, want, "enumeration must be the distinct arg1 subterms in lex order");

        // seek to each oracle value and to a few off-key targets; compare to least >= target.
        let mut targets = want.clone();
        targets.push(nest("k", &[sym("a")])); // a compound just below (k v)
        targets.push(sym("ba")); // between b and bb in byte order? [0xC2,'b','a'] vs [0xC2,'b','b']
        for target in &targets {
            cur.seek(target);
            let expect = want.iter().find(|w| w.as_slice() >= target.as_slice()).cloned();
            assert_eq!(
                cur.key().map(<[u8]>::to_vec),
                expect,
                "seek({target:?}) must land on the least subterm >= target"
            );
        }

        // seek past every subterm -> exhausted.
        cur.seek(&sym("zz"));
        assert!(cur.at_end(), "seek past the maximum must exhaust the cursor");
    }

    struct Lcg(u64);
    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg(seed
                .wrapping_mul(2862933555777941757)
                .wrapping_add(3037000493))
        }
        fn next_u64(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next_u64() % n as u64) as usize
        }
    }

    /// A random variable-width term over a two-byte symbol alphabet, so symbols share prefixes and
    /// force multi-level backtracking in seek; with nested compounds when depth allows.
    fn rand_term(rng: &mut Lcg, depth: usize) -> Vec<u8> {
        const ALPHA: &[u8] = b"ab";
        if depth == 0 || rng.below(3) != 0 {
            let len = 1 + rng.below(3);
            let mut v = vec![TAG_SYMSIZE | len as u8];
            for _ in 0..len {
                v.push(ALPHA[rng.below(ALPHA.len())]);
            }
            v
        } else {
            let n = 1 + rng.below(2);
            let mut v = vec![TAG_ARITY | (1 + n) as u8];
            v.extend(sym("f"));
            for _ in 0..n {
                v.extend(rand_term(rng, depth - 1));
            }
            v
        }
    }

    #[test]
    fn subterm_cursor_property_vs_brute_force() {
        for seed in 0..300u64 {
            let mut rng = Lcg::new(seed.wrapping_add(1));
            let n = 1 + rng.below(12);
            let a_terms: Vec<Vec<u8>> = (0..n).map(|_| rand_term(&mut rng, 2)).collect();

            let mut map = PathMap::<()>::new();
            for (i, a) in a_terms.iter().enumerate() {
                map.insert(&nest("e", &[a.clone(), sym(&format!("z{}", i % 3))]), ());
            }
            let pfx = relation_prefix("e", 3);

            let mut want: Vec<Vec<u8>> = a_terms.clone();
            want.sort();
            want.dedup();

            let mut cur = SubtermCursor::new(map.read_zipper_at_path(&pfx));
            cur.first();
            let mut got = Vec::new();
            while let Some(k) = cur.key() {
                got.push(k.to_vec());
                cur.next();
            }
            assert_eq!(got, want, "seed {seed}: enumeration");

            let mut targets = want.clone();
            for _ in 0..12 {
                targets.push(rand_term(&mut rng, 2));
            }
            for target in &targets {
                cur.seek(target);
                let expect = want.iter().find(|w| w.as_slice() >= target.as_slice()).cloned();
                assert_eq!(
                    cur.key().map(<[u8]>::to_vec),
                    expect,
                    "seed {seed}: seek({target:?})"
                );
            }
        }
    }

    /// Reference join: nested loop over one matching fact per factor, binding shared variables and
    /// rejecting on conflict. `factor_rows[f]` is the column-subterm list of factor f's facts.
    fn brute_rec(
        f: usize,
        factors: &[Factor],
        factor_rows: &[Vec<Vec<Vec<u8>>>],
        binding: &mut Vec<Option<Vec<u8>>>,
        out: &mut Vec<Vec<Vec<u8>>>,
    ) {
        if f == factors.len() {
            out.push(binding.iter().map(|b| b.clone().unwrap()).collect());
            return;
        }
        for row in &factor_rows[f] {
            let mut undo: Vec<usize> = Vec::new();
            let mut ok = true;
            for (ci, &v) in factors[f].cols.iter().enumerate() {
                if let Some(existing) = &binding[v] {
                    if existing != &row[ci] {
                        ok = false;
                        break;
                    }
                } else {
                    binding[v] = Some(row[ci].clone());
                    undo.push(v);
                }
            }
            if ok {
                brute_rec(f + 1, factors, factor_rows, binding, out);
            }
            for v in undo.into_iter().rev() {
                binding[v] = None;
            }
        }
    }

    #[test]
    fn ground_join_matches_brute_force() {
        for seed in 0..150u64 {
            let mut rng = Lcg::new(seed.wrapping_add(7));
            let nnodes = 3 + rng.below(4);
            let nodes: Vec<Vec<u8>> = (0..nnodes)
                .map(|i| sym(&((b'a' + i as u8) as char).to_string()))
                .collect();

            let mut map = PathMap::<()>::new();
            let mut e_facts: Vec<Vec<Vec<u8>>> = Vec::new();
            let mut f_facts: Vec<Vec<Vec<u8>>> = Vec::new();
            let nedges = 4 + rng.below(8);
            for _ in 0..nedges {
                let a = nodes[rng.below(nnodes)].clone();
                let b = nodes[rng.below(nnodes)].clone();
                if map.insert(&nest("e", &[a.clone(), b.clone()]), ()).is_none() {
                    e_facts.push(vec![a, b]);
                }
                let c = nodes[rng.below(nnodes)].clone();
                let d = nodes[rng.below(nnodes)].clone();
                if map.insert(&nest("f", &[c.clone(), d.clone()]), ()).is_none() {
                    f_facts.push(vec![c, d]);
                }
            }
            let pe = relation_prefix("e", 3);
            let pf = relation_prefix("f", 3);

            let queries: Vec<(Vec<Factor>, Vec<usize>, usize)> = vec![
                // path  (e $0 $1)(e $1 $2)
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // star  (e $0 $1)(e $0 $2)
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![0, 2] },
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // two-relation path  (e $0 $1)(f $1 $2)
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pf.clone(), cols: vec![1, 2] },
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // three-path  (e $0 $1)(e $1 $2)(e $2 $3)
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                        Factor { prefix: pe.clone(), cols: vec![2, 3] },
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
                // triangle  (e $0 $1)(e $1 $2)(e $2 $0) -- cyclic: factor 2's columns invert the
                // variable order, so it must validate $0 after binding $2 (the catch-up path).
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                        Factor { prefix: pe.clone(), cols: vec![2, 0] },
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // same triangle under a rotated variable order (different participation pattern).
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                        Factor { prefix: pe.clone(), cols: vec![2, 0] },
                    ],
                    vec![1, 2, 0],
                    3,
                ),
                // four-cycle  (e $0 $1)(e $1 $2)(e $2 $3)(e $3 $0)
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                        Factor { prefix: pe.clone(), cols: vec![2, 3] },
                        Factor { prefix: pe.clone(), cols: vec![3, 0] },
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
                // intra-factor coreference  (e $0 $0): only the self-loops, via catch-up on col 1.
                (
                    vec![Factor { prefix: pe.clone(), cols: vec![0, 0] }],
                    vec![0],
                    1,
                ),
                // triangle with a pendant  (e $0 $1)(e $1 $2)(e $2 $0)(f $0 $3)
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                        Factor { prefix: pe.clone(), cols: vec![2, 0] },
                        Factor { prefix: pf.clone(), cols: vec![0, 3] },
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
            ];

            for (factors, order, nvars) in &queries {
                let factor_rows: Vec<Vec<Vec<Vec<u8>>>> = factors
                    .iter()
                    .map(|fac| if fac.prefix == pe { e_facts.clone() } else { f_facts.clone() })
                    .collect();

                let mut got = ground_join(&map, factors, order, *nvars);
                let mut want = {
                    let mut binding = vec![None; *nvars];
                    let mut out = Vec::new();
                    brute_rec(0, factors, &factor_rows, &mut binding, &mut out);
                    out
                };
                got.sort();
                got.dedup();
                want.sort();
                want.dedup();
                assert_eq!(got, want, "seed {seed}: join answers must match the nested loop");
            }
        }
    }

    /// A structured fact column for the schematic differential: a ground value, or a stored variable
    /// identified by a fact-local slot (so the same slot twice in one fact is coreferent).
    #[derive(Clone)]
    enum FCol {
        G(Vec<u8>),
        V(usize),
    }

    /// Encode a fact, assigning MORK's NewVar to a slot's first occurrence and VarRef to repeats,
    /// exactly as the stored encoding represents schematic facts and their coreference.
    fn encode_fact(rel: &str, cols: &[FCol]) -> Vec<u8> {
        let mut v = vec![TAG_ARITY | (1 + cols.len()) as u8];
        v.extend(sym(rel));
        let mut introduced: Vec<usize> = Vec::new();
        for col in cols {
            match col {
                FCol::G(g) => v.extend_from_slice(g),
                FCol::V(slot) => {
                    if let Some(idx) = introduced.iter().position(|s| s == slot) {
                        v.push(TAG_VARREF | idx as u8);
                    } else {
                        introduced.push(*slot);
                        v.push(NEWVAR_BYTE);
                    }
                }
            }
        }
        v
    }

    /// A random binary fact: each column ground (small symbol set) or a stored variable (slot 0/1),
    /// so the corpus mixes ground, single-variable, coreferent, and two-variable schematic facts.
    fn gen_fact(rng: &mut Lcg, syms: &[Vec<u8>]) -> Vec<FCol> {
        (0..2)
            .map(|_| {
                if rng.below(3) == 0 {
                    FCol::V(rng.below(2))
                } else {
                    FCol::G(syms[rng.below(syms.len())].clone())
                }
            })
            .collect()
    }

    /// Reference unification join: nested loop over one fact per factor, each fact renamed apart,
    /// unifying its columns with the query variables through the same trail. Collects fully-ground
    /// answer rows, the same projection the zipper join emits.
    fn naive_rec(
        fi: usize,
        factors: &[Factor],
        factor_facts: &[Vec<Vec<FCol>>],
        env: &mut Env,
        nvars: usize,
        out: &mut BTreeSet<Vec<Vec<u8>>>,
    ) {
        if fi == factors.len() {
            let mut row = Vec::with_capacity(nvars);
            for v in 0..nvars {
                match env.ground_of(v) {
                    Some(g) => row.push(g),
                    None => return,
                }
            }
            out.insert(row);
            return;
        }
        for fact in &factor_facts[fi] {
            let mark = env.mark();
            let mut slot_ids: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
            let mut ok = true;
            for (ci, col) in fact.iter().enumerate() {
                let v = factors[fi].cols[ci];
                let cok = match col {
                    FCol::G(g) => env.unify_var_ground(v, g),
                    FCol::V(slot) => {
                        let id = match slot_ids.get(slot) {
                            Some(&id) => id,
                            None => {
                                let id = env.fresh();
                                slot_ids.insert(*slot, id);
                                id
                            }
                        };
                        env.unify_var_var(v, id)
                    }
                };
                if !cok {
                    ok = false;
                    break;
                }
            }
            if ok {
                naive_rec(fi + 1, factors, factor_facts, env, nvars, out);
            }
            env.rollback(mark);
        }
    }

    #[test]
    fn unify_join_matches_naive() {
        for seed in 0..400u64 {
            let mut rng = Lcg::new(seed.wrapping_add(11));
            let nsyms = 2 + rng.below(2);
            let syms: Vec<Vec<u8>> = (0..nsyms)
                .map(|i| sym(&((b'a' + i as u8) as char).to_string()))
                .collect();

            let mut map = PathMap::<()>::new();
            let mut e_facts: Vec<Vec<FCol>> = Vec::new();
            let mut f_facts: Vec<Vec<FCol>> = Vec::new();
            let nfacts = 3 + rng.below(6);
            for _ in 0..nfacts {
                let fe = gen_fact(&mut rng, &syms);
                if map.insert(&encode_fact("e", &fe), ()).is_none() {
                    e_facts.push(fe);
                }
                let ff = gen_fact(&mut rng, &syms);
                if map.insert(&encode_fact("f", &ff), ()).is_none() {
                    f_facts.push(ff);
                }
            }
            let pe = relation_prefix("e", 3);
            let pf = relation_prefix("f", 3);

            let queries: Vec<(Vec<Factor>, Vec<usize>, usize)> = vec![
                (vec![Factor { prefix: pe.clone(), cols: vec![0, 1] }], vec![0, 1], 2),
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![0, 2] },
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pf.clone(), cols: vec![1, 2] },
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // cyclic: triangle over schematic edges (the catch-up-with-unification path).
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                        Factor { prefix: pe.clone(), cols: vec![2, 0] },
                    ],
                    vec![0, 1, 2],
                    3,
                ),
                // cyclic four-cycle over schematic edges.
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 2] },
                        Factor { prefix: pe.clone(), cols: vec![2, 3] },
                        Factor { prefix: pe.clone(), cols: vec![3, 0] },
                    ],
                    vec![0, 1, 2, 3],
                    4,
                ),
                // intra-query coreference exercised against schematic data: (e $0 $1)(e $1 $0).
                (
                    vec![
                        Factor { prefix: pe.clone(), cols: vec![0, 1] },
                        Factor { prefix: pe.clone(), cols: vec![1, 0] },
                    ],
                    vec![0, 1],
                    2,
                ),
            ];

            for (factors, order, nvars) in &queries {
                let factor_facts: Vec<Vec<Vec<FCol>>> = factors
                    .iter()
                    .map(|fac| if fac.prefix == pe { e_facts.clone() } else { f_facts.clone() })
                    .collect();

                let got = unify_join_zipper(&map, factors, order, *nvars);
                let mut env = Env::new(*nvars);
                let mut want = BTreeSet::new();
                naive_rec(0, factors, &factor_facts, &mut env, *nvars, &mut want);

                assert_eq!(got, want, "seed {seed}: unify join must match the naive unifier");
            }
        }
    }

    #[test]
    fn least_ge_matches_brute_force() {
        let sets: &[&[u8]] = &[
            &[],
            &[0],
            &[255],
            &[0, 1, 2, 63, 64, 65, 127, 128, 191, 192, 255],
            &[10, 50, 90, 130, 170, 210, 250],
            &[63, 64],
        ];
        for set in sets {
            let mask = mask_of(set);
            for k in 0u8..=255 {
                let want = set.iter().copied().filter(|&b| b >= k).min();
                assert_eq!(least_ge(&mask, k), want, "set={set:?} k={k}");
            }
        }
    }

    #[test]
    fn first_subterm_len_parses_each_shape() {
        // symbol "ab": SymbolSize(2), 'a', 'b'  -> 3 bytes
        let sym = [TAG_SYMSIZE | 2, b'a', b'b'];
        assert_eq!(first_subterm_len(&sym), 3);
        assert!(first_subterm_is_ground(&sym));

        // NewVar -> 1 byte, non-ground
        let nv = [NEWVAR_BYTE];
        assert_eq!(first_subterm_len(&nv), 1);
        assert!(!first_subterm_is_ground(&nv));

        // VarRef(0) -> 1 byte, non-ground
        let vr = [TAG_VARREF | 0];
        assert_eq!(first_subterm_len(&vr), 1);
        assert!(!first_subterm_is_ground(&vr));

        // (k v0):  Arity(2), Sym("k"), Sym("v0")
        let k = TAG_SYMSIZE | 1;
        let v0 = TAG_SYMSIZE | 2;
        let compound = [TAG_ARITY | 2, k, b'k', v0, b'v', b'0'];
        assert_eq!(first_subterm_len(&compound), 6);
        assert!(first_subterm_is_ground(&compound));

        // (k $x): Arity(2), Sym("k"), NewVar  -> 4 bytes, non-ground
        let compound_var = [TAG_ARITY | 2, k, b'k', NEWVAR_BYTE];
        assert_eq!(first_subterm_len(&compound_var), 4);
        assert!(!first_subterm_is_ground(&compound_var));

        // trailing bytes after the first subterm are ignored: (e A B) prefix then junk
        let mut buf = compound.to_vec();
        buf.extend_from_slice(&[0xFF, 0xFF]);
        assert_eq!(first_subterm_len(&buf), 6);
    }
}
