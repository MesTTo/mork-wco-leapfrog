# A worst-case-optimal join for MORK

MORK evaluates a conjunctive `(exec .. (, p1 p2 ..) ..)` body with the ProductZipper, a
relation-at-a-time join that materializes the intermediate product before pruning it. On a triangle
over a hub that product is the s² two-paths through the hub, pruned to the few real triangles. This
adds a variable-at-a-time leapfrog join (`overlay/zipper_join.rs`) that seeks the PathMap byte-trie
directly and intersects the factors on each shared variable, so the two-paths are never built.
A router sends every nonempty relation-prefixed conjunction to the join and returns exactly MORK's
bytes; on the triangle it seeks in O(s).

The join unifies in both directions. A variable in a stored fact is a wildcard that can bind a query
subterm, so the join does data-side capture: for a query `(r (a $p) b)` against a fact `(r $d b)`,
the stored `$d` binds the whole compound `(a $p)`. That second direction, stored variables binding
query subterms, is the step MORK's matcher performs and a relational leapfrog does not. The head
position is a column like the rest: the seek prefix is the arity byte alone, so a variable query
head unifies with every stored head and a wildcard stored head is captured under a ground query
head. Everything runs over MORK's live PathMap, with no copy of the data. The term encoding, the
unification, and the answer emit are `mork_expr`'s own (`Tag`/`byte_item`, `unify`, `apply`); the
module contributes the seek order.

## The result

Run over stock MORK on the AGM-blowup triangle `(e $x $y) (e $y $z) (e $x $z)` over a hub
of `s` in-edges and `s` out-edges (plus three ground triangles):

```
    s  ans | PZ transitions       PZ us | leapfrog us | PZ/leapfrog   PZ us/s^2
  128    3 |         99654        2713 |         363 |      7.5x        0.17
  256    3 |        395846       10010 |         693 |     14.4x        0.15
  512    3 |       1578054       39789 |        1325 |     30.0x        0.15
 1024    3 |       6301766      155661 |        2790 |     55.8x        0.15
 2048    3 |      25186374      622708 |        5238 |    118.9x        0.15
 4096    3 |     100704326     2498354 |       10490 |    238.2x        0.15
```

The ProductZipper is Θ(s²): its transitions grow as s² and its microseconds over s² stay flat as s
grows. The leapfrog is O(s) on this instance: its microseconds double when s doubles. So the
speedup grows with s, to 238× at s = 4096. Both return the same three triangles. The leapfrog
column times the whole sound path, the routability check and the join together; the routability
check is parse-level and reads nothing from the map.

## Byte-identical to MORK

The router preserves MORK's semantics exactly, and `run.sh` checks it two ways.

A capture + compound + head-position corpus, each case run through both engines and compared:

```
[match] capture query constant                        (via leapfrog)
[match] witness: data var captures query compound (a $p) (via leapfrog)
[match] cyclic compound capture                       (via leapfrog)
[match] occurs-check compound (must be empty)         (via leapfrog)
[match] join-propagated capture (cycle rejected)      (via leapfrog)
[match] ground + wildcard fact                        (via leapfrog)
[match] coreferent data fact (free-var answer)        (via leapfrog-free)
[match] ground triangle                               (via leapfrog)
[match] variable-headed query                         (via leapfrog)
[match] wildcard-headed fact                          (via leapfrog)
[match] wildcard head meets variable head             (via leapfrog-free)
[match] wildcard fact propagates a compound through a cycle (via leapfrog-free)
```

The `leapfrog-free` cases have a free or schematic answer: positions bound by one schematic fact
come out as one coordinated variable, exactly as MORK emits it. And 4000 random conjunctive
queries, variable heads, wildcard-headed facts, and compound `(k ..)` columns on both sides
included:

```
4000 random trials: 3895 leapfrog (ground), 105 leapfrog (free-var), 0 fallback, 298 non-empty, 0 mismatches
```

One distribution constraint is semantic, stated where the generator lives: a variable-headed
pattern keeps total arity 3, because at total arity 4 it matches the harness's own `(exec ..)` and
`(ans ..)` atoms. That is real full-evaluation semantics, but not the single query the differential
compares; the module's own differential covers the shape against a reference with no machinery to
collide with.

## Data-side capture of a compound

The corpus witness is the case that separates unification from a relational join. The query
`(, (r (a $p) b) (r (b) $p))` over facts `(r $d b), (r a b)` has answer `(ans b)`: `(r (b) $p)`
binds `$p = b` through the data variable `$d` capturing `(b)`, then `(r (a $p) b)` with `$p = b` is
`(r (a b) b)`, which the same `$d` captures as `(a b)`. A relational join, where query variables
bind fact subterms but not the reverse, returns nothing here. The leapfrog captures the compound,
and matches the ProductZipper and SWI-Prolog under occurs-check.

There is no declined shape. Earlier revisions held back the capture that binds a non-ground
compound and propagates it through a shared variable, where a per-column union-find diverges from
unification (`nonflat_uf_unsound`). The per-column step is no longer that union-find: it is
`mork_expr::unify` threaded through one bindings store, and an assignment whose bindings close a
cycle (an occurs violation built across columns) is rejected at the answer emit, mirroring
`Expr::_unify`. That covers the shape, and the corpus pins the recovered case: a fully-wildcard
fact captures a compound and propagates it through a four-factor cycle, byte-identical to the
ProductZipper.

## How to run

```
./run.sh
```

It clones MORK (trueagi-io/MORK) and PathMap (Adam-Vandervorst/PathMap) at the pinned
commits into `build/`, overlays the one module and the one example, and runs the demonstration.
Needs a nightly Rust toolchain; `RUSTFLAGS="-C target-cpu=native"` is set for you (gxhash needs
aes and sse2).

## How the router stays sound

Routing is total on nonempty relation-prefixed conjunctions, so soundness lives in the join, not in
a gate. Three facts carry it, each with a matching lemma in `proofs/TotalRouterSafe.thy`. Pruning a
branch whose equation prefix has no solution is sound, because a solution of the system solves
every subsystem (`solvable_mono`). The columns cannot be decided independently, because pairwise
unifiability does not give a simultaneous solution (`threading_necessary`); one bindings store
threads the whole descent, re-solved by `mork_expr::unify` at each accepted column. And the
emit-time cycle rejection is exactly unsolvability: a variable equated with a term properly
containing it has no finite solution (`occurs_unsolvable`).

Free-variable answers route to the leapfrog too. `unify_join_zipper_body_rows_rendered` encodes each
answer tuple through one shared variable map, so a variable a stored fact shares across two answer
positions (the fact `(e $u $u)` binding `$x` and `$y` together) emits as one coordinated
NewVar/VarRef, byte-for-byte what MORK's exec emit produces.

An in-module adversarial differential backs the router empirically: the RAW join, no router, must
agree with a nested-loop reference over the same `unify` on eleven templates centered on the
hardest shapes, wildcard and compound heads included (`ADV_N` seeds; the suite default is 300, the
sealing run used 20000, 0 mismatches). Any divergence would sit in the seek order, not the
unification.

## Scope of the speedup

The win is on join-bound conjunctive queries, where the ProductZipper materializes an intermediate
the worst-case-optimal join prunes. The triangle is that case. It is not a claim about MeTTa program
speed in general: the exec/meta-rewrite loop is bound by how many times it re-derives an
accumulating space, not by a per-query join intermediate, so a different lever (semi-naive delta)
governs there. Wiring this join into `metta_calculus`'s dispatch so a conjunctive body uses it is
the next step; the router here is a standalone demonstration of the join and its boundary.

## Provenance

- MORK: `trueagi-io/MORK` at `4a101d1`, unchanged except the single `pub mod zipper_join;` line the
  overlay adds to `kernel/src/lib.rs`. The ProductZipper it is measured against is MORK's own.
- PathMap: `Adam-Vandervorst/PathMap` at `5569535`.
- Overlay: `zipper_join.rs` (the join, depends only on PathMap and MORK's `expr`) and
  `wco_leapfrog.rs` (the demonstration, depends only on MORK + PathMap).

## Proofs

`proofs/` holds the Isabelle theories behind the design (Isabelle2025; `isabelle build -D proofs`).
`RoutingSafe.thy` proves that on ground terms unifiability is equality, the coincidence behind the
ground fast path. `ZipperUnifySafe.thy` proves the flat coincidence and the boundary of the
retired byte-level union-find (`nonflat_uf_unsound`), the mechanism whose decline the router no
longer needs. `TotalRouterSafe.thy` proves the equation-system facts the total router rests on:
subsystem solvability, the necessity of threading one bindings store, and the unsolvability of an
occurs violation, which is what the emit-time cycle rejection removes. The specific router and its
emit are checked empirically by the differentials, not by these theories.
