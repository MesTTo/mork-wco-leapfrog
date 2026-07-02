# A worst-case-optimal join for MORK

MORK evaluates a conjunctive `(exec .. (, p1 p2 ..) ..)` body with the ProductZipper, a
relation-at-a-time join that materializes the intermediate product before pruning it. On a triangle
over a hub that product is the s² two-paths through the hub, pruned to the few real triangles. This
adds a variable-at-a-time leapfrog join (`overlay/zipper_join.rs`) that seeks the PathMap byte-trie
directly and intersects the factors on each shared variable, so the two-paths are never built.
Behind a sound router it returns exactly MORK's bytes, and on the triangle it seeks in O(s).

The join unifies in both directions. A variable in a stored fact is a wildcard that can bind a query
subterm, so the join does data-side capture: for a query `(r (a $p) b)` against a fact `(r $d b)`,
the stored `$d` binds the whole compound `(a $p)`. That second direction, stored variables binding
query subterms, is the step MORK's matcher performs and a relational leapfrog does not. Everything
runs over MORK's live PathMap, with no copy of the data. The term encoding, the unification, and
the answer emit are `mork_expr`'s own (`Tag`/`byte_item`, `unify`, `apply`); the module contributes
the seek order.

## The result

Run over stock MORK on the AGM-blowup triangle `(e $x $y) (e $y $z) (e $x $z)` over a hub
of `s` in-edges and `s` out-edges (plus three ground triangles):

```
    s  ans | PZ transitions       PZ us | leapfrog us | PZ/leapfrog   PZ us/s^2
  128    3 |         99654        2367 |         368 |      6.4x        0.14
  256    3 |        395846       10220 |         742 |     13.8x        0.16
  512    3 |       1578054       38313 |        1427 |     26.8x        0.15
 1024    3 |       6301766      151808 |        2836 |     53.5x        0.14
 2048    3 |      25186374      613592 |        5794 |    105.9x        0.15
 4096    3 |     100704326     2470528 |       11156 |    221.5x        0.15
```

The ProductZipper is Θ(s²): its transitions grow as s² and its microseconds over s² stay flat at
0.15 as s grows. The leapfrog is O(s) on this instance: its microseconds double when s doubles. So
the speedup grows with s, to 221× at s = 4096. Both return the same three triangles. The leapfrog
column times the whole sound path, the routability check and the join together.

## Byte-identical to MORK

The router preserves MORK's semantics exactly. It sends a body to the leapfrog only when the join is
provably byte-identical to the ProductZipper, and falls back otherwise, so the answers always match
MORK. `run.sh` checks this two ways.

A capture + compound corpus, each case run through both and compared:

```
[match] capture query constant                        (via leapfrog)
[match] witness: data var captures query compound (a $p) (via leapfrog)
[match] cyclic compound capture                       (via leapfrog)
[match] occurs-check compound (must be empty)         (via leapfrog)
[match] join-propagated capture (declines, sound)     (via fallback)
[match] ground + wildcard fact                        (via leapfrog)
[match] coreferent data fact (free-var answer)        (via leapfrog-free)
[match] ground triangle                               (via leapfrog)
```

The `leapfrog-free` case has a free variable in the answer, and the two positions bound by the
schematic fact `(e $u $u)` come out as one coordinated variable, exactly as MORK emits it. And 4000
random flat-conjunctive queries, the whole class the join covers, ground answers and free-variable
answers alike:

```
4000 random trials: 3894 leapfrog (ground), 106 leapfrog (free-var), 0 fallback, 283 non-empty, 0 mismatches
```

## Data-side capture of a compound

The corpus witness is the case that separates unification from a relational join. The query
`(, (r (a $p) b) (r (b) $p))` over facts `(r $d b), (r a b)` has answer `(ans b)`: `(r (b) $p)`
binds `$p = b` through the data variable `$d` capturing `(b)`, then `(r (a $p) b)` with `$p = b` is
`(r (a b) b)`, which the same `$d` captures as `(a b)`. A relational join, where query variables
bind fact subterms but not the reverse, returns nothing here. The leapfrog captures the compound,
and matches the ProductZipper and SWI-Prolog under occurs-check.

The join covers the flat conjunctive fragment whole, ground and free-variable answers alike, and the
compound-capture shapes the matcher handles: a data variable capturing a query compound,
cyclic capture, nested coreference, and the occurs-check (which correctly returns nothing). One
shape it declines, where a single data variable both captures a non-ground compound and propagates
that capture through the join (`(e (k $x0) $x1) (e (k $x1) $x2) (h $x2 $x0)`). That decline is not a
gap left to close. `ZipperUnifySafe.thy` proves a byte-level union-find is unsound on a non-ground
compound (the lemma `nonflat_uf_unsound`), so no per-column worst-case-optimal join can take that
shape soundly. Answering it needs the per-tuple coupling the ProductZipper already does, and the
router sends exactly that shape there. Every body gets MORK's answer; every shape a per-column WCO
join can soundly take, this one takes. The gate lives in the join module, self-contained, so a
divergent body is never routed.

## How to run

```
./run.sh
```

It clones MORK (trueagi-io/MORK) and PathMap (Adam-Vandervorst/PathMap) at the pinned
commits into `build/`, overlays the one module and the one example, and runs the demonstration.
Needs a nightly Rust toolchain; `RUSTFLAGS="-C target-cpu=native"` is set for you (gxhash needs
aes and sse2).

## How the router stays sound

`unify_join_zipper_body_safe` decides routing from the encoded body and the live map alone. A flat
query routes whenever its answers are ground. A query with a compound argument routes when the
matcher and the join agree, which is every compound shape except the propagated-capture one above;
that check reads the query factors and the schematic facts under each join prefix and declines the
divergent shape. The random differential is what surfaced the boundary: an earlier all-variable
gate missed two flat shapes (a ground factor never checked to exist, and a data variable in a
leading position that should capture a query constant), both since folded into the routed class and
covered by the 4000-trial sweep.

Free-variable answers route to the leapfrog too. `unify_join_zipper_body_rows_rendered` encodes each
answer tuple through one shared variable map, so a variable a stored fact shares across two answer
positions (the fact `(e $u $u)` binding `$x` and `$y` together) emits as one coordinated
NewVar/VarRef, byte-for-byte what MORK's exec emit produces. That is the `leapfrog-free` path in the
corpus and the 106 free-variable answers in the sweep, all matching MORK.

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

`proofs/` holds the Isabelle theories behind the design (Isabelle2025). `ZipperUnifySafe.thy`
proves the per-column union-find semantics behind the join is sound. `RoutingSafe.thy` proves that
on flat data a union-find agreement equals first-order unification, and that on non-flat data it
does not, which is why a compound is checked against the matcher before routing rather than assumed
safe. The specific gate and the one divergent shape are checked empirically by the differential,
not by these theories.
