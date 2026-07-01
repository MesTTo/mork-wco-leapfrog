# A worst-case-optimal join for MORK

Upstream MORK answers a conjunctive `(exec .. (, p1 p2 ..) ..)` with the ProductZipper, a
product/nested join. On a triangle query over a hub it builds the O(s²) two-paths through the hub
before pruning them down to the few real triangles. This adds a variable-at-a-time leapfrog join
(`overlay/zipper_join.rs`) that seeks the PathMap byte-trie directly and intersects the factors on
each shared variable, so it never materializes those intermediates. Behind a sound router it
returns exactly MORK's answers, and on the triangle it runs in O(s).

The join carries unification, not equality alone. A variable in a stored fact is a wildcard, and it
can bind a query subterm, so the join does data-side capture: given a query `(r (a $p) b)` and a
fact `(r $d b)`, the stored `$d` absorbs the whole compound `(a $p)`. That is the step that makes
this unification and not a relational join, and it is the case MORK's own matcher handles that a
plain leapfrog does not. Everything runs over MORK's live PathMap, with no copy of the data.

## The result

Run over stock upstream MORK on the AGM-blowup triangle `(e $x $y) (e $y $z) (e $x $z)` over a hub
of `s` in-edges and `s` out-edges (plus three ground triangles):

```
    s | ProductZipper us | leapfrog us | speedup
  256 |            9,705 |         651 |    14.9x
 1024 |          152,441 |       2,585 |    59.0x
 2048 |          619,647 |       5,223 |   118.6x
 4096 |        2,471,936 |      10,047 |   246.0x
```

The ProductZipper is Θ(s²): its microseconds over s² stay flat (0.15) as s grows. The leapfrog is
O(s) on this instance: its microseconds double when s doubles. So the speedup grows with s and is
246× at s = 4096. Both return the same three triangles. The leapfrog column is the whole sound
path, the routability check plus the join, not the join alone.

## It equals MORK's answers

The join is not a different semantics. A router sends a body to the leapfrog only when the join is
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
[match] coreferent data fact (free-var answer)        (via fallback)
[match] ground triangle                               (via leapfrog)
```

And 4000 random flat-conjunctive queries, a class the join covers whole:

```
4000 random trials: 3894 leapfrog, 106 fallback, 283 non-empty, 0 mismatches
```

## Data-side capture of a compound

The corpus witness is the case that separates unification from a relational join. The query
`(, (r (a $p) b) (r (b) $p))` over facts `(r $d b), (r a b)` has answer `(ans b)`: `(r (b) $p)`
binds `$p = b` through the data variable `$d` capturing `(b)`, then `(r (a $p) b)` with `$p = b` is
`(r (a b) b)`, which the same `$d` captures as `(a b)`. A relational join, where query variables
bind fact subterms but not the reverse, returns nothing here. The leapfrog captures the compound,
and matches the ProductZipper and SWI-Prolog under occurs-check.

The join covers the flat conjunctive queries whole, and the compound-capture shapes the matcher
handles: a data variable capturing a query compound, cyclic capture, nested coreference, and the
occurs-check (which correctly returns nothing). It declines one shape, where a single data variable
both captures a non-ground compound and propagates that capture through the join
(`(e (k $x0) $x1) (e (k $x1) $x2) (h $x2 $x0)`). Forcing it there produces one answer the
ProductZipper does not, so the router keeps that shape on the ProductZipper. The gate is in the
join module, self-contained, so a body that would diverge is never routed.

## How to run

```
./run.sh
```

It clones upstream MORK (trueagi-io/MORK) and PathMap (Adam-Vandervorst/PathMap) at the pinned
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

Free-variable answers fall back too. The join computes them, but this standalone demo renders ground
answers and leaves the fresh-variable emit to MORK, so a body whose answer carries a free variable
routes to the ProductZipper here.

## What the speedup is, and is not

The win is on join-bound conjunctive queries, where the ProductZipper materializes an intermediate
the worst-case-optimal join prunes. The triangle is that case. It is not a claim about MeTTa program
speed in general: the exec/meta-rewrite loop is bound by how many times it re-derives an
accumulating space, not by a per-query join intermediate, so a different lever (semi-naive delta)
governs there. Wiring this join into `metta_calculus`'s dispatch so a conjunctive body uses it is
the next step; the router here is a standalone demonstration of the join and its boundary.

## Provenance

- MORK: `trueagi-io/MORK` at `4a101d1`, unchanged except the single `pub mod zipper_join;` line the
  overlay adds to `kernel/src/lib.rs`. The ProductZipper it is measured against is upstream's.
- PathMap: `Adam-Vandervorst/PathMap` at `5569535`.
- Overlay: `zipper_join.rs` (the join, depends only on PathMap) and `wco_leapfrog.rs` (the
  demonstration, depends only on MORK + PathMap).

## Proofs

`proofs/` holds the Isabelle theories behind the design (Isabelle2025). `ZipperUnifySafe.thy`
proves the trail/union-find the join threads is sound. `RoutingSafe.thy` proves that on flat data a
union-find agreement equals first-order unification, and that on non-flat data it does not, which is
why a compound is checked against the matcher before routing rather than assumed safe. The specific
gate and the one divergent shape are checked empirically by the differential, not by these theories.
