# A worst-case-optimal join for MORK

Upstream MORK answers a conjunctive `(exec .. (, p1 p2 ..) ..)` with the ProductZipper, a
product/nested join. On a triangle query over a hub it builds the O(s²) two-paths through the hub
before pruning them down to the few real triangles. This adds a variable-at-a-time leapfrog join
(`overlay/zipper_join.rs`) that seeks the PathMap byte-trie directly and intersects the factors on
each shared variable, so it never materializes those intermediates. Behind a sound router it
returns exactly MORK's answers, and on the triangle it runs in O(s).

The join carries unification, not equality alone: a variable in a stored fact is a wildcard that
binds through a trail, so coreference in the data is respected. This is the trie-join integrated
with unification, run over MORK's live PathMap with no copy of the data.

## The result

Run over stock upstream MORK on the AGM-blowup triangle `(e $x $y) (e $y $z) (e $x $z)` over a hub
of `s` in-edges and `s` out-edges (plus three ground triangles):

```
    s | ProductZipper us | leapfrog us | speedup
  256 |           10,147 |         571 |    17.8x
 1024 |          155,215 |       2,257 |    68.8x
 2048 |          625,308 |       4,519 |   137.5x
 4096 |        2,483,368 |       8,932 |   278.0x
```

The ProductZipper is Θ(s²) (its microseconds over s² stay flat as s grows); the leapfrog is O(s)
here (its microseconds double when s doubles). So the speedup grows with s and is 278× at
s = 4096. Both return the same three triangles.

## It equals MORK's answers

The join is not a different semantics. A router sends a body to the leapfrog only when the two are
provably byte-identical, and falls back to the ProductZipper otherwise, so the answers always match
MORK. `run.sh` checks this on a capture-heavy corpus and on 4000 random flat-conjunctive queries:

```
4000 random trials: 660 leapfrog, 3340 fallback, 283 non-empty, 0 mismatches
```

The corpus includes data-side capture cases; those fall back, and upstream MORK answers them
correctly on its own (it does data-side capture). This join agrees with MORK; it does not fix it.

## How to run

```
./run.sh
```

It clones upstream MORK (trueagi-io/MORK) and PathMap (Adam-Vandervorst/PathMap) at the pinned
commits into `build/`, overlays the one module and the one example, and runs the demonstration.
Needs a nightly Rust toolchain; `RUSTFLAGS="-C target-cpu=native"` is set for you (gxhash needs
aes and sse2).

## How the router stays sound

The leapfrog is worst-case-optimal but not complete on every body. Two shapes diverge from the
ProductZipper, and the random differential above is what surfaced them:

- A fully-ground factor like `(e b c)` folds to a prefix with no join column, so the join never
  checks it exists and can report a spurious answer.
- A data variable in a leading position, `(e $v b a)` under a query `(e b b $z)`, is skipped: the
  join descends the literal bytes `e b b` and never reaches the fact whose first argument is the
  variable that should capture `b`.

So the router routes to the leapfrog only when every argument of every factor is a variable and
every answer component comes out ground. That class has no ground prefix to miss a capture and no
unchecked factor, and it is exactly where the two joins agree. Everything else, including data-side
capture of a compound, falls back to the ProductZipper.

## Scope, honestly

The leapfrog covers all-variable-column conjunctive joins, which is where worst-case-optimality
matters (multi-way joins like the triangle). Single-factor queries, ground columns, and
free-variable answers fall back; they are correct but not accelerated. A single join that is
simultaneously worst-case-optimal and does data-side capture of a compound is not here yet, and the
leapfrog declines compounds today. The router is a standalone demonstration; wiring it into MORK's
exec dispatch so `metta_calculus` uses it is the next step.

## Provenance

- MORK: `trueagi-io/MORK` at `4a101d1`, unchanged except the single `pub mod zipper_join;` line the
  overlay adds to `kernel/src/lib.rs`. The ProductZipper it is measured against is upstream's.
- PathMap: `Adam-Vandervorst/PathMap` at `5569535`.
- Overlay: `zipper_join.rs` (the join, depends only on PathMap) and `wco_leapfrog.rs` (the
  demonstration, depends only on MORK + PathMap).

## Proofs

`proofs/` holds the Isabelle theories behind the design (Isabelle2025). `ZipperUnifySafe.thy`
proves the trail/union-find the join threads is sound. `RoutingSafe.thy` proves that on flat data a
union-find agreement equals first-order unification, and that on non-flat data it does not, which
is the reason a compound falls back rather than routing. The specific gate this router uses and the
two divergent shapes above are checked empirically by the differential, not by these theories.
