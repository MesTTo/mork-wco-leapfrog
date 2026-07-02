# A worst-case-optimal join for MORK

MORK evaluates a conjunctive `(exec .. (, p1 p2 ..) ..)` body with the ProductZipper, a
relation-at-a-time join that materializes the intermediate product before pruning it. On a triangle
over a hub that product is the s² two-paths through the hub, pruned to the few real triangles. This
adds a variable-at-a-time leapfrog join (`overlay/zipper_join.rs`) that seeks the PathMap byte-trie
directly and intersects the factors on each shared variable, so the two-paths are never built.
A router sends every nonempty relation-prefixed conjunction to the join and returns exactly MORK's
bytes; on the triangle it seeks in O(s). And the engine itself dispatches: the space-to-space
transform inside `metta_calculus` routes intersecting conjunctive bodies to the join
(`overlay/space_dispatch.patch`), so `mork run yourfile.mm2` evaluates them on it.

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
    s  ans | PZ transitions       PZ us | leapfrog us    wired us |  PZ/wired   PZ us/s^2
  128    3 |         99654        2462 |         367         364 |      6.8x        0.15
  256    3 |        395846        9888 |         738        1069 |      9.2x        0.15
  512    3 |       1578054       38467 |        1389        1342 |     28.7x        0.15
 1024    3 |       6301766      155612 |        2715        2727 |     57.1x        0.15
 2048    3 |      25186374      622829 |        5403        5339 |    116.7x        0.15
 4096    3 |     100704326     2521317 |       11028       10846 |    232.5x        0.15
```

The ProductZipper is Θ(s²): its transitions grow as s² and its microseconds over s² stay flat as s
grows. The leapfrog is O(s) on this instance: its microseconds double when s doubles. So the
speedup grows with s, to 232× at s = 4096. Both return the same three triangles. The leapfrog
column times the router over the module; the wired column times the whole engine step through
`metta_calculus` with the dispatch on, which costs the same, so the engine adds nothing over the
join. The same holds from the command line: `./run.sh compare` on this workload prints the stock
arm walking 395846 transitions in 9 ms at s = 256 and the wired arm walking 0 in under a
millisecond, byte-identical spaces.

## Byte-identical to MORK

The dispatch preserves MORK's semantics exactly, and it is checked at three levels.

Every case in a capture + compound + head-position corpus runs three ways, the stock engine (the
dispatch pinned off), the router over the module, and the wired engine, and all three must agree
byte for byte:

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
4000 random trials, each also through the wired engine: 3895 leapfrog (ground), 105 leapfrog (free-var), 0 fallback, 298 non-empty, 0 mismatches
```

One distribution constraint is semantic, stated where the generator lives: a variable-headed
pattern keeps total arity 3, because at total arity 4 it matches the harness's own `(exec ..)` and
`(ans ..)` atoms. That is real full-evaluation semantics, but not the single query the differential
compares; the engine-level differential below has no such constraint, because both arms run full
evaluation and collide with the machinery identically.

The engine level is sealed in-repo (`cargo test -p mork zipper_join` in the built tree): every
resource program under `kernel/resources/` runs to several depths with the dispatch off and on and
must produce identical spaces and step counts (the run.sh sweep extends this to 2000 steps), and
20000 random whole programs, several exec atoms with chained and machinery-colliding bodies run
for several steps, must agree the same way. A transform-level test also pins the match count and
changed flag per body, multiplicity included, and a re-index test pins that a streamed leaf hands
back a coreferent fact's original bytes. Nil's backward-via-forward chainer (upstream's `bench
bfc`, reproduced here as plain MM2 files) checks out at every proof size, 5 through 19: spaces
byte-identical, the bench's own proof assertions passing, step counts and match counts equal.

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
./run.sh                            # the three-way demonstration above
./run.sh yourfile.mm2 [args..]      # run your MM2 program on the wired engine
./run.sh compare yourfile.mm2 [steps]   # both engines on your program, spaces diffed, times printed
```

It clones MORK (trueagi-io/MORK) and PathMap (Adam-Vandervorst/PathMap) at the pinned
commits into `build/`, overlays the module, the example, and the engine patch, and runs. Needs a
nightly Rust toolchain; `RUSTFLAGS="-C target-cpu=native"` is set for you (gxhash needs aes and
sse2). Extra arguments after your file pass through to `mork run`, so `--steps 100` or
`--timing true` work as usual, and `MORK_LEAPFROG=0 ./run.sh yourfile.mm2` runs the same program
on the stock engine.

## What the engine dispatches

The patch adds one function, `Space::query_multi_dispatch`, and points the space-to-space
transform (the `,`/`,` exec path) at it. A dispatched body streams through the join one callback
per product tuple: each accepted assignment reconstructs the stored facts it sits on, pairs them
with the pattern factors exactly as `query_multi_raw` does, and re-derives the bindings with
`mork_expr::unify`, so the template instantiation and emit downstream are stock code fed the same
inputs, and match multiplicity is preserved. Interpreted sources and sinks (`I`/`O` bodies) and
the pattern-directed dumps keep the stock path and its enumeration order.

Dispatch follows a measured policy, not a reflex: a body routes to the join only when it has a
cycle the leapfrog can seek and win on. Three conjuncts, cheapest first: cyclic over the
whole-column variables (a cycle carried only inside compound arguments gives the seek nothing, and
the counter machine measured 1.6× slower without this conjunct), cyclic over the full variable
sets (alpha-acyclic queries are where a relation-at-a-time plan already meets the optimal bound,
which declines paths, semijoins, and pure products without reading data), and not functionally
degenerate (a diamond of function tables is a real hyperedge cycle whose AGM bound still collapses
to O(N), so a bounded data probe detects each simple factor's trailing functional dependency and
re-runs the reduction; `finite_domain`, exactly that shape, measured 3.7× slower dispatched and
now declines at 79 ms against 70 stock, the residual being the one-time confirm scan of the
genuinely functional tables). A graph's `edge` disproves its dependency at the first repeated
source, so a genuine cyclic pattern stops paying for the probe within a few facts and dispatches.
Dispatched everywhere instead (`MORK_LEAPFROG=all`), the counter machine runs 3.4× slower and a
10⁶-tuple pure product 1.8× slower, while one body, a gini step whose factors share variables
inside compounds over a large relation, wins 1.8×; taking that winner too is a cardinality
question, the per-eval cost-based dispatch that is the next step.

On the stock resource suite the default policy
is at parity everywhere, and the triangle above is 232×. The boundary in one contrast: the s=4096
triangle as a plain MM2 file runs `./run.sh compare` at 2497 ms stock against 10 ms wired,
byte-identical; `bench bfc` at size 19 (a 14.5 s proof search emitting 2.9M atoms) runs at parity,
because its hot bodies are single-factor `sol` lookups with no product to prune, where callgrind
puts a third of the instructions in the matcher walk and a third in the expression codec and
emit. Dispatched everywhere anyway (`MORK_LEAPFROG=all`), bfc runs 21% slower, which is the
policy earning its keep.

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
NewVar/VarRef, byte-for-byte what MORK's exec emit produces. The engine dispatch does not need the
renderer at all: it re-derives each tuple's bindings with stock `unify` and lets MORK's own emit
number the output, which is how a schematic match stays byte-identical there.

An in-module adversarial differential backs the router empirically: the RAW join, no router, must
agree with a nested-loop reference over the same `unify` on eleven templates centered on the
hardest shapes, wildcard and compound heads included (`ADV_N` seeds; the suite default is 300, the
sealing run used 20000, 0 mismatches). Any divergence would sit in the seek order, not the
unification.

## Scope of the speedup

The win is on join-bound conjunctive queries, where the ProductZipper materializes an intermediate
the worst-case-optimal join prunes. The triangle is that case, and with the dispatch wired the win
now reaches `mork run`: a program whose body intersects runs it on the join with no code change.
It is not a claim about MeTTa program speed in general: the exec/meta-rewrite loop is bound by how
many times it re-derives an accumulating space, not by a per-query join intermediate, so a
different lever (semi-naive delta) governs there, and enumeration-shaped bodies stay deliberately
on the ProductZipper. The next steps are the per-eval cost-based dispatch that can also take the
compound-shared class, and the interpreted-source paths.

## Provenance

- MORK: `trueagi-io/MORK` at `4a101d1`, changed by the single `pub mod zipper_join;` line and the
  35-line `overlay/space_dispatch.patch` (one added function and one call-site change in
  `kernel/src/space.rs`). The ProductZipper it is measured against is MORK's own.
- PathMap: `Adam-Vandervorst/PathMap` at `5569535`.
- Overlay: `zipper_join.rs` (the join, depends only on PathMap and MORK's `expr`),
  `wco_leapfrog.rs` (the demonstration), and `space_dispatch.patch` (the engine hook).

## Proofs

`proofs/` holds the Isabelle theories behind the design (Isabelle2025; `isabelle build -D proofs`).
`RoutingSafe.thy` proves that on ground terms unifiability is equality, the coincidence behind the
ground fast path. `ZipperUnifySafe.thy` proves the flat coincidence and the boundary of the
retired byte-level union-find (`nonflat_uf_unsound`), the mechanism whose decline the router no
longer needs. `TotalRouterSafe.thy` proves the equation-system facts the total router rests on:
subsystem solvability, the necessity of threading one bindings store, and the unsolvability of an
occurs violation, which is what the emit-time cycle rejection removes. The specific router and its
emit are checked empirically by the differentials, not by these theories.
