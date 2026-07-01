//! A worst-case-optimal join for MORK: the leapfrog-unification join (`zipper_join`, ported
//! verbatim into upstream) behind a sound router, over MORK's LIVE PathMap. Depends only on stock
//! MORK + PathMap.
//!
//! Upstream MORK answers a conjunctive `(exec .. (, p1 p2 ..) ..)` with the ProductZipper, a
//! product/nested join that is O(s^2) on the triangle. This routes a body to the variable-at-a-time
//! leapfrog when that join is byte-identical to the ProductZipper (every factor argument is a
//! variable and every answer component comes out ground) and falls back to the ProductZipper
//! otherwise. So the router equals MORK's answers everywhere, and is worst-case-optimal on the
//! conjunctive queries the leapfrog covers.
//!
//!   RUSTFLAGS="-C target-cpu=native" cargo +nightly run -p mork --release --example wco_leapfrog

use mork::space::Space;
use mork::zipper_join::{parse_body_factors, unify_join_zipper_partial};
use mork_expr::serialize;
use pathmap::zipper::{ZipperIteration, ZipperMoving};
use std::collections::BTreeSet;

/// Encode a conjunction body with MORK's own parser: insert it and read the key back. No hand
/// encoder, so the bytes are exactly what the ProductZipper sees.
fn encode_body(patterns: &[&str]) -> Vec<u8> {
    let mut s = Space::new();
    s.add_all_sexpr(format!("(, {})", patterns.join(" ")).as_bytes()).unwrap();
    let mut rz = s.btm.read_zipper();
    rz.to_next_val();
    rz.path().to_vec()
}

/// A fully-ground answer row `[b_v0, b_v1, ..]` rendered as the `(ans ..)` bytes MORK's exec emits,
/// then serialized: `[Arity(N+1)] [SymSize(3)] ans b0 b1 ..`.
fn ans_string(row: &[Vec<u8>]) -> String {
    let mut v = vec![row.len() as u8 + 1, 0xC0 | 3];
    v.extend_from_slice(b"ans");
    for b in row {
        v.extend_from_slice(b);
    }
    serialize(&v)
}

fn snapshot(space: &Space) -> BTreeSet<Vec<u8>> {
    let mut set = BTreeSet::new();
    let mut rz = space.btm.read_zipper();
    while rz.to_next_val() {
        set.insert(rz.path().to_vec());
    }
    set
}

/// The variables of a body in first-occurrence order (the order the answer tuple is keyed by).
fn ans_vars_of(patterns: &[&str]) -> Vec<String> {
    let mut seen: Vec<String> = Vec::new();
    for p in patterns {
        let b = p.as_bytes();
        let mut i = 0;
        while i < b.len() {
            if b[i] == b'$' {
                let start = i;
                let mut j = i + 1;
                while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
                    j += 1;
                }
                let name = p[start..j].to_string();
                if !seen.contains(&name) {
                    seen.push(name);
                }
                i = j;
            } else {
                i += 1;
            }
        }
    }
    seen
}

/// MORK's ProductZipper answers to the body, the matcher `transitions` it spent, and microseconds.
fn mork_productzipper(facts: &str, patterns: &[&str], ans: &[String]) -> (BTreeSet<String>, usize, u128) {
    let mut space = Space::new();
    space.add_all_sexpr(facts.as_bytes()).unwrap();
    let before = snapshot(&space);
    let exec = format!("(exec 0 (, {}) (, (ans {})))\n", patterns.join(" "), ans.join(" "));
    space.add_all_sexpr(exec.as_bytes()).unwrap();
    unsafe { mork::space::transitions = 0 };
    let t0 = std::time::Instant::now();
    space.metta_calculus(1);
    let us = t0.elapsed().as_micros();
    let transitions = unsafe { mork::space::transitions };
    let mut out = BTreeSet::new();
    let mut rz = space.btm.read_zipper();
    while rz.to_next_val() {
        let p = rz.path().to_vec();
        if !before.contains(&p) {
            let s = serialize(&p);
            if s.starts_with(&format!("[{}] ans", ans.len() + 1)) {
                out.insert(s);
            }
        }
    }
    (out, transitions, us)
}

/// Whether every argument of every factor is a single variable (no ground column, no compound).
/// This is the leapfrog's provably-sound class: with no ground argument there is no literal byte
/// prefix that could skip a data variable which should capture it, and every factor carries a
/// column so it is actually checked. A ground column or a leading constant routes to the ProductZipper.
fn all_variable_columns(patterns: &[&str]) -> bool {
    for p in patterns {
        let s = p.trim();
        if !s.starts_with('(') || !s.ends_with(')') {
            return false;
        }
        let (mut depth, mut toks, mut cur) = (0i32, Vec::new(), String::new());
        for ch in s[1..s.len() - 1].chars() {
            match ch {
                '(' => {
                    depth += 1;
                    cur.push(ch);
                }
                ')' => {
                    depth -= 1;
                    cur.push(ch);
                }
                c if c.is_whitespace() && depth == 0 => {
                    if !cur.is_empty() {
                        toks.push(std::mem::take(&mut cur));
                    }
                }
                c => cur.push(c),
            }
        }
        if !cur.is_empty() {
            toks.push(cur);
        }
        if toks.len() < 2 || toks[1..].iter().any(|a| !a.starts_with('$')) {
            return false;
        }
    }
    true
}

/// The sound router: the WCO leapfrog when every factor is all variable columns and every answer
/// row is fully ground (the class it is byte-identical to the ProductZipper on), else the
/// ProductZipper. Returns the answers, which path ran, and the join microseconds.
fn router(facts: &str, patterns: &[&str], ans: &[String]) -> (BTreeSet<String>, &'static str, u128) {
    if all_variable_columns(patterns) {
        let body = encode_body(patterns);
        if let Some((factors, nvars)) = parse_body_factors(&body) {
            let mut space = Space::new();
            space.add_all_sexpr(facts.as_bytes()).unwrap();
            let order: Vec<usize> = (0..nvars).collect();
            let t0 = std::time::Instant::now();
            let rows = unify_join_zipper_partial(&space.btm, &factors, &order, nvars);
            if rows.iter().all(|r| r.iter().all(|c| c.is_some())) {
                let us = t0.elapsed().as_micros();
                let out = rows
                    .iter()
                    .map(|r| ans_string(&r.iter().map(|c| c.clone().unwrap()).collect::<Vec<_>>()))
                    .collect();
                return (out, "leapfrog", us);
            }
        }
    }
    let (pz, _, us) = mork_productzipper(facts, patterns, ans);
    (pz, "fallback", us)
}

fn triangle_space(s: usize) -> String {
    let mut prog = String::new();
    for k in 0..s {
        prog.push_str(&format!("(e i{k} c)\n(e c o{k})\n"));
    }
    for t in 0..3 {
        prog.push_str(&format!("(e p{t}a p{t}b)\n(e p{t}b p{t}c)\n(e p{t}a p{t}c)\n"));
    }
    prog
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// A random flat conjunctive query and fact set: relations over variable/constant columns, facts
/// that may carry data variables (schematic). No compounds, so this is the leapfrog's routable
/// class; a constant column still makes the body fall back, exercising both paths.
fn gen_case(rng: &mut Rng) -> (String, Vec<String>) {
    let rels = ["e", "p", "q", "r"];
    let vars = ["$x", "$y", "$z"];
    let consts = ["a", "b", "c", "d"];
    let dvars = ["$u", "$v"];
    loop {
        let npat = 1 + rng.below(3);
        let mut patterns = Vec::new();
        for _ in 0..npat {
            let rel = rels[rng.below(rels.len())];
            let arity = 2 + rng.below(2);
            let args: Vec<String> = (0..arity)
                .map(|_| {
                    if rng.below(3) == 0 {
                        consts[rng.below(consts.len())].to_string()
                    } else {
                        vars[rng.below(vars.len())].to_string()
                    }
                })
                .collect();
            patterns.push(format!("({} {})", rel, args.join(" ")));
        }
        let pats: Vec<&str> = patterns.iter().map(|s| s.as_str()).collect();
        if ans_vars_of(&pats).is_empty() {
            continue;
        }
        let nfacts = rng.below(8);
        let mut facts = String::new();
        for _ in 0..nfacts {
            let rel = rels[rng.below(rels.len())];
            let arity = 2 + rng.below(2);
            let args: Vec<String> = (0..arity)
                .map(|_| {
                    if rng.below(4) == 0 {
                        dvars[rng.below(dvars.len())].to_string()
                    } else {
                        consts[rng.below(consts.len())].to_string()
                    }
                })
                .collect();
            facts.push_str(&format!("({} {})\n", rel, args.join(" ")));
        }
        return (facts, patterns);
    }
}

fn main() {
    let mut bad = 0;

    println!("=== 1. Correctness: router vs MORK ProductZipper on a capture-heavy corpus ===\n");
    let corpus: &[(&str, &str, &[&str])] = &[
        ("capture query constant", "(rel a $w)\n", &["(rel $x b)"]),
        ("witness: p fixed by join", "(r $d b)\n(r a b)\n", &["(r (a $p) b)", "(r (b) $p)"]),
        ("ground + wildcard fact", "(p a)\n(p b)\n(q a)\n(q $w)\n", &["(p $x)", "(q $x)"]),
        ("coreferent data fact (free-var answer)", "(e $u $u)\n(e a b)\n(e b c)\n", &["(e $x $y)", "(e $y $z)"]),
        ("occurs (must be empty)", "(e $w $w)\n", &["(e $x (f $x))"]),
        ("ground triangle", "(e a b)\n(e a c)\n(e b c)\n(e b d)\n", &["(e $x $y)", "(e $y $z)", "(e $x $z)"]),
    ];
    for (name, facts, patterns) in corpus {
        let ans = ans_vars_of(patterns);
        let (mork, _, _) = mork_productzipper(facts, patterns, &ans);
        let (rt, path, _) = router(facts, patterns, &ans);
        let ok = mork == rt;
        bad += !ok as usize;
        println!("[{}] {name} (via {path})", if ok { "match" } else { "MISMATCH" });
        if !ok {
            println!("    MORK  : {mork:?}\n    router: {rt:?}");
        }
    }

    println!("\n=== 2. Correctness: router vs MORK over a random flat-conjunctive distribution ===\n");
    let mut rng = Rng(0x243F6A8885A308D3);
    let trials = 4000;
    let (mut leapfrog, mut fallback, mut nonempty) = (0, 0, 0);
    for i in 0..trials {
        let (facts, patterns) = gen_case(&mut rng);
        let pats: Vec<&str> = patterns.iter().map(|s| s.as_str()).collect();
        let ans = ans_vars_of(&pats);
        let (mork, _, _) = mork_productzipper(&facts, &pats, &ans);
        let (rt, path, _) = router(&facts, &pats, &ans);
        if rt != mork {
            bad += 1;
            if bad <= 5 {
                println!("MISMATCH trial {i} ({path})\n  facts={facts:?}\n  pats={patterns:?}\n  MORK={mork:?}\n  router={rt:?}");
            }
        }
        if path == "leapfrog" {
            leapfrog += 1;
        } else {
            fallback += 1;
        }
        nonempty += !mork.is_empty() as usize;
    }
    println!("{trials} random trials: {leapfrog} leapfrog, {fallback} fallback, {nonempty} non-empty, {bad} mismatches");

    println!("\n=== 3. Optimality: router (leapfrog) vs ProductZipper on the AGM-blowup triangle ===\n");
    let tri = &["(e $x $y)", "(e $y $z)", "(e $x $z)"];
    let tri_ans = ans_vars_of(tri);
    println!("{:>5} {:>4} | {:>13} {:>11} | {:>11} | {:>9} {:>11}", "s", "ans", "PZ transitions", "PZ us", "router us", "PZ/router", "PZ us/s^2");
    for &s in &[128usize, 256, 512, 1024, 2048, 4096] {
        let facts = triangle_space(s);
        let (pz, pz_trans, pz_us) = mork_productzipper(&facts, tri, &tri_ans);
        let (rt, path, rt_us) = router(&facts, tri, &tri_ans);
        assert_eq!(pz, rt, "s={s}: router != ProductZipper");
        assert_eq!(path, "leapfrog", "s={s}: triangle must route to the leapfrog");
        println!(
            "{s:>5} {:>4} | {pz_trans:>13} {pz_us:>11} | {rt_us:>11} | {:>8.1}x {:>11.2}",
            pz.len(),
            pz_us as f64 / rt_us.max(1) as f64,
            pz_us as f64 / (s * s) as f64
        );
    }
    println!("\nRouter answers == MORK everywhere; O(s) on the triangle where the ProductZipper is O(s^2).");
    std::process::exit(if bad == 0 { 0 } else { 1 });
}
