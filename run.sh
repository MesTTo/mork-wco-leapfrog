#!/usr/bin/env bash
# Build the worst-case-optimal leapfrog-unification join over STOCK upstream MORK, wired into the
# engine's dispatch, then run the demonstration or your own MM2 program.
#
#   ./run.sh                            the demonstration: every case through the stock engine,
#                                       the router, and the wired engine, all byte-compared
#   ./run.sh yourfile.mm2 [args..]      run your MM2 program on the wired engine; extra args pass
#                                       through to `mork run`, e.g. --steps 100 --timing true
#   ./run.sh compare yourfile.mm2 [steps]
#                                       run it on both engines, diff the result spaces, print times
#
# MORK_LEAPFROG=0 pins the stock ProductZipper path, MORK_LEAPFROG=all dispatches every routable
# body; the default dispatches conjunctive bodies with a variable column shared by two factors.
#
# This clones upstream MORK and PathMap at pinned commits and overlays one module
# (kernel/src/zipper_join.rs), one example, a single `pub mod` line, and one reviewable engine
# patch (overlay/space_dispatch.patch: `query_multi_dispatch`, and the space-to-space transform
# calling it). Everything else is upstream's, so the ProductZipper measured against is upstream's.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$here/build"
mkdir -p "$build"

# Resolve the input path before any cd, relative to the caller's directory.
mode=demo
input=""
declare -a pass=()
if [ $# -gt 0 ]; then
  if [ "$1" = compare ]; then
    [ $# -ge 2 ] || { echo "usage: ./run.sh compare yourfile.mm2 [steps]" >&2; exit 2; }
    mode=compare
    input="$(realpath "$2")"
    [ $# -ge 3 ] && pass=(--steps "$3")
  else
    mode=run
    input="$(realpath "$1")"
    shift
    pass=("$@")
  fi
  [ -f "$input" ] || { echo "no such file: $input" >&2; exit 2; }
fi

MORK_URL="https://github.com/trueagi-io/MORK"
MORK_PIN="4a101d14388b8678bef3b377d6d04793f10c1686"
PATHMAP_URL="https://github.com/Adam-Vandervorst/PathMap"
PATHMAP_PIN="5569535069fd571fe66c6c39a366a755cd3ad54e"

clone_pin () {  # url dir pin
  [ -d "$2/.git" ] || git clone "$1" "$2"
  git -C "$2" checkout --quiet "$3"
}

# MORK's Cargo expects PathMap as its sibling ../PathMap, so lay them out side by side.
clone_pin "$PATHMAP_URL" "$build/PathMap" "$PATHMAP_PIN"
clone_pin "$MORK_URL"    "$build/MORK"    "$MORK_PIN"

cp "$here/overlay/zipper_join.rs" "$build/MORK/kernel/src/zipper_join.rs"
grep -q "pub mod zipper_join;" "$build/MORK/kernel/src/lib.rs" \
  || sed -i 's/^pub mod space;/pub mod space;\npub mod zipper_join;/' "$build/MORK/kernel/src/lib.rs"
grep -q "query_multi_dispatch" "$build/MORK/kernel/src/space.rs" \
  || git -C "$build/MORK" apply "$here/overlay/space_dispatch.patch"
mkdir -p "$build/MORK/kernel/examples"
cp "$here/overlay/examples/wco_leapfrog.rs" "$build/MORK/kernel/examples/wco_leapfrog.rs"

# gxhash needs aes+sse2 (target-cpu=native); MORK builds on nightly.
cd "$build/MORK"
export RUSTFLAGS="-C target-cpu=native"

case "$mode" in
  demo)
    exec cargo +nightly run -p mork --release --example wco_leapfrog
    ;;
  run)
    exec cargo +nightly run -p mork --release --bin mork -- run "$input" "${pass[@]}"
    ;;
  compare)
    cargo +nightly build -p mork --release --bin mork
    out_pz="$(mktemp)"; out_lf="$(mktemp)"
    trap 'rm -f "$out_pz" "$out_lf"' EXIT
    MORK_LEAPFROG=0 target/release/mork run "$input" "${pass[@]}" > "$out_pz"
    MORK_LEAPFROG=1 target/release/mork run "$input" "${pass[@]}" > "$out_lf"
    grep '^executing' "$out_pz" | sed 's/^/  stock : /'
    grep '^executing' "$out_lf" | sed 's/^/  wired : /'
    if diff <(sed -n '/^result:/,$p' "$out_pz") <(sed -n '/^result:/,$p' "$out_lf") > /dev/null; then
      echo "  result spaces byte-identical"
    else
      echo "  RESULT SPACES DIFFER:"
      diff <(sed -n '/^result:/,$p' "$out_pz") <(sed -n '/^result:/,$p' "$out_lf") | head -20
      exit 1
    fi
    ;;
esac
