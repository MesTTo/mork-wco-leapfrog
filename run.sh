#!/usr/bin/env bash
# Build and run the worst-case-optimal leapfrog-unification join over STOCK upstream MORK.
#
# This clones upstream MORK and PathMap at pinned commits, overlays one module
# (kernel/src/zipper_join.rs) plus one example and a single `pub mod` line, and runs the
# demonstration. Nothing else in MORK changes, so the ProductZipper it is measured against is
# exactly upstream's.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$here/build"
mkdir -p "$build"

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
mkdir -p "$build/MORK/kernel/examples"
cp "$here/overlay/examples/wco_leapfrog.rs" "$build/MORK/kernel/examples/wco_leapfrog.rs"

# gxhash needs aes+sse2 (target-cpu=native); MORK builds on nightly.
cd "$build/MORK"
RUSTFLAGS="-C target-cpu=native" cargo +nightly run -p mork --release --example wco_leapfrog "$@"
