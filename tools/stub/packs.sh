#!/bin/sh
# The stub server's packs, into $1 (default build/stub): good, slow (images answer late), broken
# (an image missing), badjson, and big (100 faces, for the bench). `missing` is absent on purpose.
set -eu
out=${1:-build/stub}
draw="swift tools/packs/draw.swift"
rm -rf "$out"
mkdir -p "$out"
$draw numbered "$out/good" 12 Numbers
$draw numbered "$out/slow" 12 Slow
$draw numbered "$out/broken" 12 Broken
rm "$out/broken/face-007.png"
mkdir -p "$out/badjson"
printf '{"name": "Bad", "faces": [' > "$out/badjson/pack.json"
$draw numbered "$out/big" 100 "Hundred"
