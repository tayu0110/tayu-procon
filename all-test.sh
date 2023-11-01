#!/bin/bash

for dir in \
  "bitset" "complex" "convolution" "fenwick-tree" "flow" "geometry" \
  "graph" "iolib" "math" "matrix" "mincost-flow" "modint" "numeric" \
  "polynomial" "rational" "segtree" "simple-rand" "simple-test" "string" "suffix-array" \
  "trie" "two-sat" "unionfind" "utility" "wavelet-matrix"; do
  cd "${dir}" || exit
  echo "${dir} is testing..."
  cargo test
  cargo test --doc
  cd ../
done
