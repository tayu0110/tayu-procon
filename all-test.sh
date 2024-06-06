#!/bin/bash

for dir in \
  "balanced-bst" "bitset" "complex" "convolution" "cpgraph" "cpio" "ds" "fenwick-tree" "flow" "geometry" \
  "graph" "iolib" "math" "matrix" "mincost-flow" "modint" "number-theoretic-transform" "numeric" \
  "polynomial" "rational" "segtree" "simple-rand" "string" \
  "trie" "two-sat" "unionfind" "utility"; do
  cd "${dir}" || exit
  echo "${dir} is testing..."
  cargo test --all-features
  cargo test --release --all-features
  cd ../
done
