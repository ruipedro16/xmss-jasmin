#!/usr/bin/env bash

set -e

single_tree_impls=("XMSS-SHA2_10_256") # The parameters are different for "XMSS-SHA2_10_192"
multi_tree_impls=("XMSSMT-SHA2_20/2_256" "XMSSMT-SHA2_20/4_256")

all_impls=("${single_tree_impls[@]}" "${multi_tree_impls[@]}")

for impl in "${all_impls[@]}"; do
    make clean run IMPL="$impl"
done