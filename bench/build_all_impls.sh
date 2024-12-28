#!/usr/bin/env bash

set -e

single_tree_impls=("XMSS-SHA2_10_256") # The parameters are different for "XMSS-SHA2_10_192"
multi_tree_impls=("XMSSMT-SHA2_20/2_256" "XMSSMT-SHA2_20/4_256")

all_impls=("${single_tree_impls[@]}" "${multi_tree_impls[@]}")

BENCH_DIR=$(pwd)
TEST_DIR=$(cd ../test/xmss && pwd)

mkdir -p asm/

cd $TEST_DIR

for impl in "${all_impls[@]}"; do
    make clean && make asm_files IMPL="$impl"
    cp bin/*.s $BENCH_DIR/asm/
done

cd $BENCH_DIR/asm/

find . -type f -name 'test_xmss_*' -exec bash -c 'mv "$0" "${0/test_xmss_/}"' {} \;

