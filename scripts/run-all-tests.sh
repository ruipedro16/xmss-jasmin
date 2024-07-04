#!/bin/bash

test_dirs=(
    "hash_address"
    "stdlib"
    "sha256/sha256_array"
    "sha256/sha256_in_ptr"
    "hash"
    "wots"
    "xmss"
)

for dir in ${test_dirs[@]}; do
    make     -C ../test/$dir clean
    make -j8 -C ../test/$dir
    make -j8 -C ../test/$dir run
done
