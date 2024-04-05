#!/bin/bash

dirs=(
    "stdlib"
    "fips202/shake256_ptr" 
    "fips202/shake256_array"
    "fips202/shake256_in_ptr"
    "hash_address" 
    "hash_core"
    "hash"
    "wots"
    "xmss_commons"
    # "xmss_core"
    # "xmss"
)

for dir in "${dirs[@]}"; do
    echo "Testing $dir"
    make -C $dir clean   || { echo "Failed to run make clean in $dir"; exit 1; }
    make -C $dir -j8     || { echo "Failed to run make in $dir"; exit 1; }
    make -C $dir -j8 run || { echo "Failed to run make run in $dir"; exit 1; }
done
