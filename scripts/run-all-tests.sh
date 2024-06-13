#!/bin/bash

test_dirs=(
    "wots"
    "xmss"
)

for dir in ${test_dirs[@]}; do
    make -C ../test/$dir clean
    make -C ../test/$dir
    make -C ../test/$dir run
done
