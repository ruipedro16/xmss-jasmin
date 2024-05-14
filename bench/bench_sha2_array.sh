#!/bin/bash

# FIXME: TODO: Remove this script & fix Makefile

# Check if the number of arguments is correct
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <min_inlen> <max_inlen>"
    exit 1
fi

# Check if both arguments are integers
if ! [[ "$1" =~ ^[0-9]+$ ]] || ! [[ "$2" =~ ^[0-9]+$ ]]; then
    echo "Both arguments must be integers."
    exit 1
fi

# Check if both arguments are non-negative
if [ "$1" -lt 0 ] || [ "$2" -lt 0 ]; then
    echo "Both arguments must be non-negative integers."
    exit 1
fi

# Check if max is greater than min
if [ "$2" -le "$1" ]; then
    echo "max_inlen must be greater than min_inlen."
    exit 1
fi

# Set default values
: "${CC:=cc}"
: "${CFLAGS:= -Wall -O3 -Wextra -Wpedantic}"
: "${LDLIBS:=-lcrypto}"

rm -rf csv/bench_sha2_array.csv
mkdir -p bin/ csv/

make -C ../test/sha256/sha256_array/ clean

# Compile Jasmin
for ((i = $1; i <= $2; i++)); do
    make -C ../test/sha256/sha256_array/ bin/test_sha256_$i.s
    cp ../test/sha256/sha256_array/bin/test_sha256_$i.s bin/
done

# Compile code for benchmarks
for ((i = $1; i <= $2; i++)); do
    $CC $CFLAGS -o bin/bench_sha2_array_$i -I./common -DINLEN=$i bench_sha2_array.c bin/test_sha256_$i.s $LDLIBS
done

# Run benchmarks
for ((i = $1; i <= $2; i++)); do
    ./bin/bench_sha2_array_$i
done
