#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [ "$#" -gt 0 ]; then
  DIR_NAME="$1"
else
  DIR_NAME="../jazz"
fi

if [ -d "$DIR_NAME" ]; then
  rm -rf "$DIR_NAME"/*
fi

rm -rf "$SCRIPT_DIR/../test/xmss/bin"

make -C "$SCRIPT_DIR/../test/xmss" -j8  asm_files

mkdir -p "$DIR_NAME"

mv "$SCRIPT_DIR/../test/xmss/bin/"*.s "$DIR_NAME"

for file in "$DIR_NAME"/*.s; do
  if [[ -f $file ]]; then
    mv "$file" "${file/test_/}"
  fi
done
