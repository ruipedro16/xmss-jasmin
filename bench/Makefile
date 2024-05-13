# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

# FIXME: Fix bench_sha2_array

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

# --------------------------------------------------------------------------------------------------

# Optinal flag -DALL_TIMINGS
BENCH_FLAGS ?= 

MIN_MSG_LEN := 1
MAX_MSG_LEN := 5

# --------------------------------------------------------------------------------------------------

bench_sha2: results/bench_sha2_ptr.json results/bench_sha2_array.json
bench_wots: results/results_wots.json
bench_xmss: results/results_xmss.json

SHA2_CSV_FILES := $(addprefix csv/bench_sha2_array_,$(addsuffix .csv,$(shell seq 1 10)))
bench_sha2_array: $(SHA2_CSV_FILES)

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(filter-out ../submodules/xmss-reference/xmss_core_fast.c \
                            ../submodules/xmss-reference/randombytes.c \
							../submodules/xmss-reference/randombytes.h, $(wildcard ../submodules/xmss-reference/*.c))

BENCH_SOURCES := common/notrandombytes.c 

# --------------------------------------------------------------------------------------------------

bin/wots.s: bin/
	$(MAKE) -C ../test/wots clean asm_files
	cp ../test/wots/bin/test_wots_xmss-sha2_10_256.s $@

bin/xmss.s: bin/
	$(MAKE) -C ../test/xmss/ clean asm_files
	cp ../test/xmss/bin/test_xmss_xmss-sha2_10_256.s $@

bin/sha2_ptr.s: bin/
	$(MAKE) -C ../test/sha256/sha256_in_ptr/ asm_files
	cp ../test/sha256/sha256_in_ptr/bin/test_sha256_in_ptr.s $@

bin/sha2_array_%.s: bin/
	$(MAKE) -C ../test/sha256/sha256_array/ bin/test_sha256_$*.s
	cp ../test/sha256/sha256_array/bin/test_sha256_$*.s $@

# --------------------------------------------------------------------------------------------------

bin/bench_wots: bin/wots.s
	$(CC) $(CFLAGS) -o $@ -I./common -I../submodules/xmss-reference \
	-DIMPL=XMSS-SHAKE_20_512 -DMAX_MSG_LEN=$(MAX_MSG_LEN) -DMIN_MSG_LEN=$(MIN_MSG_LEN) \
	$(REF_SOURCES) $(BENCH_SOURCES) $(BENCH_FLAGS) bench_wots.c $< $(LDLIBS)

bin/bench_xmss: bin/xmss.s
	$(CC) $(CFLAGS) -o $@ -I./common -I../submodules/xmss-reference \
	-DIMPL=XMSS-SHAKE_20_512 $(REF_SOURCES) $(BENCH_SOURCES) $(BENCH_FLAGS) \
	bench_xmss.c $< $(LDLIBS)

bin/bench_sha2_ptr: bin/sha2_ptr.s
	$(CC) $(CFLAGS) -o $@ -I./common $(BENCH_FLAGS) bench_sha2_ptr.c $< $(LDLIBS)

bin/bench_sha2_array_%: bin/sha2_array_%.s
	$(CC) $(CFLAGS) -o $@ -I./common $(BENCH_FLAGS) -DINLEN=$* bench_sha2_array.c $< $(LDLIBS)

# --------------------------------------------------------------------------------------------------

csv/bench_wots.csv: bin/bench_wots | csv/
	./$<

csv/bench_xmss.csv: bin/bench_xmss | csv/
	./$<

csv/bench_sha2_ptr.csv: bin/bench_sha2_ptr | csv/
	./$<

csv/bench_sha2_array_%.csv: bin/bench_sha2_array_% | csv/
	./$<

# --------------------------------------------------------------------------------------------------

results/results_wots.json: csv/bench_wots.csv | results/
	./print_results.py -in $< -out $@

results/results_xmss.json: csv/bench_xmss.csv | results/
	./print_results.py -in $< -out $@

# TODO: Add for SHA2

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

csv/:
	mkdir -p $@

results/:
	mkdir -p $@

# --------------------------------------------------------------------------------------------------

clean:
	$(RM) -rf bin/

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true

distclean:
	$(RM) -rf csv/
