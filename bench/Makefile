# -*- Makefile -*-

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

default: bin/bench_wots bin/bench_xmss
bench_wots: results/results_wots.json
bench_xmss: results/results_xmss.json

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(filter-out ../submodules/xmss-reference/xmss_core_fast.c \
                            ../submodules/xmss-reference/randombytes.c \
							../submodules/xmss-reference/randombytes.h, $(wildcard ../submodules/xmss-reference/*.c))

BENCH_SOURCES := common/notrandombytes.c 

# --------------------------------------------------------------------------------------------------

bin/wots.s: bin/
	make -C ../test/wots clean asm_files
	cp ../test/wots/bin/test_wots_xmss-sha2_10_256.s $@

bin/xmss.s: bin/
	make -C ../test/xmss/ clean asm_files
	cp ../test/xmss/bin/test_xmss_xmss-sha2_10_256.s $@

# --------------------------------------------------------------------------------------------------

bin/bench_wots: bin/wots.s
	$(CC) $(CFLAGS) -o $@ -I./common -I../submodules/xmss-reference \
	-DIMPL=XMSS-SHAKE_20_512 -DMAX_MSG_LEN=$(MAX_MSG_LEN) -DMIN_MSG_LEN=$(MIN_MSG_LEN) \
	$(REF_SOURCES) $(BENCH_SOURCES) $(BENCH_FLAGS) bench_wots.c $< $(LDLIBS)

bin/bench_xmss: bin/xmss.s
	$(CC) $(CFLAGS) -o $@ -I./common -I../submodules/xmss-reference \
	-DIMPL=XMSS-SHAKE_20_512 $(REF_SOURCES) $(BENCH_SOURCES) $(BENCH_FLAGS) \
	bench_xmss.c $< $(LDLIBS)

# --------------------------------------------------------------------------------------------------

csv/bench_wots.csv: bin/bench_wots | csv/
	./$<

csv/bench_xmss.csv: bin/bench_xmss | csv/
	./$<

# --------------------------------------------------------------------------------------------------

results/results_wots.json: csv/bench_wots.csv | results/
	./print_results.py -in $< -out $@

results/results_xmss.json: csv/bench_xmss.csv | results/
	./print_results.py -in $< -out $@

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

csv/:
	mkdir -p $@

results/:
	mkdir -p $@

# --------------------------------------------------------------------------------------------------

clean:
	rm -rf bin/

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true

distclean:
	rm -rf csv/

# --------------------------------------------------------------------------------------------------

debug:
	@echo $(CSV_FILES)
	@echo $(REF_SOURCES)