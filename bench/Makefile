# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

# --------------------------------------------------------------------------------------------------

# Optinal flag -DALL_TIMINGS
BENCH_FLAGS ?= 

# --------------------------------------------------------------------------------------------------

BIN_FILES := bin/bench_wots bin/bench_xmss
ASM_FILES := bin/wots.s bin/xmss.s
CSV_FILES := $(patsubst bin/%,csv/%.csv,$(BIN_FILES))

default: $(BIN_FILES)
run: bench_wots bench_xmss
asm_files: $(ASM_FILES)

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(filter-out ../submodules/xmss-reference/xmss_core_fast.c \
                            ../submodules/xmss-reference/randombytes.c \
							../submodules/xmss-reference/randombytes.h, $(wildcard ../submodules/xmss-reference/*.c))

BENCH_SOURCES := common/notrandombytes.c common/cpucycles.c 

# --------------------------------------------------------------------------------------------------

bin/wots.s: bin/
	make -C ../test/wots clean asm_files
	cp ../test/wots/bin/test_wots.s $@

bin/xmss.s: bin/
	make -C ../test/xmss/ clean asm_files
	cp ../test/xmss/bin/test_xmss_xmss-sha2_10_256.s $@

# --------------------------------------------------------------------------------------------------

bin/bench_wots: bin/wots.s
	$(CC) $(CFLAGS) -o $@ -I./common -I../submodules/xmss-reference \
	-DIMPL=XMSS-SHAKE_20_512 $(REF_SOURCES) $(BENCH_SOURCES) $(BENCH_FLAGS) \
	bench_wots.c $< $(LDLIBS)

bin/bench_xmss: bin/xmss.s
	$(CC) $(CFLAGS) -o $@ -I./common -I../submodules/xmss-reference \
	-DIMPL=XMSS-SHAKE_20_512 $(REF_SOURCES) $(BENCH_SOURCES) $(BENCH_FLAGS) \
	bench_xmss.c $< $(LDLIBS)

bench_wots: bin/bench_wots | csv/
	./$<

bench_xmss: bin/bench_xmss | csv/
	./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

csv/:
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