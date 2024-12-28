# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

# --------------------------------------------------------------------------------------------------

ASM_FILES := asm/xmssmt-sha2_20_2_256.s
BIN       := bin/bench_xmssmt-sha2_20_2_256
OUT       := $(addsuffix .out,$(BIN))

SOURCES :=  ../submodules/xmss-reference/fips202.c \
			../submodules/xmss-reference/hash_address.c \
			../submodules/xmss-reference/hash.c \
			../submodules/xmss-reference/params.c \
			../submodules/xmss-reference/utils.c \
			../submodules/xmss-reference/wots.c \
			../submodules/xmss-reference/xmss_commons.c \
			../submodules/xmss-reference/xmss_core.c \
			../submodules/xmss-reference/xmss.c

RUNS ?= 1

# --------------------------------------------------------------------------------------------------

default: $(BIN)
all: default
run: $(OUT)

# --------------------------------------------------------------------------------------------------

bin/bench_xmssmt-sha2_20_2_256: asm/xmssmt-sha2_20_2_256.s | csv/ bin/
	$(CC) $(CFLAGS) -o $@ \
	bench.c -I../submodules/xmss-reference/ -I./common/ \
	common/notrandombytes.c \
	$< $(SOURCES) -DRUNS=$(RUNS) $(LDLIBS)

bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

csv/:
	mkdir -p $@

bin/:
	mkdir -p $@

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	-$(RM) -r $(BIN)

# --------------------------------------------------------------------------------------------------
