# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

default: check_empty

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

# --------------------------------------------------------------------------------------------------

ASM_FILES := $(wildcard asm/*.s)
BIN       := $(patsubst asm/%.s,bin/bench%,$(ASM_FILES))
OUT       := $(addsuffix .out,$(BIN))

# --------------------------------------------------------------------------------------------------

check_empty:
ifeq ($(strip $(ASM_FILES)),)
	@echo "No ASM files found in asm/. Running ../scripts/jazz.sh asm/"
	@../scripts/jazz.sh asm/
else
	@echo "ASM files found: $(ASM_FILES)"
endif

# --------------------------------------------------------------------------------------------------

csv/:
	mkdir -p $@

bin/:
	mkdir -p $@

asm/:
	mkdir -p $@

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	-$(RM) -r asm/ bin/