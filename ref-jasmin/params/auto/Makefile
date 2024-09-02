# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(filter-out %xmss_core_fast.c, $(wildcard ../../../submodules/xmss-reference/*.c))

# --------------------------------------------------------------------------------------------------

default: bin/gen_params
run: bin/gen_params.out

# --------------------------------------------------------------------------------------------------

bin/gen_params: | bin/
	$(CC) $(CFLAGS) -o $@ -I../../../submodules/xmss-reference/ gen_params.c $(REF_SOURCES) $(LDLIBS)

bin/gen_params.out: bin/gen_params
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/

distclean:
	find ../ -type f -name 'params-*' -delete
