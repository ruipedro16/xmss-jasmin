# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

# --------------------------------------------------------------------------------------------------

IMPL_LIST := XMSS-SHAKE_20_512 XMSS-SHA2_10_256
SPACE = $(space) $(space)
GET_IMPL  = $(subst $(SPACE),_,$(wordlist 1, 3, $(subst _, ,$*)))


# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(filter-out %xmss_core_fast.c, $(wildcard ../../xmss-reference/*.c))

# --------------------------------------------------------------------------------------------------

BIN := $(addprefix bin/gen_params_, $(IMPL_LIST))
OUT := $(addsuffix .out, $(BIN))

default: $(BIN)
run: $(OUT)

# --------------------------------------------------------------------------------------------------

bin/gen_params_%: | bin/
	$(CC) $(CFLAGS) -o $@ -I../../xmss-reference/ gen_params.c \
	-DIMPL=$(GET_IMPL) $(REF_SOURCES) $(LDLIBS)

bin/gen_params_%.out: bin/gen_params_% | ../param/
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

../param/:
	mkdir -p $@

.PHONY: clean
clean:
	rm -rf bin/

.PHONY: distclean
distclean:
	rm -rf ../param/
	
