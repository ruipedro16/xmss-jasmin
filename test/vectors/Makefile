# -*- Makefile -*-

# ----------------------------------------------------------------------------------------------------------------------

# TODO: Adapt to work with any xmss[mt] implementation

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

# ----------------------------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)

# ----------------------------------------------------------------------------------------------------------------------

default: bin/gen_vectors bin/test_vectors
run: bin/gen_vectors.out bin/test_vectors.out

# ----------------------------------------------------------------------------------------------------------------------

bin/gen_vectors: | bin/ vectors/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL=XMSS-SHA2_10_256 ../common/notrandombytes.c ../common/print.c \
	$(REF_SOURCES) gen_vectors.c $(LDLIBS)

bin/gen_vectors.out: bin/gen_vectors
	@./$< > vectors/vectors.txt

bin/test_xmss_core_xmss-sha2_10_256.s: | bin/
	$(MAKE) -C ../xmss_core/ bin/test_xmss_core_xmss-sha2_10_256.s
	cp ../xmss_core/bin/test_xmss_core_xmss-sha2_10_256.s $@

bin/test_vectors: bin/test_xmss_core_xmss-sha2_10_256.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL=XMSS-SHA2_10_256 ../common/notrandombytes.c \
	$(REF_SOURCES) test_vectors.c $< $(LDLIBS)

bin/test_vectors.out: bin/test_vectors
	@./$<

# ----------------------------------------------------------------------------------------------------------------------

vectors/:
	mkdir -p $@

bin/:
	mkdir -p $@

# ----------------------------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	$(RM) -fr bin/ vectors/

# ----------------------------------------------------------------------------------------------------------------------
debug:
	@echo $(TESTS)