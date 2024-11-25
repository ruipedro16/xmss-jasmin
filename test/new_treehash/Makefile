# -*- Makefile -*-

CC     ?= clang
CFLAGS ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS := -lcrypto 

TEST_FLAGS := -DTEST_TREEHASH_JASMIN -DTEST_BUILDAUTHPATH_JASMIN -DTEST_TREESIG_JASMIN 

TESTS = bin/test_treehash
OUT   = bin/test_treehash.out

default: $(TESTS)
run: $(OUT)

.PRECIOUS: $(TESTS)

REF_SOURCES := $(wildcard ../*.c) new_xmss.c test_new_version.c
SOURCES := ../common/notrandombytes.c ../common/print.c

$(TESTS):
bin/test_treehash: bin/
	$(CC) $(CFLAGS) $(TEST_FLAGS) -o $@ -I../common -I../ -I. $(SOURCES) $(REF_SOURCES) $(LDLIBS)

bin/%.out: bin/%
	@./$<

# ----------------------------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

clean:
	-$(RM) -r bin/
	find . -name '*.txt' -delete
