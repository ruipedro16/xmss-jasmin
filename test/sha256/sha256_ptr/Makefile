# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../../ref-jasmin/

# --------------------------------------------------------------------------------------------------

default: bin/test_sha256_ptr
run: bin/test_sha256_ptr.out
obj_files: bin/test_sha256_ptr.o
checkct: bin/test_sha256_ptr.check

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/%.s
bin/%.s: %.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../../common ../../common/notrandombytes.c test_sha256.c $< $(LDLIBS)

%.o: %.s
	$(AS) $< -o $@

bin/%.check: %.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -checkCT -infer $^ > $@


bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	rm -fr bin/
