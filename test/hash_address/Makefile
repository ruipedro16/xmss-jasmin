# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/

# --------------------------------------------------------------------------------------------------

SOURCES := test_hash_address.c ../hash_address.c ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

default: bin/test_hash_address
run: bin/test_hash_address.out

asm_files: bin/test_hash_address.s
obj_files: bin/test_hash_address.o
checkct: bin/test_hash_address.check

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/test_hash_address.s
bin/test_hash_address.s: test_hash_address.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

bin/test_hash_address: bin/test_hash_address.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ $(SOURCES) $<

%.o: %.s
	$(AS) $< -o $@

bin/test_hash_address.check: test_hash_address.jazz | bin/
	$(JAZZCT) --infer $^ > $@


bin/test_hash_address.out: bin/test_hash_address
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	rm -fr bin/
