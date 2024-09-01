# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/

JPP ?= ../../submodules/jasmin-preprocessor/jpp

# --------------------------------------------------------------------------------------------------

SOURCES := test_hash_address.c ../hash_address.c ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

default: bin/test_hash_address
run: bin/test_hash_address.out

asm_files: bin/test_hash_address.s
obj_files: bin/test_hash_address.o

ct:  bin/test_hash_address.check_ct
sct: bin/test_hash_address.check_sct

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/test_hash_address.s
bin/test_hash_address.s: test_hash_address.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

bin/test_hash_address: bin/test_hash_address.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ $(SOURCES) $<

%.o: %.s
	$(AS) $< -o $@

.PHONY: bin/test_hash_address.check_ct bin/test_hash_address.check_sct
bin/test_hash_address.check_ct: test_hash_address.jazz | bin/
	$(JPP) $(JINCLUDE) -in $< -out $@
	$(JAZZCT) --infer $@
	-$(RM) $@

bin/test_hash_address.check_sct: test_hash_address.jazz | bin/
	$(JPP) $(JINCLUDE) -in $< -out $@
	$(JAZZCT) --sct --infer $@
	-$(RM) $@

bin/test_hash_address.out: bin/test_hash_address
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/
