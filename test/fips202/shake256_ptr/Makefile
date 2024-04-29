# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../../ref-jasmin/

JPP ?= ../../../submodules/jasmin-preprocessor/jpp

# --------------------------------------------------------------------------------------------------

SOURCES := test_shake256_ptr.c ../../fips202.c

# --------------------------------------------------------------------------------------------------

default: bin/test_shake256_ptr
run: bin/test_shake256_ptr.out

asm_files: bin/test_shake256_ptr.s
obj_files: bin/test_shake256_ptr.o

ct: bin/test_shake256_ptr.check_ct
sct: bin/test_shake256_ptr.check_sct

# --------------------------------------------------------------------------------------------------

.PRECIOUS: bin/test_shake256_ptr.s
bin/test_shake256_ptr.s: test_shake256_ptr.jazz | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

bin/test_shake256_ptr: bin/test_shake256_ptr.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../../common -I../../ $(SOURCES) $<

%.o: %.s
	$(AS) $< -o $@

bin/test_shake256_ptr.check_ct: test_shake256_ptr.jazz | bin/
	$(JPP) $(JINCLUDE) -in $< -out $@
	$(JAZZCT) --infer $@
	$(RM) $@

bin/test_shake256_ptr.check_sct: test_shake256_ptr.jazz | bin/
	$(JPP) $(JINCLUDE) -in $< -out $@
	$(JAZZCT) --sct --infer $@
	$(RM) $@


bin/test_shake256_ptr.out: bin/test_shake256_ptr
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	$(RM) -fr bin/
