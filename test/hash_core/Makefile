# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/

JPP          ?= ../../submodules/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../submodules/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(filter-out %xmss_core_fast.c,$(filter-out %randombytes.c, $(wildcard ../../xmss-reference/*.c)))

SOURCES := test_hash_core.c ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

INLEN_LIST  = 1 2 8 16 32 64 128 256 512 1024
OUTLEN_LIST = 1 2 8 16 32 64 128 256 512 1024

TLIST := $(foreach I,$(INLEN_LIST),$(foreach O,$(OUTLEN_LIST),$(I)_$(O)))

# --------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_hash_core_, $(TLIST))
OUT   := $(addsuffix .out, $(TESTS))

GET_INLEN  = $(word 2, $(subst _, ,$*))
GET_OUTLEN = $(word 3, $(subst _, ,$*))

# --------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
ASM_FILES     := $(JPP_FILES:.jpp=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)
CHECKCT_FILES := $(JPP_FILES:.jpp=.check)

# --------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)

jpp_files: $(JPP_FILES)
asm_files: $(ASM_FILES)
obj_files: $(OBJ_FILES)

# --------------------------------------------------------------------------------------------------

$(JPP_FILES):
.PRECIOUS: bin/test_hash_core_%.jpp
bin/test_hash_core_%.jpp: | bin/
	cp test_hash_core.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@ \
	--task "fn:core_hash_shake256_out_64_jazz p:INLEN:$(GET_INLEN)"

$(ASM_FILES):
.PRECIOUS: bin/test_hash_core_%.s
bin/test_hash_core_%.s: bin/test_hash_core_%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(TESTS):
bin/test_hash_%: bin/test_hash_core_%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../../xmss-reference/ \
	-DINLEN=$(GET_INLEN) $(SOURCES) $(REF_SOURCES) $< $(LDLIBS)

$(OBJ_FILES):
bin/test_hash_core_%.o: bin/test_hash_core_%.s
	$(AS) $< -o $@


bin/test_hash_core_%.out: bin/test_hash_core_%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	$(RM) -fr bin/
