# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/

JPP          ?= ../../submodules/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../submodules/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

INLEN_LIST ?= 1 31 32 33 63 64 65 95 96 97 127 128 129 135 136 137 159 160 \
161 191 192 193 223 224 225 255 256 257 270 271 272

TLIST := $(INLEN_LIST)

# --------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_core_hash_, $(TLIST))
OUT   := $(addsuffix .out, $(TESTS))

GET_INLEN   = $(word 4, $(subst _, ,$*))

# --------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
ASM_FILES     := $(JPP_FILES:.jpp=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)

CHECK_CT  := $(JPP_FILES:.jpp=.check_ct)
CHECK_SCT := $(JPP_FILES:.jpp=.check_sct)

# --------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)

jpp_files: $(JPP_FILES)
asm_files: $(ASM_FILES)
obj_files: $(OBJ_FILES)

ct: $(CHECK_CT)
sct: $(CHECK_SCT)

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)

SOURCES := test_core_hash.c ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

$(JPP_FILES):
.PRECIOUS: bin/%.jpp
bin/%.jpp: | bin/
	cp test_core_hash.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@ --task "fn:core_hash p:INLEN:$(GET_INLEN)"

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jpp
	$(JASMIN) $(JFLAGS) $< -o $@

$(TESTS):
bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -DIMPL=XMSS-SHAKE_20_512 -DINLEN=$(GET_INLEN) -I../common -I../ \
	$(REF_SOURCES) $(SOURCES) $< $(LDLIBS)

$(OBJ_FILES):
bin/%.o: bin/%.s
	$(AS) $< -o $@

$(CHECK_CT):
bin/%.check_ct: bin/%.jpp | bin/
	$(JAZZCT) --infer $^

$(CHECK_SCT):
bin/%.check_sct: bin/%.jpp | bin/
	$(JAZZCT) --sct --infer $^

bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/
