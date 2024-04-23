# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../../ref-jasmin/

JPP          ?= ../../../submodules/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../../submodules/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

LEN_LIST ?= 1 31 32 33 63 64 65 95 96 97 127 128 129 135 136 137 159 160 \
161 191 192 193 223 224 225 255 256 257 270 271 272

TLIST := $(foreach O,$(LEN_LIST), $(foreach I,$(LEN_LIST), $(O)_$(I)))

# --------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_fips202_, $(TLIST))
OUT   := $(addsuffix .out, $(TESTS))

GET_OUTLEN  = $(word 3, $(subst _, ,$*))
GET_INLEN   = $(word 4, $(subst _, ,$*))

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
checkct: $(CHECKCT_FILES)

# --------------------------------------------------------------------------------------------------

SOURCES := test_shake256_array.c ../../fips202.c \
           ../../common/notrandombytes.c ../../common/print.c

# --------------------------------------------------------------------------------------------------

$(JPP_FILES):
.PRECIOUS: bin/%.jpp
bin/%.jpp: | bin/
	cp test_shake256_array.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@ --task "fn:shake256  p:OUTLEN:$(GET_OUTLEN) \
	p:INLEN:$(GET_INLEN)"

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jpp
	$(JASMIN) $(JFLAGS) $< -o $@

$(TESTS):
bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -DOUTLEN=$(GET_OUTLEN) -DINLEN=$(GET_INLEN) \
	-I../../common -I../../ $(SOURCES) $<

$(OBJ_FILES):
bin/%.o: bin/%.s
	$(AS) $< -o $@

$(CHECKCT_FILES):
bin/%.check: bin/%.jpp
	$(JAZZCT) --infer $^ > $@

bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	rm -fr bin/

# --------------------------------------------------------------------------------------------------

debug:
	@echo $(TESTS)