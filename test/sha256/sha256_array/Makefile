# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../../ref-jasmin/

JPP          ?= ../../../scripts/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../../scripts/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

INLEN_LIST ?= 1 31 32 33 63 64 65 95 96 97 127 128 129 135 136 137 159 160 \
161 191 192 193 223 224 225 255 256 257 270 271 272

TLIST := $(INLEN_LIST)

# --------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_sha256_, $(TLIST))
OUT   := $(addsuffix .out, $(TESTS))

GET_INLEN  = $(word 3, $(subst _, ,$*))

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

$(JPP_FILES):
.PRECIOUS: bin/%.jpp
bin/%.jpp: | bin/
	cp test_sha256_array.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@ --task "fn:sha256_array p:INLEN:$(GET_INLEN)"

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jpp | bin/
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(TESTS):
bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../../common ../../common/notrandombytes.c test_sha256_array.c $< $(LDLIBS)

$(OBJ_FILES):
%.o: %.s
	$(AS) $< -o $@

$(CHECKCT_FILES):
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


debug:
	@echo $(ASM_FILES)