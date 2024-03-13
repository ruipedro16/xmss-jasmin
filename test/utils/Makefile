# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic

JASMIN   ?= jasminc
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/

JPP          ?= ../../scripts/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../scripts/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

INLEN_LIST  = 1 2 3 4 5 6 7 8
OUTLEN_LIST = 1 2 3 4 5 6 7 8
LEN_LIST    = $(shell seq 1 100)

TLIST := $(foreach I,$(INLEN_LIST),$(foreach O,$(OUTLEN_LIST),$(foreach L,$(LEN_LIST),$(I)_$(O)_$(L))))

# --------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_utils_, $(TLIST))
OUT   := $(addsuffix .out, $(TESTS))

GET_INLEN  = $(word 1, $(subst _, ,$*))
GET_OUTLEN = $(word 2, $(subst _, ,$*))
GET_LEN    = $(word 3, $(subst _, ,$*))

# --------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
ASM_FILES     := $(JPP_FILES:.jpp=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)
CHECKCT_FILES := $(JPP_FILES:.jpp=.check)

# --------------------------------------------------------------------------------------------------

SOURCES := test_utils.c ../../xmss-reference/utils.c \
           ../common/notrandombytes.c ../common/print.c

# --------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)

jpp_files: $(JPP_FILES)
asm_files: $(ASM_FILES)
obj_files: $(OBJ_FILES)
checkct: $(CHECKCT_FILES)

# --------------------------------------------------------------------------------------------------

$(JPP_FILES):
.PRECIOUS: bin/test_utils_%.jpp
bin/test_utils_%.jpp: | bin/
	cp test_utils.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@ --task "fn:ull_to_bytes_jazz p:OUTLEN:$(GET_OUTLEN)" \
	"fn:bytes_to_ull_jazz p:INLEN:$(GET_INLEN)" "fn:memset_jazz p:LEN:$(GET_LEN)"

$(ASM_FILES):
.PRECIOUS: bin/test_utils_%.s
bin/test_utils_%.s: bin/test_utils_%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(TESTS):
bin/test_utils_%: bin/test_utils_%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../../xmss-reference/ \
	-DOUTLEN=$(GET_OUTLEN) -DINLEN=$(GET_INLEN) -DLEN=$(GET_LEN) \
	$(SOURCES) $<

$(OBJ_FILES):
bin/test_utils_%.o: bin/test_utils_%.s
	$(AS) $< -o $@

$(CHECKCT_FILES):
bin/test_utils_%.check: bin/test_utils_%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -checkCT -infer $^ > $@

bin/test_utils_%.out: bin/test_utils_%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	rm -fr bin/
