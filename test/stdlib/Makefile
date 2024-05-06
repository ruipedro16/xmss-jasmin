# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

JPP          ?= ../../submodules/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../submodules/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

INLEN_LIST := $(shell seq 1 100)
TLIST := $(foreach I,$(INLEN_LIST),$(I))

# --------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_utils_, $(TLIST)) bin/test_conditions
OUT   := $(addsuffix .out, $(TESTS))

# --------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
ASM_FILES     := $(JPP_FILES:.jpp=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)

CHECK_CT  := $(JPP_FILES:.jpp=.check_ct)
CHECK_SCT := $(JPP_FILES:.jpp=.check_sct)

# --------------------------------------------------------------------------------------------------

SOURCES := test_utils.c ../common/notrandombytes.c ../common/print.c ../utils.c

# --------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)

jpp_files: $(JPP_FILES)
asm_files: $(ASM_FILES)
obj_files: $(OBJ_FILES)

ct: $(CHECK_CT)
sct: $(CHECK_SCT)

# --------------------------------------------------------------------------------------------------

$(JPP_FILES):
.PRECIOUS: bin/%.jpp
bin/test_utils_%.jpp: | bin/
	cp test_utils.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@ --task "fn:bytes_to_ull_jazz p:INLEN:$*" \
	"fn:memset_zero_u8_jazz p:INLEN:$*"

bin/test_conditions.jpp: bin/
	cp test_conditions.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(TESTS):
bin/test_utils_%: bin/test_utils_%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DINLEN=$* $(SOURCES) $<

bin/test_conditions: bin/test_conditions.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ test_conditions.c ../common/notrandombytes.c $<

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
	$(RM) -fr bin/
