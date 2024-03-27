# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

JPP          ?= ../../scripts/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../scripts/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

TESTS := bin/test_wots
OUT   := $(addsuffix .out, $(TESTS))

# --------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
ASM_FILES     := $(JPP_FILES:.jpp=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)
CHECKCT_FILES := $(JPP_FILES:.jpp=.check)

# --------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)

SOURCES := test_wots.c ../common/notrandombytes.c ../common/print.c

TEST_FLAGS := -DTEST_EXPAND_SEED -DTEST_GEN_CHAIN

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
	cp test_wots.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(TESTS):
bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL=XMSS-SHAKE_20_512 $(TEST_FLAGS) \
	$(SOURCES) $(REF_SOURCES) $< $(LDLIBS)

$(OBJ_FILES):
bin/%.o: bin/%.s
	$(AS) $< -o $@

$(CHECKCT_FILES):
bin/%.check: bin/%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -checkCT -infer $^ > $@

bin/%.out: bin/%
	@./$<

# --------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	rm -fr bin/

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true

# --------------------------------------------------------------------------------------------------

debug:
	@echo $(REF_SOURCES)