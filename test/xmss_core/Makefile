# -*- Makefile -*-

# ----------------------------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

JPP          ?= ../../scripts/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../scripts/jasmin-preprocessor/preprocessor

# ----------------------------------------------------------------------------------------------------------------------

IMPLS := XMSS-SHAKE_20_512 XMSS-SHA2_10_256
IMPL_STR := $(foreach impl,$(IMPLS),$(shell echo $(impl) | tr '[:upper:]' '[:lower:]'))

SPACE = $(space) $(space)

GET_IMPL = $(subst $(SPACE),_,$(wordlist 4, 6, $(subst _, ,$*)))
GET_IMPL_UPPER_CASE = $(shell echo $(subst $(SPACE),_,$(wordlist 4, 6, $(subst _, ,$*))) | tr '[:lower:]' '[:upper:]')

# ----------------------------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_xmss_core_, $(IMPL_STR))
OUT   := $(addsuffix .out, $(TESTS))

# ----------------------------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
ASM_FILES     := $(JPP_FILES:.jpp=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)
CHECKCT_FILES := $(JPP_FILES:.jpp=.check)

# ----------------------------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)

SOURCES := test_xmss_core.c ../common/notrandombytes.c ../common/print.c

TEST_FLAGS := 

# ----------------------------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)

jpp_files: $(JPP_FILES)
asm_files: $(ASM_FILES)
obj_files: $(OBJ_FILES)
checkct: $(CHECKCT_FILES)

# ----------------------------------------------------------------------------------------------------------------------

$(JPP_FILES):
.PRECIOUS: bin/%.jpp
bin/%.jpp: | bin/
	echo "from XMSS require \"params/params-$(GET_IMPL).jinc\"\n" > $@
	echo "from XMSS require \"core_hash/core_hash_$(GET_IMPL).jtmpl\"\n\n" >> $@
	cat test_xmss_core.jazz  >> $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(TESTS):
bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL=$(GET_IMPL_UPPER_CASE)  $(TEST_FLAGS) \
	$(SOURCES) $(REF_SOURCES) $< $(LDLIBS)

$(OBJ_FILES):
bin/%.o: bin/%.s
	$(AS) $< -o $@

$(CHECKCT_FILES):
bin/%.check: bin/%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) -checkCT -infer $^ > $@

bin/%.out: bin/%
	@./$<

# ----------------------------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	rm -fr bin/

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true

# ----------------------------------------------------------------------------------------------------------------------

debug:
	@echo $(REF_SOURCES)