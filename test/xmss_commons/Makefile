# -*- Makefile -*-

# ----------------------------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto

JASMIN   ?= jasminc
JAZZCT   ?= jazzct
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../../ref-jasmin/ -I Stdlib:../../ref-jasmin/stdlib

JPP          ?= ../../submodules/jasmin-preprocessor/jpp
PREPROCESSOR ?= ../../submodules/jasmin-preprocessor/preprocessor

# ----------------------------------------------------------------------------------------------------------------------

IMPLS := XMSS-SHA2_10_256
IMPL_STR := $(foreach impl,$(IMPLS),$(shell echo $(impl) | tr '[:upper:]' '[:lower:]'))

SPACE = $(space) $(space)

GET_IMPL = $(subst $(SPACE),_,$(wordlist 4, 6, $(subst _, ,$*)))
GET_IMPL_UPPER_CASE = $(shell echo $(subst $(SPACE),_,$(wordlist 4, 6, $(subst _, ,$*))) | tr '[:lower:]' '[:upper:]')

# ----------------------------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_xmss_commons_, $(IMPL_STR))
OUT   := $(addsuffix .out, $(TESTS))

# ----------------------------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
ASM_FILES     := $(JPP_FILES:.jpp=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)

CHECK_CT  := $(JPP_FILES:.jpp=.check_ct)
CHECK_SCT := $(JPP_FILES:.jpp=.check_sct)

# ----------------------------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)

SOURCES := test_xmss_commons.c ../common/notrandombytes.c ../common/print.c

TEST_FLAGS := -DTEST_LTREE -DTEST_GEN_LEAF_WOTS -DTEST_COMPUTE_ROOT -DTEST_XMSS_CORE_SIGN_OPEN -DDEBUG

# ----------------------------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)

jpp_files: $(JPP_FILES)
asm_files: $(ASM_FILES)
obj_files: $(OBJ_FILES)

ct: $(CHECK_CT)
sct: $(CHECK_SCT)

# ----------------------------------------------------------------------------------------------------------------------

$(JPP_FILES):
.PRECIOUS: bin/%.jpp
bin/%.jpp: | bin/
	echo "from XMSS require \"params/params-$(GET_IMPL).jinc\"\n" > $@
	echo "from XMSS require \"core_hash/core_hash_$(GET_IMPL).jtmpl\"\n\n" >> $@
	cat test_xmss_commons.jazz  >> $@
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

$(CHECK_CT):
bin/%.check_ct: bin/%.jpp | bin/
	$(JAZZCT) --infer $^

$(CHECK_SCT):
bin/%.check_sct: bin/%.jpp | bin/
	$(JAZZCT) --sct --infer $^

bin/%.out: bin/%
	@./$<

# ----------------------------------------------------------------------------------------------------------------------

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	$(RM) -r bin/

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true

