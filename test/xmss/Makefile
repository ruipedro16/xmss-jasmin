# -*- Makefile -*-

# ----------------------------------------------------------------------------------------------------------------------

# TODO: Add checkCT 

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

GET_IMPL = $(subst $(SPACE),_,$(wordlist 3, 5, $(subst _, ,$*)))
GET_IMPL_UPPER_CASE = $(shell echo $(subst $(SPACE),_,$(wordlist 3, 5, $(subst _, ,$*))) | tr '[:lower:]' '[:upper:]')

# ----------------------------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_xmss_, $(IMPL_STR))
OUT   := $(addsuffix .out, $(TESTS))

# ----------------------------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
JAZZ_FILES    := $(JPP_FILES:.jpp=.jazz)
ASM_FILES     := $(JAZZ_FILES:.jazz=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)

CHECK_CT  := $(JPP_FILES:.jpp=.check_ct)
CHECK_SCT := $(JPP_FILES:.jpp=.check_sct)

# ----------------------------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)

SOURCES := test_xmss.c ../common/notrandombytes.c ../common/print.c

# ----------------------------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)

jpp_files: $(JPP_FILES)
jazz_files: $(JAZZ_FILES)
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
	cat test_xmss.jazz  >> $@
	$(JPP) $(JINCLUDE) -in $@ -out $@

$(JAZZ_FILES):
.PRECIOUS: bin/%.jazz
bin/%.jazz: bin/%.jpp | bin/
	$(PREPROCESSOR) --input_file $< --output_file $@

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jazz
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(TESTS):
bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL=$(GET_IMPL_UPPER_CASE) -DTEST_XMSS -DDEBUG_TEST \
	$(SOURCES) $(REF_SOURCES) $< $(LDLIBS) -lm

$(OBJ_FILES):
bin/%.o: bin/%.s
	$(AS) $< -o $@

$(CHECK_CT):
bin/%.check_ct: bin/%.jazz | bin/
	$(JAZZCT) --infer $^

$(CHECK_SCT):
bin/%.check_sct: bin/%.jazz | bin/
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
