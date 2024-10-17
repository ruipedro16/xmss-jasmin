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

IMPL ?= # XMSS-SHA2_10_192  XMSS-SHA2_10_256 XMSSMT-SHA2_20/2_256 XMSSMT-SHA2_20/4_256
IMPL_STR := $(foreach impl,$(IMPL),$(shell echo $(impl) | tr '[:upper:]' '[:lower:]')) # TODO: Remove the foreach 

SPACE = $(space) $(space)

GET_IMPL = $(subst /,_,$(subst $(SPACE),_,$(wordlist 3,$(words $(subst _, ,$*)), $(subst _, ,$*))))
GET_IMPL_UPPER_CASE = $(shell echo $(IMPL_STR) | tr '[:lower:]' '[:upper:]')
# $(IMPL_STR) # $(shell echo $(subst $(SPACE),_,$(wordlist 3,$(words $(subst _, ,$*)), $(subst _, ,$*))) | tr '[:lower:]' '[:upper:]')


# ----------------------------------------------------------------------------------------------------------------------

TESTS := $(addprefix bin/test_xmss_, $(subst /,_, $(IMPL_STR)))
OUT   := $(addsuffix .out, $(TESTS))

# ----------------------------------------------------------------------------------------------------------------------

JPP_FILES             := $(addsuffix .jpp, $(TESTS))
JAZZ_FILES            := $(JPP_FILES:.jpp=.jazz)
ASM_FILES             := $(JAZZ_FILES:.jazz=.s)
ZEROIZATION_ASM_FILES := $(patsubst bin/%.jazz,bin/zeroization_loop_%.s,$(JAZZ_FILES)) $(patsubst bin/%.jazz,bin/zeroization_unroll_%.s,$(JAZZ_FILES))
ALL_ASM_FILES         := $(ASM_FILES) $(ZEROIZATION_ASM_FILES)
OBJ_FILES             := $(ALL_ASM_FILES:.s=.o)

CHECK_CT  := $(JPP_FILES:.jpp=.check_ct)
CHECK_SCT := $(JPP_FILES:.jpp=.check_sct) # NOTE: This should fail as the code is not protected against Spectre attacks

# ----------------------------------------------------------------------------------------------------------------------

REF_SOURCES := $(wildcard ../*.c)

SOURCES := test_xmss.c ../common/notrandombytes.c ../common/print.c

# ----------------------------------------------------------------------------------------------------------------------

default: $(TESTS)
run: $(OUT)

jpp_files: $(JPP_FILES)
jazz_files: $(JAZZ_FILES)
asm_files: $(ALL_ASM_FILES)
obj_files: $(OBJ_FILES)

ct: $(CHECK_CT)
sct: $(CHECK_SCT)

# ----------------------------------------------------------------------------------------------------------------------

$(JPP_FILES):
.PRECIOUS: bin/%.jpp
bin/%.jpp: | bin/
	../scripts/import_params_hash.py "$(GET_IMPL)" > $@
	cat test_xmss.jazz >> $@
	$(JPP) $(JINCLUDE) -in $@ -out $@

$(JAZZ_FILES):
.PRECIOUS: bin/%.jazz
bin/%.jazz: bin/%.jpp | bin/
	$(PREPROCESSOR) --input_file $< --output_file $@

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jazz
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(ZEROIZATION_ASM_FILES):
bin/zeroization_loop_%.s: bin/%.jazz
	$(JASMIN) $(JFLAGS) -stack-zero loop $(JINCLUDE) $< -o $@

bin/zeroization_unroll_%.s: bin/%.jazz
	$(JASMIN) $(JFLAGS) -stack-zero unrolled $(JINCLUDE) $< -o $@

$(TESTS):
bin/%: bin/%.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL="$(GET_IMPL_UPPER_CASE)" -DTEST_XMSS -DDEBUG_TEST \
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
	-$(RM) -r bin/
	-$(RM) -r *.txt

.PHONY: clean_executables
clean_executables:
	find bin/ -type f -executable -delete || true

debug:
	@echo $(TESTS)