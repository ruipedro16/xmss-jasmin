# -*- Makefile -*-

# --------------------------------------------------------------------------------------------------

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

# --------------------------------------------------------------------------------------------------

IMPLS := XMSS-SHA2_10_256
IMPL_STR := $(foreach impl,$(IMPLS),$(shell echo $(impl) | tr '[:upper:]' '[:lower:]'))

# --------------------------------------------------------------------------------------------------

TESTS := bin/test_conditions $(addprefix bin/test_mem_, $(IMPL_STR))
OUT   := $(addsuffix .out, $(TESTS))

# --------------------------------------------------------------------------------------------------

JPP_FILES     := $(addsuffix .jpp, $(TESTS))
ASM_FILES     := $(JPP_FILES:.jpp=.s)
OBJ_FILES     := $(ASM_FILES:.s=.o)

CHECK_CT  := $(JPP_FILES:.jpp=.check_ct)
CHECK_SCT := $(JPP_FILES:.jpp=.check_sct)

# --------------------------------------------------------------------------------------------------

SOURCES := ../common/notrandombytes.c ../common/print.c ../utils.c

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
bin/test_conditions.jpp: bin/
	cp test_conditions.jazz $@
	$(JPP) $(JINCLUDE) -in $@ -out $@

# TODO: FIXME: improve this rule
bin/test_mem_xmss-sha2_10_256.jpp: bin/
	echo "from XMSS require \"params/params-xmss-sha2_10_256.jinc\"\n" > $@
	cat test_mem.jazz >> $@
	$(JPP) $(JINCLUDE) -in $@ -out $@
	$(PREPROCESSOR) --input_file $@ --output_file $@

$(ASM_FILES):
.PRECIOUS: bin/%.s
bin/%.s: bin/%.jpp
	$(JASMIN) $(JFLAGS) $(JINCLUDE) $< -o $@

$(TESTS):
bin/test_conditions: bin/test_conditions.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ test_conditions.c ../common/notrandombytes.c $<

# TODO: FIXME: improve this rule
bin/test_mem_xmss-sha2_10_256: bin/test_mem_xmss-sha2_10_256.s | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ test_mem.c $(wildcard ../*.c) ../common/notrandombytes.c -DIMPL=XMSS-SHA2_10_256 $< -lcrypto

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
