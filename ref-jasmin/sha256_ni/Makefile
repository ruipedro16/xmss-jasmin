
JASMIN ?= jasminc
JFLAGS ?= -nowarning ${JADDFLAGS}

CC     ?= clang
CFLAGS ?= -march=native

C_FILES := $(wildcard *.c)
TEST    := bin/sha256_ni
OUT     := $(addsuffix .out, $(TEST))

all: $(TEST)
default: $(TEST)
run: $(OUT)

.PRECIOUS: bin/%.s
bin/%.s: %.jazz | bin/
	$(JASMIN) $(JFLAGS) -o $@ $<

bin/%: bin/%.s
	$(CC) $(CFLAGS) -o $@ -I. print.c test_sha256ni.c $<

bin/%.out: bin/%
	@./$<

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/ *.s 
	