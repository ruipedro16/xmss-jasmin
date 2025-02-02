# -*- Makefile -*-

CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic -march=native -mtune=native
LDLIBS   = -lcrypto

IMPL_FLAGS := -DXMSSMT -DXMSS_VARIANT="\"XMSSMT-SHA2_20/2_256\""

SOURCE_FILES := $(wildcard *.c)

BIN := bin/speed_regular_sha2 bin/speed_sha2_shani

OUT := $(addsuffix .out, $(BIN))

all: $(BIN)
run: $(OUT)
.DEFAULT_GOAL := all

$(BIN):
bin/speed_regular_sha2: | bin/
	$(CC) $(CFLAGS) -o $@ $(SOURCE_FILES) $(LDLIBS) $(IMPL_FLAGS)

bin/speed_sha2_shani: | bin/
	$(CC) $(CFLAGS) -o $@ $(SOURCE_FILES) $(LDLIBS) $(IMPL_FLAGS) -DSHA2_SHANI

$(OUT):
bin/%.out: bin/%
	@./$<

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/
