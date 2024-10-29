# -*- Makefile -*-

# ----------------------------------------------------------------------------------------------------------------------

AS       ?= as
CC       ?= clang
CFLAGS   ?= -Wall -g -O3 -Wextra -Wpedantic
LDLIBS   = -lcrypto -lm

# ----------------------------------------------------------------------------------------------------------------------

BIN := bin/addr_properties
OUT := $(addsuffix .out, $(BIN))

default: $(BIN)
run: $(OUT)

SOURCES := $(wildcard ../*.c) $(wildcard ../common/*.c) main.c

$(BIN): | bin/
	$(CC) $(CFLAGS) -o $@ -I../common -I../ -DIMPL="XMSSMT-SHA2_20/2_256" $(SOURCES) $(LDLIBS) 

$(OUT): $(BIN)
	./$<

bin/:
	mkdir -p $@

.PHONY: clean
clean:
	-$(RM) -r bin/


debug:
	@echo $(SOURCES)