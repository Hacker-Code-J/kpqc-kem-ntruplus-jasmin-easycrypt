# -*- Makefile -*-

EASYCRYPT ?= easycrypt
PROOF := NTRUPlus768DecapHashHBridge.ec

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(PROOF)
