# -*- Makefile -*-

EASYCRYPT ?= easycrypt
PROOF := NTRUPlus768DecapR1ToBytesBridge.ec

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(PROOF)
