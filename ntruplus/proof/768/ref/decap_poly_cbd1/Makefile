# -*- Makefile -*-

EASYCRYPT ?= easycrypt
PROOF := NTRUPlus768DecapPolyCBD1Bridge.ec

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(PROOF)
