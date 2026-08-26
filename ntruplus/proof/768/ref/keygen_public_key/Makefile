# -*- Makefile -*-

EASYCRYPT ?= easycrypt
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 30 -max-provers 1
PROOF := NTRUPlus768KeygenPublicKeyBridge.ec

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(PROOF)
