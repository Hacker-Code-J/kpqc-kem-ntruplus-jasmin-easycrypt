# -*- Makefile -*-

EASYCRYPT ?= easycrypt
FAIL_PROOF := NTRUPlus768DecapFailProof.ec
BRIDGE_PROOF := NTRUPlus768DecapFailBridge.ec
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 5 -max-provers 1

.PHONY: all check fail-proof bridge-proof

all: check

check: fail-proof bridge-proof

fail-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(FAIL_PROOF)

bridge-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(BRIDGE_PROOF)
