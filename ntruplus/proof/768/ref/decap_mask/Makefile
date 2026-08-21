# -*- Makefile -*-

EASYCRYPT ?= easycrypt
MASK_PROOF := NTRUPlus768DecapMaskProof.ec
BRIDGE_PROOF := NTRUPlus768DecapMaskBridge.ec
SOURCE_BRIDGE_PROOF := NTRUPlus768DecapMaskSourceBridge.ec
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 5 -max-provers 1

.PHONY: all check mask-proof bridge-proof source-bridge-proof

all: check

check: mask-proof source-bridge-proof bridge-proof

mask-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(MASK_PROOF)

bridge-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(BRIDGE_PROOF)

source-bridge-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(SOURCE_BRIDGE_PROOF)
