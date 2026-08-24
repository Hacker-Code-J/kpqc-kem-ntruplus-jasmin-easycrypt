# -*- Makefile -*-

EASYCRYPT ?= easycrypt
ALGEBRA_PROOF := NTRUPlus768EncapPolyBasemulAddAlgebra.ec
BRIDGE_PROOF := NTRUPlus768EncapPolyBasemulAddBridge.ec
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 5 -max-provers 1

.PHONY: all check algebra bridge

all: check

check: algebra bridge

algebra:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(ALGEBRA_PROOF)

bridge:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(BRIDGE_PROOF)
