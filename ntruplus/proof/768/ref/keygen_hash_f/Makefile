# -*- Makefile -*-

EASYCRYPT ?= easycrypt
HEAVY_PROOF := NTRUPlus768HashFProof.ec
LIGHT_PROOF := NTRUPlus768KeygenHashFBridge.ec
CONCRETE_PROOF := NTRUPlus768KeygenHashFConcrete.ec
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 5 -max-provers 1

.PHONY: all check heavy light concrete hash-f-proof bridge-proof concrete-proof

all: check

check: heavy light concrete

heavy hash-f-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(HEAVY_PROOF)

light bridge-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(LIGHT_PROOF)

concrete concrete-proof:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(CONCRETE_PROOF)
