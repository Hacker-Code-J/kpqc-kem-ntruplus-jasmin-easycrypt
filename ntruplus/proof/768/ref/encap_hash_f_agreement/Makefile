# -*- Makefile -*-

EASYCRYPT ?= easycrypt
AGREEMENT_PROOF := NTRUPlus768EncapHashFAgreement.ec
CONCRETE_PROOF := NTRUPlus768EncapHashFConcrete.ec
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 5 -max-provers 1
EASYCRYPT_INCLUDES := -I . -I ../keygen_hash_f

.PHONY: all check agreement concrete

all: check

check: agreement concrete

agreement:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(EASYCRYPT_INCLUDES) $(AGREEMENT_PROOF)

concrete:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(EASYCRYPT_INCLUDES) $(CONCRETE_PROOF)

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

agreement concrete: check-model-compatibility
