# -*- Makefile -*-

EASYCRYPT ?= easycrypt
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 30 -max-provers 1
PROOF := NTRUPlus768KeygenSecretFBridge.ec

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(PROOF)

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

check: check-model-compatibility
