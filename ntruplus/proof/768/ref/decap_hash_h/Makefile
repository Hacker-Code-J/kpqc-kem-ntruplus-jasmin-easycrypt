# -*- Makefile -*-

EASYCRYPT ?= easycrypt
PROOF := NTRUPlus768DecapHashHBridge.ec

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(PROOF)

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

check: check-model-compatibility
