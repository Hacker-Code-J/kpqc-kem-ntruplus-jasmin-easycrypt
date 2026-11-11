# -*- Makefile -*-

EASYCRYPT ?= easycrypt
VERIFY_PROOF := NTRUPlus768VerifyProof.ec
BRIDGE_PROOF := NTRUPlus768DecapVerifyBridge.ec

.PHONY: all check verify-proof bridge-proof

all: check

check: verify-proof bridge-proof

verify-proof:
	$(EASYCRYPT) compile -no-eco $(VERIFY_PROOF)

bridge-proof:
	$(EASYCRYPT) compile -no-eco $(BRIDGE_PROOF)

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

verify-proof bridge-proof: check-model-compatibility
