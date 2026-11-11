# -*- Makefile -*-

EASYCRYPT ?= easycrypt
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 30 -max-provers 1
PROOFS := NTRUPlus768CoefficientRecovery.ec \
  NTRUPlus768IntegerConvolution.ec \
  NTRUPlus768Crepmod3Recovery.ec \
  NTRUPlus768ValidKeyM1Recovery.ec

.PHONY: all check

all: check

check:
	@set -e; for proof in $(PROOFS); do \
	  $(EASYCRYPT) compile $(EASYCRYPT_FLAGS) "$$proof"; \
	done

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

check: check-model-compatibility
