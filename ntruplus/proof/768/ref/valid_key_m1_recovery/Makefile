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
