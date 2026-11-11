# -*- Makefile -*-

EASYCRYPT ?= easycrypt
THEORY := NTRUPlus768NTTSchedule.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_DIR := ../basemul
BASEMUL_EXTRACTED_DIR := ../basemul/extracted
EASYCRYPT_INCLUDES := -I . -I $(BASEMUL_DIR) -I $(BASEMUL_EXTRACTED_DIR) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(THEORY)

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

check: check-model-compatibility
