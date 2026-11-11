# -*- Makefile -*-

JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/invntt_radix3.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_invntt_radix3
EXTRACTED := extracted/NTRUPlus768InvNTTRadix3.ec
WORD_PROOF := NTRUPlus768InvNTTRadix3Proof.ec
ALGEBRA_PROOF := NTRUPlus768InvNTTRadix3Algebra.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
RADIX2_64_PROOF := ../ntt_radix2_64
RADIX2_64_EXTRACTED := ../ntt_radix2_64/extracted
INVNTT_RADIX2_64_PROOF := ../invntt_radix2_64
INVNTT_RADIX2_64_EXTRACTED := ../invntt_radix2_64/extracted
INVNTT_RADIX2_32_PROOF := ../invntt_radix2_32
INVNTT_RADIX2_32_EXTRACTED := ../invntt_radix2_32/extracted
INVNTT_RADIX2_16_PROOF := ../invntt_radix2_16
INVNTT_RADIX2_16_EXTRACTED := ../invntt_radix2_16/extracted
INVNTT_RADIX2_8_PROOF := ../invntt_radix2_8
INVNTT_RADIX2_8_EXTRACTED := ../invntt_radix2_8/extracted
INVNTT_RADIX2_4_PROOF := ../invntt_radix2_4
INVNTT_RADIX2_4_EXTRACTED := ../invntt_radix2_4/extracted
NTT_SCHEDULE_PROOF := ../ntt_schedule
EASYCRYPT_INCLUDES := -I extracted -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(RADIX2_64_PROOF) -I $(RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX2_64_PROOF) -I $(INVNTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX2_32_PROOF) -I $(INVNTT_RADIX2_32_EXTRACTED) -I $(INVNTT_RADIX2_16_PROOF) -I $(INVNTT_RADIX2_16_EXTRACTED) -I $(INVNTT_RADIX2_8_PROOF) -I $(INVNTT_RADIX2_8_EXTRACTED) -I $(INVNTT_RADIX2_4_PROOF) -I $(INVNTT_RADIX2_4_EXTRACTED) -I $(NTT_SCHEDULE_PROOF) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all extract check

all: check

extract:
	@mkdir -p extracted
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(EXTRACTED) -f $(SLICE)

check: extract
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(WORD_PROOF)
	@if [ -f $(ALGEBRA_PROOF) ]; then \
	  $(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF); \
	fi

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

check: check-model-compatibility
