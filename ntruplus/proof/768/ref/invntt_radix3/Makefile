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
NTT_SCHEDULE_PROOF := ../ntt_schedule
EASYCRYPT_INCLUDES := -I extracted -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(RADIX2_64_PROOF) -I $(RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX2_64_PROOF) -I $(INVNTT_RADIX2_64_EXTRACTED) -I $(NTT_SCHEDULE_PROOF) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

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
