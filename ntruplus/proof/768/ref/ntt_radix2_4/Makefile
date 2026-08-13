# -*- Makefile -*-

JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/ntt_radix2_4.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4
EXTRACTED := extracted/NTRUPlus768NTTRadix2_4.ec
WORD_PROOF := NTRUPlus768NTTRadix2_4Proof.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
RADIX3_PROOF := ../ntt_radix3
RADIX3_EXTRACTED := ../ntt_radix3/extracted
RADIX2_64_PROOF := ../ntt_radix2_64
RADIX2_64_EXTRACTED := ../ntt_radix2_64/extracted
RADIX2_32_PROOF := ../ntt_radix2_32
RADIX2_32_EXTRACTED := ../ntt_radix2_32/extracted
RADIX2_16_PROOF := ../ntt_radix2_16
RADIX2_16_EXTRACTED := ../ntt_radix2_16/extracted
NTT_SCHEDULE := ../ntt_schedule
EASYCRYPT_INCLUDES := -I extracted -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(RADIX3_PROOF) -I $(RADIX3_EXTRACTED) -I $(RADIX2_64_PROOF) -I $(RADIX2_64_EXTRACTED) -I $(RADIX2_32_PROOF) -I $(RADIX2_32_EXTRACTED) -I $(RADIX2_16_PROOF) -I $(RADIX2_16_EXTRACTED) -I $(NTT_SCHEDULE) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all extract check

all: check

extract:
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(EXTRACTED) -f $(SLICE)

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(WORD_PROOF)
