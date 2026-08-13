# -*- Makefile -*-

JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/ntt.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt
EXTRACTED := extracted/NTRUPlus768NTT.ec
WORD_PROOF := NTRUPlus768NTTProof.ec
ALGEBRA_PROOF := NTRUPlus768NTTAlgebra.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
STAGE1_PROOF := ../ntt_stage1
STAGE1_EXTRACTED := ../ntt_stage1/extracted
RADIX3_PROOF := ../ntt_radix3
RADIX3_EXTRACTED := ../ntt_radix3/extracted
RADIX2_64_PROOF := ../ntt_radix2_64
RADIX2_64_EXTRACTED := ../ntt_radix2_64/extracted
RADIX2_32_PROOF := ../ntt_radix2_32
RADIX2_32_EXTRACTED := ../ntt_radix2_32/extracted
RADIX2_16_PROOF := ../ntt_radix2_16
RADIX2_16_EXTRACTED := ../ntt_radix2_16/extracted
RADIX2_8_PROOF := ../ntt_radix2_8
RADIX2_8_EXTRACTED := ../ntt_radix2_8/extracted
RADIX2_4_PROOF := ../ntt_radix2_4
RADIX2_4_EXTRACTED := ../ntt_radix2_4/extracted
NTT_SCHEDULE := ../ntt_schedule
EASYCRYPT_INCLUDES := -I extracted -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(STAGE1_PROOF) -I $(STAGE1_EXTRACTED) -I $(RADIX3_PROOF) -I $(RADIX3_EXTRACTED) -I $(RADIX2_64_PROOF) -I $(RADIX2_64_EXTRACTED) -I $(RADIX2_32_PROOF) -I $(RADIX2_32_EXTRACTED) -I $(RADIX2_16_PROOF) -I $(RADIX2_16_EXTRACTED) -I $(RADIX2_8_PROOF) -I $(RADIX2_8_EXTRACTED) -I $(RADIX2_4_PROOF) -I $(RADIX2_4_EXTRACTED) -I $(NTT_SCHEDULE) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all extract check

all: check

extract:
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(EXTRACTED) -f $(SLICE)

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(WORD_PROOF)
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF)
