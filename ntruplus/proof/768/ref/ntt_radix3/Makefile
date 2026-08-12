# -*- Makefile -*-

JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/ntt_radix3.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3
EXTRACTED := extracted/NTRUPlus768NTTRadix3.ec
WORD_PROOF := NTRUPlus768NTTRadix3Proof.ec
ALGEBRA_PROOF := NTRUPlus768NTTRadix3Algebra.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
STAGE1_PROOF := ../ntt_stage1
STAGE1_EXTRACTED := ../ntt_stage1/extracted
NTT_SCHEDULE := ../ntt_schedule
EASYCRYPT_INCLUDES := -I extracted -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(STAGE1_PROOF) -I $(STAGE1_EXTRACTED) -I $(NTT_SCHEDULE) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all extract check

all: check

extract:
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(EXTRACTED) -f $(SLICE)

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(WORD_PROOF)
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF)
