# -*- Makefile -*-

JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/ntt_stage1.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1
EXTRACTED := extracted/NTRUPlus768NTTStage1.ec
WORD_PROOF := NTRUPlus768NTTStage1Proof.ec
ALGEBRA_PROOF := NTRUPlus768NTTStage1Algebra.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
NTT_SCHEDULE := ../ntt_schedule
EASYCRYPT_INCLUDES := -I extracted -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(NTT_SCHEDULE) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all extract check

all: check

extract:
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(EXTRACTED) -f $(SLICE)

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(WORD_PROOF)
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF)
