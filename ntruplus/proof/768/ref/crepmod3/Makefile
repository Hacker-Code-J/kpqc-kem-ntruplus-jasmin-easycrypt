# -*- Makefile -*-

JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/crepmod3.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3
EXTRACTED := extracted/NTRUPlus768Crepmod3.ec
WORD_PROOF := NTRUPlus768Crepmod3Proof.ec
ALGEBRA_PROOF := NTRUPlus768Crepmod3Algebra.ec
DECAP_BRIDGE := NTRUPlus768Crepmod3DecapBridge.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
FORMOSA_ARRAYS := ../../../../../external/formosa-mlkem/crypto-specs/arrays
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
POLY_BASEMUL := ../poly_basemul
POLY_BASEMUL_EXTRACTED := ../poly_basemul/extracted
POLY_BASEMUL_INVNTT := ../poly_basemul_invntt
POLY_FROMBYTES := ../poly_frombytes
INVNTT_PROOF := ../invntt
INVNTT_EXTRACTED := ../invntt/extracted
INVNTT_RADIX2_4 := ../invntt_radix2_4
INVNTT_RADIX2_4_EXTRACTED := ../invntt_radix2_4/extracted
INVNTT_RADIX2_8 := ../invntt_radix2_8
INVNTT_RADIX2_8_EXTRACTED := ../invntt_radix2_8/extracted
INVNTT_RADIX2_16 := ../invntt_radix2_16
INVNTT_RADIX2_16_EXTRACTED := ../invntt_radix2_16/extracted
INVNTT_RADIX2_32 := ../invntt_radix2_32
INVNTT_RADIX2_32_EXTRACTED := ../invntt_radix2_32/extracted
INVNTT_RADIX2_64 := ../invntt_radix2_64
INVNTT_RADIX2_64_EXTRACTED := ../invntt_radix2_64/extracted
INVNTT_RADIX3 := ../invntt_radix3
INVNTT_RADIX3_EXTRACTED := ../invntt_radix3/extracted
INVNTT_FINAL := ../invntt_final
INVNTT_FINAL_EXTRACTED := ../invntt_final/extracted
NTT_RADIX2_64 := ../ntt_radix2_64
NTT_RADIX2_64_EXTRACTED := ../ntt_radix2_64/extracted
NTT_STAGE1 := ../ntt_stage1
NTT_STAGE1_EXTRACTED := ../ntt_stage1/extracted
NTT_SCHEDULE := ../ntt_schedule
EASYCRYPT_INCLUDES := -I extracted -I . -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON) -I $(FORMOSA_ARRAYS) -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(POLY_BASEMUL) -I $(POLY_BASEMUL_EXTRACTED) -I $(POLY_BASEMUL_INVNTT) -I $(POLY_FROMBYTES) -I $(INVNTT_PROOF) -I $(INVNTT_EXTRACTED) -I $(INVNTT_RADIX2_4) -I $(INVNTT_RADIX2_4_EXTRACTED) -I $(INVNTT_RADIX2_8) -I $(INVNTT_RADIX2_8_EXTRACTED) -I $(INVNTT_RADIX2_16) -I $(INVNTT_RADIX2_16_EXTRACTED) -I $(INVNTT_RADIX2_32) -I $(INVNTT_RADIX2_32_EXTRACTED) -I $(INVNTT_RADIX2_64) -I $(INVNTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX3) -I $(INVNTT_RADIX3_EXTRACTED) -I $(INVNTT_FINAL) -I $(INVNTT_FINAL_EXTRACTED) -I $(NTT_RADIX2_64) -I $(NTT_RADIX2_64_EXTRACTED) -I $(NTT_STAGE1) -I $(NTT_STAGE1_EXTRACTED) -I $(NTT_SCHEDULE)

.PHONY: all extract check

all: check

extract:
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(EXTRACTED) -f $(SLICE)
	find extracted -maxdepth 1 -type f -name '*.ec' -exec sed -i 's/[[:space:]]\+$$//' {} +

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(WORD_PROOF)
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF)
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(DECAP_BRIDGE)
