# -*- Makefile -*-

JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/poly_sub.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_sub
EXTRACTED := extracted/NTRUPlus768PolySub.ec
WORD_PROOF := NTRUPlus768PolySubProof.ec
ALGEBRA_PROOF := NTRUPlus768PolySubAlgebra.ec
BRIDGE_PROOF := NTRUPlus768PolySubDecapBridge.ec
FORMOSA_ARRAYS := ../../../../../external/formosa-mlkem/crypto-specs/arrays
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
POLY_BASEMUL := ../poly_basemul
POLY_BASEMUL_EXTRACTED := ../poly_basemul/extracted
POLY_BASEMUL_INVNTT := ../poly_basemul_invntt
POLY_FROMBYTES := ../poly_frombytes
CREPMOD3 := ../crepmod3
CREPMOD3_EXTRACTED := ../crepmod3/extracted
NTT_SCHEDULE := ../ntt_schedule
NTT := ../ntt
NTT_EXTRACTED := ../ntt/extracted
NTT_STAGE1 := ../ntt_stage1
NTT_STAGE1_EXTRACTED := ../ntt_stage1/extracted
NTT_RADIX3 := ../ntt_radix3
NTT_RADIX3_EXTRACTED := ../ntt_radix3/extracted
NTT_RADIX2_64 := ../ntt_radix2_64
NTT_RADIX2_64_EXTRACTED := ../ntt_radix2_64/extracted
NTT_RADIX2_32 := ../ntt_radix2_32
NTT_RADIX2_32_EXTRACTED := ../ntt_radix2_32/extracted
NTT_RADIX2_16 := ../ntt_radix2_16
NTT_RADIX2_16_EXTRACTED := ../ntt_radix2_16/extracted
NTT_RADIX2_8 := ../ntt_radix2_8
NTT_RADIX2_8_EXTRACTED := ../ntt_radix2_8/extracted
NTT_RADIX2_4 := ../ntt_radix2_4
NTT_RADIX2_4_EXTRACTED := ../ntt_radix2_4/extracted
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
INVNTT := ../invntt
INVNTT_EXTRACTED := ../invntt/extracted
EASYCRYPT_INCLUDES := -I extracted -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(POLY_BASEMUL) -I $(POLY_BASEMUL_EXTRACTED) -I $(POLY_BASEMUL_INVNTT) -I $(POLY_FROMBYTES) -I $(CREPMOD3) -I $(CREPMOD3_EXTRACTED) -I $(NTT) -I $(NTT_EXTRACTED) -I $(NTT_STAGE1) -I $(NTT_STAGE1_EXTRACTED) -I $(NTT_RADIX3) -I $(NTT_RADIX3_EXTRACTED) -I $(NTT_RADIX2_64) -I $(NTT_RADIX2_64_EXTRACTED) -I $(NTT_RADIX2_32) -I $(NTT_RADIX2_32_EXTRACTED) -I $(NTT_RADIX2_16) -I $(NTT_RADIX2_16_EXTRACTED) -I $(NTT_RADIX2_8) -I $(NTT_RADIX2_8_EXTRACTED) -I $(NTT_RADIX2_4) -I $(NTT_RADIX2_4_EXTRACTED) -I $(INVNTT_RADIX2_4) -I $(INVNTT_RADIX2_4_EXTRACTED) -I $(INVNTT_RADIX2_8) -I $(INVNTT_RADIX2_8_EXTRACTED) -I $(INVNTT_RADIX2_16) -I $(INVNTT_RADIX2_16_EXTRACTED) -I $(INVNTT_RADIX2_32) -I $(INVNTT_RADIX2_32_EXTRACTED) -I $(INVNTT_RADIX2_64) -I $(INVNTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX3) -I $(INVNTT_RADIX3_EXTRACTED) -I $(INVNTT_FINAL) -I $(INVNTT_FINAL_EXTRACTED) -I $(INVNTT) -I $(INVNTT_EXTRACTED) -I $(NTT_SCHEDULE) -I $(FORMOSA_ARRAYS) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all extract check

all: check

extract:
	@mkdir -p extracted
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(EXTRACTED) -f $(SLICE)
	find extracted -maxdepth 1 -type f -name '*.ec' -exec sed -i 's/[[:space:]]\+$$//' {} +

check: extract
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(WORD_PROOF)
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF)
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(BRIDGE_PROOF)
