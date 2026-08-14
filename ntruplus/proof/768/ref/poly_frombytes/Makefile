# -*- Makefile -*-

EASYCRYPT ?= easycrypt
ALGEBRA_PROOF := NTRUPlus768PolyFromBytesAlgebra.ec
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
POLY_BASEMUL := ../poly_basemul
POLY_BASEMUL_EXTRACTED := ../poly_basemul/extracted
POLY_BASEMUL_INVNTT := ../poly_basemul_invntt
NTT_SCHEDULE := ../ntt_schedule
NTT_RADIX2_64 := ../ntt_radix2_64
NTT_RADIX2_64_EXTRACTED := ../ntt_radix2_64/extracted
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
FORMOSA_ARRAYS := ../../../../../external/formosa-mlkem/crypto-specs/arrays
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
EASYCRYPT_INCLUDES := -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(POLY_BASEMUL) -I $(POLY_BASEMUL_EXTRACTED) -I $(POLY_BASEMUL_INVNTT) -I $(NTT_RADIX2_64) -I $(NTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX2_4) -I $(INVNTT_RADIX2_4_EXTRACTED) -I $(INVNTT_RADIX2_8) -I $(INVNTT_RADIX2_8_EXTRACTED) -I $(INVNTT_RADIX2_16) -I $(INVNTT_RADIX2_16_EXTRACTED) -I $(INVNTT_RADIX2_32) -I $(INVNTT_RADIX2_32_EXTRACTED) -I $(INVNTT_RADIX2_64) -I $(INVNTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX3) -I $(INVNTT_RADIX3_EXTRACTED) -I $(INVNTT_FINAL) -I $(INVNTT_FINAL_EXTRACTED) -I $(INVNTT) -I $(INVNTT_EXTRACTED) -I $(NTT_SCHEDULE) -I $(FORMOSA_ARRAYS) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF)
