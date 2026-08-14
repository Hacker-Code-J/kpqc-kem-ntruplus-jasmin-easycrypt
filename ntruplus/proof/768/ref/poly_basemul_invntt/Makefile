# -*- Makefile -*-

EASYCRYPT ?= easycrypt
PROOF := NTRUPlus768PolyBasemulInvNTTAlgebra.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
POLY_BASEMUL_PROOF := ../poly_basemul
POLY_BASEMUL_EXTRACTED := ../poly_basemul/extracted
NTT_SCHEDULE_PROOF := ../ntt_schedule
NTT_RADIX2_64_PROOF := ../ntt_radix2_64
NTT_RADIX2_64_EXTRACTED := ../ntt_radix2_64/extracted
INVNTT_RADIX2_4_PROOF := ../invntt_radix2_4
INVNTT_RADIX2_4_EXTRACTED := ../invntt_radix2_4/extracted
INVNTT_RADIX2_8_PROOF := ../invntt_radix2_8
INVNTT_RADIX2_8_EXTRACTED := ../invntt_radix2_8/extracted
INVNTT_RADIX2_16_PROOF := ../invntt_radix2_16
INVNTT_RADIX2_16_EXTRACTED := ../invntt_radix2_16/extracted
INVNTT_RADIX2_32_PROOF := ../invntt_radix2_32
INVNTT_RADIX2_32_EXTRACTED := ../invntt_radix2_32/extracted
INVNTT_RADIX2_64_PROOF := ../invntt_radix2_64
INVNTT_RADIX2_64_EXTRACTED := ../invntt_radix2_64/extracted
INVNTT_RADIX3_PROOF := ../invntt_radix3
INVNTT_RADIX3_EXTRACTED := ../invntt_radix3/extracted
INVNTT_FINAL_PROOF := ../invntt_final
INVNTT_FINAL_EXTRACTED := ../invntt_final/extracted
INVNTT_PROOF := ../invntt
INVNTT_EXTRACTED := ../invntt/extracted
EASYCRYPT_INCLUDES := -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(POLY_BASEMUL_PROOF) -I $(POLY_BASEMUL_EXTRACTED) -I $(NTT_RADIX2_64_PROOF) -I $(NTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX2_4_PROOF) -I $(INVNTT_RADIX2_4_EXTRACTED) -I $(INVNTT_RADIX2_8_PROOF) -I $(INVNTT_RADIX2_8_EXTRACTED) -I $(INVNTT_RADIX2_16_PROOF) -I $(INVNTT_RADIX2_16_EXTRACTED) -I $(INVNTT_RADIX2_32_PROOF) -I $(INVNTT_RADIX2_32_EXTRACTED) -I $(INVNTT_RADIX2_64_PROOF) -I $(INVNTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX3_PROOF) -I $(INVNTT_RADIX3_EXTRACTED) -I $(INVNTT_FINAL_PROOF) -I $(INVNTT_FINAL_EXTRACTED) -I $(INVNTT_PROOF) -I $(INVNTT_EXTRACTED) -I $(NTT_SCHEDULE_PROOF) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(PROOF)
