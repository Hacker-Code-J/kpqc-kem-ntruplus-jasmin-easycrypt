# -*- Makefile -*-

EASYCRYPT ?= easycrypt
THEORY := NTRUPlus768CyclotomicFactorization.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_DIR := ../basemul
BASEMUL_EXTRACTED_DIR := ../basemul/extracted
FQINV_DIR := ../fqinv
NTT_SCHEDULE_DIR := ../ntt_schedule
EASYCRYPT_INCLUDES := -I . -I $(FQINV_DIR) -I $(NTT_SCHEDULE_DIR) \
	-I $(BASEMUL_DIR) -I $(BASEMUL_EXTRACTED_DIR) \
	-I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(THEORY)
