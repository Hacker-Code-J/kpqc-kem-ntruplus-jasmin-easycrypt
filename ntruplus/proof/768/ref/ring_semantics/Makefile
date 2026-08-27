# -*- Makefile -*-

EASYCRYPT ?= easycrypt
FACTORIZATION_THEORY := NTRUPlus768CyclotomicFactorization.ec
EVALUATION_THEORY := NTRUPlus768EvaluationSemantics.ec
REPRESENTATION_THEORY := NTRUPlus768TerminalRepresentation.ec
FORWARD_STAGE1_THEORY := NTRUPlus768ForwardNTTStage1Semantics.ec
FORWARD_RADIX3_THEORY := NTRUPlus768ForwardNTTRadix3Semantics.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_DIR := ../basemul
BASEMUL_EXTRACTED_DIR := ../basemul/extracted
FQINV_DIR := ../fqinv
NTT_SCHEDULE_DIR := ../ntt_schedule
POLY_BASEMUL_DIR := ../poly_basemul
POLY_BASEMUL_EXTRACTED_DIR := ../poly_basemul/extracted
NTT_STAGE1_DIR := ../ntt_stage1
NTT_STAGE1_EXTRACTED_DIR := ../ntt_stage1/extracted
NTT_RADIX3_DIR := ../ntt_radix3
NTT_RADIX3_EXTRACTED_DIR := ../ntt_radix3/extracted
EASYCRYPT_INCLUDES := -I . -I $(FQINV_DIR) -I $(NTT_SCHEDULE_DIR) \
	-I $(BASEMUL_DIR) -I $(BASEMUL_EXTRACTED_DIR) \
	-I $(POLY_BASEMUL_DIR) -I $(POLY_BASEMUL_EXTRACTED_DIR) \
	-I $(NTT_STAGE1_DIR) -I $(NTT_STAGE1_EXTRACTED_DIR) \
	-I $(NTT_RADIX3_DIR) -I $(NTT_RADIX3_EXTRACTED_DIR) \
	-I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all check factorization evaluation representation forward-stage1 forward-radix3

all: check

check: factorization evaluation representation forward-stage1 forward-radix3

factorization:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(FACTORIZATION_THEORY)

evaluation:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(EVALUATION_THEORY)

representation:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(REPRESENTATION_THEORY)

forward-stage1:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(FORWARD_STAGE1_THEORY)

forward-radix3:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(FORWARD_RADIX3_THEORY)
