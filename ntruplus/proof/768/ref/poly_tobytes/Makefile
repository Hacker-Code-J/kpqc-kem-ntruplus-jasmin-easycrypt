# -*- Makefile -*-

EASYCRYPT ?= easycrypt
WORD_PROOF := NTRUPlus768PolyToBytesProof.ec
ALGEBRA_PROOF := NTRUPlus768PolyToBytesAlgebra.ec
POLY_FROMBYTES := ../poly_frombytes
FORMOSA_ARRAYS := ../../../../../external/formosa-mlkem/crypto-specs/arrays
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
EASYCRYPT_INCLUDES := -I . -I extracted -I ../basemul -I ../basemul/extracted -I $(POLY_FROMBYTES) -I $(FORMOSA_ARRAYS) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all check

all: check

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(WORD_PROOF)
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF)
