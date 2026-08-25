# -*- Makefile -*-

JASMINC ?= jasminc
JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/baseinv.jazz
SLICE := __baseinv_core
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-baseinv-jasmin-proof.XXXXXX))
ASM := $(OUTDIR)/baseinv.s
GENERATED := $(OUTDIR)/NTRUPlus768BaseInv.ec
TRACKED := extracted/NTRUPlus768BaseInv.ec
PROOF := NTRUPlus768BaseInvProof.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
FQINV_PROOF := ../fqinv
FQINV_JASMIN := ../fqinv_jasmin
FQINV_JASMIN_EXTRACTED := ../fqinv_jasmin/extracted
BASEINV_PROOF := ../baseinv
EASYCRYPT_INCLUDES := -I $(OUTDIR) -I . -I $(FQINV_JASMIN) -I $(FQINV_JASMIN_EXTRACTED) -I $(FQINV_PROOF) -I $(BASEINV_PROOF) -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all asm extract refresh-extraction check

all: check

asm:
	@mkdir -p $(OUTDIR)
	$(JASMINC) -arch x86-64 -call-conv linux -system linux -checksafety -slice $(SLICE) -o $(ASM) $(SOURCE)

extract:
	@mkdir -p $(OUTDIR)
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(GENERATED) -f $(SLICE)
	cmp -s $(GENERATED) $(TRACKED) || \
	  { diff -u $(TRACKED) $(GENERATED); exit 1; }

refresh-extraction:
	@mkdir -p extracted
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(TRACKED) -f $(SLICE)

check: extract
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(PROOF)
