# -*- Makefile -*-

JASMINC ?= jasminc
JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/fqinv.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_fqinv
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-fqinv-jasmin-proof.XXXXXX))
ASM := $(OUTDIR)/fqinv.s
GENERATED := $(OUTDIR)/NTRUPlus768FqInv.ec
TRACKED := extracted/NTRUPlus768FqInv.ec
PROOF := NTRUPlus768FqInvProof.ec
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
FQINV_ALGEBRA := ../fqinv
EASYCRYPT_INCLUDES := -I $(OUTDIR) -I . -I $(FQINV_ALGEBRA) -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

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
