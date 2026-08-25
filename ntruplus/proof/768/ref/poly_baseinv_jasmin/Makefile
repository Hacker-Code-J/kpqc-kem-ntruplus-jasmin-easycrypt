# -*- Makefile -*-

JASMINC ?= jasminc
JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
EASYCRYPT_FLAGS ?= -no-eco -p Z3 -timeout 30 -max-provers 1
SOURCE := ../../../../jasmin/768/ref/poly_baseinv.jazz
SLICE := __poly_baseinv_core
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-poly-baseinv-jasmin-proof.XXXXXX))
PROOFDIR := $(abspath .)
REPO_ROOT := $(abspath ../../../../..)
ABS_OUTDIR := $(abspath $(OUTDIR))
ASM := $(OUTDIR)/poly_baseinv.s
GENERATED := $(OUTDIR)/NTRUPlus768PolyBaseInv.ec
TRACKED := extracted/NTRUPlus768PolyBaseInv.ec
PROOF := NTRUPlus768PolyBaseInvProof.ec
ROOT_PROOF := ntruplus/proof/768/ref/poly_baseinv_jasmin/$(PROOF)
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
BASEINV_JASMIN := ../baseinv_jasmin
BASEINV_JASMIN_EXTRACTED := ../baseinv_jasmin/extracted
BASEINV_PROOF := ../baseinv
FQINV_PROOF := ../fqinv
FQINV_JASMIN := ../fqinv_jasmin
FQINV_JASMIN_EXTRACTED := ../fqinv_jasmin/extracted
POLY_BASEMUL := ../poly_basemul
POLY_BASEMUL_EXTRACTED := ../poly_basemul/extracted
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
NTT_SCHEDULE := ../ntt_schedule
EASYCRYPT_INCLUDES := -I $(OUTDIR) -I . -I $(BASEINV_JASMIN) -I $(BASEINV_JASMIN_EXTRACTED) -I $(BASEINV_PROOF) -I $(FQINV_PROOF) -I $(FQINV_JASMIN) -I $(FQINV_JASMIN_EXTRACTED) -I $(POLY_BASEMUL) -I $(POLY_BASEMUL_EXTRACTED) -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(NTT_SCHEDULE) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)
EASYCRYPT_ABS_INCLUDES := -I $(ABS_OUTDIR) -I $(PROOFDIR) -I $(abspath $(BASEINV_JASMIN)) -I $(abspath $(BASEINV_JASMIN_EXTRACTED)) -I $(abspath $(BASEINV_PROOF)) -I $(abspath $(FQINV_PROOF)) -I $(abspath $(FQINV_JASMIN)) -I $(abspath $(FQINV_JASMIN_EXTRACTED)) -I $(abspath $(POLY_BASEMUL)) -I $(abspath $(POLY_BASEMUL_EXTRACTED)) -I $(abspath $(BASEMUL_PROOF)) -I $(abspath $(BASEMUL_EXTRACTED)) -I $(abspath $(NTT_SCHEDULE)) -I $(abspath $(FORMOSA_ECLIB)) -I $(abspath $(FORMOSA_COMMON))
EASYCRYPT_ROOT_INCLUDES := -I $(ABS_OUTDIR) -I ntruplus/proof/768/ref/poly_baseinv_jasmin -I ntruplus/proof/768/ref/baseinv_jasmin -I ntruplus/proof/768/ref/baseinv_jasmin/extracted -I ntruplus/proof/768/ref/baseinv -I ntruplus/proof/768/ref/fqinv -I ntruplus/proof/768/ref/fqinv_jasmin -I ntruplus/proof/768/ref/fqinv_jasmin/extracted -I ntruplus/proof/768/ref/poly_basemul -I ntruplus/proof/768/ref/poly_basemul/extracted -I ntruplus/proof/768/ref/basemul -I ntruplus/proof/768/ref/basemul/extracted -I ntruplus/proof/768/ref/ntt_schedule -I external/formosa-mlkem/proof/eclib -I external/formosa-mlkem/crypto-specs/common

.PHONY: all asm extract refresh-extraction check

all: check

asm:
	@mkdir -p $(OUTDIR)
	$(JASMINC) -auto-spill-all -arch x86-64 -call-conv linux -system linux -checksafety -slice $(SLICE) -o $(ASM) $(SOURCE)

extract:
	@mkdir -p $(OUTDIR)
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(GENERATED) -f $(SLICE)
	cmp -s $(GENERATED) $(TRACKED) || \
	  { diff -u $(TRACKED) $(GENERATED); exit 1; }

refresh-extraction:
	@mkdir -p extracted
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(TRACKED) -f $(SLICE)

check: extract
	cd $(REPO_ROOT) && \
	  $(EASYCRYPT) compile $(EASYCRYPT_FLAGS) $(EASYCRYPT_ROOT_INCLUDES) \
	    $(ROOT_PROOF)
