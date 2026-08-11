# -*- Makefile -*-

JASMIN2EC ?= jasmin2ec
EASYCRYPT ?= easycrypt
SOURCE := ../../../../jasmin/768/ref/basemul.jazz
SLICE := jade_ntruplus_ntruplus768_amd64_ref_basemul
EXTRACTED := extracted/NTRUPlus768Basemul.ec
PROOF := NTRUPlus768BasemulProof.ec

.PHONY: all extract check

all: check

extract:
	$(JASMIN2EC) $(SOURCE) --array-model=old -o $(EXTRACTED) -f $(SLICE)

check:
	$(EASYCRYPT) compile -no-eco -I extracted $(PROOF)
