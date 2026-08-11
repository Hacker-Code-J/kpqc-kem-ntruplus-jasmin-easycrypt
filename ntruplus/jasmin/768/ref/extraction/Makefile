# -*- Makefile -*-

JASMIN2EC ?= /usr/local/bin/jasmin2ec
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-basemul-ec.XXXXXX))
SLICE := jade_ntruplus_ntruplus768_amd64_ref_basemul
NORMAL := $(OUTDIR)/NTRUPlus768Basemul.ec
CT := $(OUTDIR)/NTRUPlus768BasemulCT.ec

.PHONY: all ec ec_ct

all: ec

ec:
	@mkdir -p "$(OUTDIR)"
	$(JASMIN2EC) ../basemul.jazz --array-model=old -o "$(NORMAL)" -f $(SLICE)
	@printf 'easycrypt: %s\n' "$(NORMAL)"

ec_ct:
	@mkdir -p "$(OUTDIR)"
	$(JASMIN2EC) ../basemul.jazz -m CT -o "$(CT)" -f $(SLICE)
	@printf 'easycrypt-ct: %s\n' "$(CT)"
