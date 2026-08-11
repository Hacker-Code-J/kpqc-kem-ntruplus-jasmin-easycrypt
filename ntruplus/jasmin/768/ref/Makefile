# -*- Makefile -*-

JASMINC ?= /usr/local/bin/jasminc
JASMINCT ?= /usr/local/bin/jasmin-ct
JASMIN2EC ?= /usr/local/bin/jasmin2ec
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_basemul
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-basemul-asm.XXXXXX))

.PHONY: default asm safety export-info ct sct ec

default: asm

asm:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/basemul.s" basemul.jazz
	@printf 'assembly: %s\n' "$(OUTDIR)/basemul.s"

safety:
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -checksafety -slice $(SLICE) \
	  -o "$(OUTDIR)/basemul-safety.s" basemul.jazz

export-info:
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -print-export-info-json basemul.jazz

ct:
	$(JASMINCT) --slice=$(SLICE) basemul.jazz

sct:
	$(JASMINCT) --slice=$(SLICE) --sct basemul.jazz

ec:
	$(MAKE) -C extraction OUTDIR="$(OUTDIR)" JASMIN2EC="$(JASMIN2EC)"
