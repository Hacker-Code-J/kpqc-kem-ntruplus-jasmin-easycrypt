# -*- Makefile -*-

PYTHON ?= python3
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
CHECKER := check_decap_r2_tobytes.py

.PHONY: all check selfcheck clean

all: check selfcheck

check:
	$(PYTHON) $(CHECKER) --kem-source "$(KEM_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --kem-source "$(KEM_SOURCE)"

clean:
	@true
