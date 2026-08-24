# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
CHECKER := check_encap_poly_basemul_add.py
VECTORS := check_encap_poly_basemul_add_vectors.py
DRIVER := encap_poly_basemul_add_driver.c
POLY_SOURCE := ../../../NTRU+/NTRU+768/poly.c
NTT_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
POLY_HEADER := ../../../NTRU+/NTRU+768/poly.h
NTT_HEADER := ../../../NTRU+/NTRU+768/ntt.h
PARAMS_HEADER := ../../../NTRU+/NTRU+768/params.h
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-encap-poly-basemul-add-test.XXXXXX))

.PHONY: all check selfcheck run ubsan clean

all: check selfcheck run ubsan

check:
	$(PYTHON) $(CHECKER) \
		--params-header "$(PARAMS_HEADER)" \
		--ntt-header "$(NTT_HEADER)" \
		--poly-header "$(POLY_HEADER)" \
		--ntt-source "$(NTT_SOURCE)" \
		--poly-source "$(POLY_SOURCE)" \
		--kem-source "$(KEM_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
		--params-header "$(PARAMS_HEADER)" \
		--ntt-header "$(NTT_HEADER)" \
		--poly-header "$(POLY_HEADER)" \
		--ntt-source "$(NTT_SOURCE)" \
		--poly-source "$(POLY_SOURCE)" \
		--kem-source "$(KEM_SOURCE)"

run:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) $(DRIVER) "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) -o "$(OUTDIR)/encap_poly_basemul_add_driver"
	$(PYTHON) $(VECTORS) --driver "$(OUTDIR)/encap_poly_basemul_add_driver" --ntt-source "$(NTT_SOURCE)"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) $(SANFLAGS) $(DRIVER) "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) -o "$(OUTDIR)/encap_poly_basemul_add_driver_ubsan"
	$(PYTHON) $(VECTORS) --driver "$(OUTDIR)/encap_poly_basemul_add_driver_ubsan" --ntt-source "$(NTT_SOURCE)"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	rm -rf "$(OUTDIR)"
