# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
CHECKER := check_keygen_sampler.py
DRIVER := keygen_sampler_driver.c
POLY_SOURCE := ../../../NTRU+/NTRU+768/poly.c
NTT_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
POLY_HEADER := ../../../NTRU+/NTRU+768/poly.h
PARAMS_HEADER := ../../../NTRU+/NTRU+768/params.h
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-keygen-sampler-test.XXXXXX))

.PHONY: all check selfcheck run ubsan clean

all: check selfcheck run ubsan

check:
	$(PYTHON) $(CHECKER) \
		--params-header "$(PARAMS_HEADER)" \
		--poly-header "$(POLY_HEADER)" \
		--poly-source "$(POLY_SOURCE)" \
		--kem-source "$(KEM_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check \
		--params-header "$(PARAMS_HEADER)" \
		--poly-header "$(POLY_HEADER)" \
		--poly-source "$(POLY_SOURCE)" \
		--kem-source "$(KEM_SOURCE)"

run:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) $(DRIVER) "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) -o "$(OUTDIR)/keygen_sampler_driver"
	"$(OUTDIR)/keygen_sampler_driver"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan:
	@mkdir -p "$(OUTDIR)"
	$(CC) $(CFLAGS) $(SANFLAGS) $(DRIVER) "$(POLY_SOURCE)" "$(NTT_SOURCE)" $(LDFLAGS) -o "$(OUTDIR)/keygen_sampler_driver_ubsan"
	"$(OUTDIR)/keygen_sampler_driver_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	rm -rf "$(OUTDIR)"
