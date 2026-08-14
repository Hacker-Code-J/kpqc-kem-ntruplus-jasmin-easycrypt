# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
JASMIN_SOURCE := $(JASMIN_DIR)/crepmod3.jazz
POLY_SOURCE := ../../../NTRU+/NTRU+768/poly.c
KEM_SOURCE := ../../../NTRU+/NTRU+768/kem.c
CHECKER := check_crepmod3.py
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
SLICE := jade_ntruplus_ntruplus768_amd64_ref_poly_crepmod3
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-crepmod3-test.XXXXXX))

.PHONY: check selfcheck ccheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --poly-source "$(POLY_SOURCE)" --kem-source "$(KEM_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --poly-source "$(POLY_SOURCE)" --kem-source "$(KEM_SOURCE)" --jasmin-source "$(JASMIN_SOURCE)"

ccheck:
	$(CC) $(CFLAGS) -c crepmod3_diff.c -o /tmp/crepmod3_diff.o
	$(CC) $(CFLAGS) -c "$(POLY_SOURCE)" -o /tmp/crepmod3_c_ref.o

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/crepmod3.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/crepmod3.s" -o "$(OUTDIR)/crepmod3.o"
	$(CC) $(CFLAGS) crepmod3_diff.c "$(POLY_SOURCE)" "$(OUTDIR)/crepmod3.o" \
		$(LDFLAGS) -o "$(OUTDIR)/crepmod3_diff"
	"$(OUTDIR)/crepmod3_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(SLICE) -o "$(OUTDIR)/crepmod3.s" "$(JASMIN_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/crepmod3.s" -o "$(OUTDIR)/crepmod3.o"
	$(CC) $(CFLAGS) $(SANFLAGS) crepmod3_diff.c "$(POLY_SOURCE)" "$(OUTDIR)/crepmod3.o" \
		$(LDFLAGS) -o "$(OUTDIR)/crepmod3_diff_ubsan"
	"$(OUTDIR)/crepmod3_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
