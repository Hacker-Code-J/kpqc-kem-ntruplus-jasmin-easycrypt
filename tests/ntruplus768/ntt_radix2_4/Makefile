# -*- Makefile -*-

CC ?= /usr/bin/gcc
PYTHON ?= python3
CFLAGS ?= -Wall -Wextra -Werror -O2 -g -ffunction-sections -fdata-sections
LDFLAGS ?= -Wl,--gc-sections
SANFLAGS ?= -fsanitize=undefined -fno-sanitize-recover=undefined
JASMIN_DIR := ../../../ntruplus/jasmin/768/ref
RADIX2_4_SOURCE := $(JASMIN_DIR)/ntt_radix2_4.jazz
RADIX2_8_SOURCE := $(JASMIN_DIR)/ntt_radix2_8.jazz
RADIX2_16_SOURCE := $(JASMIN_DIR)/ntt_radix2_16.jazz
RADIX2_32_SOURCE := $(JASMIN_DIR)/ntt_radix2_32.jazz
RADIX2_64_SOURCE := $(JASMIN_DIR)/ntt_radix2_64.jazz
RADIX3_SOURCE := $(JASMIN_DIR)/ntt_radix3.jazz
STAGE1_SOURCE := $(JASMIN_DIR)/ntt_stage1.jazz
C_SOURCE := ../../../NTRU+/NTRU+768/ntt.c
CHECKER := check_ntt_radix2_4.py
JASMINC ?= /usr/local/bin/jasminc
JFLAGS ?= -arch x86-64 -call-conv linux -system linux
RADIX2_4_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4
RADIX2_8_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_8
RADIX2_16_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_16
RADIX2_32_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_32
RADIX2_64_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_64
RADIX3_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_radix3
STAGE1_SLICE := jade_ntruplus_ntruplus768_amd64_ref_ntt_stage1
OUTDIR := $(if $(OUTDIR),$(OUTDIR),$(shell mktemp -d /tmp/ntruplus768-ntt-radix2-4-test.XXXXXX))

.PHONY: check selfcheck run ubsan clean

check:
	$(PYTHON) $(CHECKER) --c-source "$(C_SOURCE)" --jasmin-source "$(RADIX2_4_SOURCE)"

selfcheck:
	$(PYTHON) $(CHECKER) --self-check --c-source "$(C_SOURCE)" --jasmin-source "$(RADIX2_4_SOURCE)"

run: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_4_SLICE) -o "$(OUTDIR)/ntt_radix2_4.s" "$(RADIX2_4_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_8_SLICE) -o "$(OUTDIR)/ntt_radix2_8.s" "$(RADIX2_8_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_16_SLICE) -o "$(OUTDIR)/ntt_radix2_16.s" "$(RADIX2_16_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_32_SLICE) -o "$(OUTDIR)/ntt_radix2_32.s" "$(RADIX2_32_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_64_SLICE) -o "$(OUTDIR)/ntt_radix2_64.s" "$(RADIX2_64_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX3_SLICE) -o "$(OUTDIR)/ntt_radix3.s" "$(RADIX3_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(STAGE1_SLICE) -o "$(OUTDIR)/ntt_stage1.s" "$(STAGE1_SOURCE)"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_radix2_4.s" -o "$(OUTDIR)/ntt_radix2_4.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_radix2_8.s" -o "$(OUTDIR)/ntt_radix2_8.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_radix2_16.s" -o "$(OUTDIR)/ntt_radix2_16.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_radix2_32.s" -o "$(OUTDIR)/ntt_radix2_32.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_radix2_64.s" -o "$(OUTDIR)/ntt_radix2_64.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_radix3.s" -o "$(OUTDIR)/ntt_radix3.o"
	$(CC) $(CFLAGS) -c "$(OUTDIR)/ntt_stage1.s" -o "$(OUTDIR)/ntt_stage1.o"
	$(CC) $(CFLAGS) ntt_radix2_4_diff.c "$(OUTDIR)/ntt_radix2_4.o" \
		"$(OUTDIR)/ntt_radix2_8.o" "$(OUTDIR)/ntt_radix2_16.o" \
		"$(OUTDIR)/ntt_radix2_32.o" "$(OUTDIR)/ntt_radix2_64.o" \
		"$(OUTDIR)/ntt_radix3.o" "$(OUTDIR)/ntt_stage1.o" \
		$(LDFLAGS) -o "$(OUTDIR)/ntt_radix2_4_diff"
	"$(OUTDIR)/ntt_radix2_4_diff"
	@printf 'test-outdir: %s\n' "$(OUTDIR)"

ubsan: check
	@mkdir -p "$(OUTDIR)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_4_SLICE) -o "$(OUTDIR)/ntt_radix2_4.s" "$(RADIX2_4_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_8_SLICE) -o "$(OUTDIR)/ntt_radix2_8.s" "$(RADIX2_8_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_16_SLICE) -o "$(OUTDIR)/ntt_radix2_16.s" "$(RADIX2_16_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_32_SLICE) -o "$(OUTDIR)/ntt_radix2_32.s" "$(RADIX2_32_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX2_64_SLICE) -o "$(OUTDIR)/ntt_radix2_64.s" "$(RADIX2_64_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(RADIX3_SLICE) -o "$(OUTDIR)/ntt_radix3.s" "$(RADIX3_SOURCE)"
	$(JASMINC) $(JFLAGS) -slice $(STAGE1_SLICE) -o "$(OUTDIR)/ntt_stage1.s" "$(STAGE1_SOURCE)"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_radix2_4.s" -o "$(OUTDIR)/ntt_radix2_4.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_radix2_8.s" -o "$(OUTDIR)/ntt_radix2_8.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_radix2_16.s" -o "$(OUTDIR)/ntt_radix2_16.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_radix2_32.s" -o "$(OUTDIR)/ntt_radix2_32.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_radix2_64.s" -o "$(OUTDIR)/ntt_radix2_64.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_radix3.s" -o "$(OUTDIR)/ntt_radix3.o"
	$(CC) $(CFLAGS) $(SANFLAGS) -c "$(OUTDIR)/ntt_stage1.s" -o "$(OUTDIR)/ntt_stage1.o"
	$(CC) $(CFLAGS) $(SANFLAGS) ntt_radix2_4_diff.c "$(OUTDIR)/ntt_radix2_4.o" \
		"$(OUTDIR)/ntt_radix2_8.o" "$(OUTDIR)/ntt_radix2_16.o" \
		"$(OUTDIR)/ntt_radix2_32.o" "$(OUTDIR)/ntt_radix2_64.o" \
		"$(OUTDIR)/ntt_radix3.o" "$(OUTDIR)/ntt_stage1.o" \
		$(LDFLAGS) -o "$(OUTDIR)/ntt_radix2_4_diff_ubsan"
	"$(OUTDIR)/ntt_radix2_4_diff_ubsan"
	@printf 'ubsan-outdir: %s\n' "$(OUTDIR)"

clean:
	@true
