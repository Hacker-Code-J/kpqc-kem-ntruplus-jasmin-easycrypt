# -*- Makefile -*-

EASYCRYPT ?= easycrypt
ALGEBRA_PROOF := NTRUPlus768PolyFromBytesAlgebra.ec
CANONICAL_PROOF ?= NTRUPlus768CanonicalDecoder.ec
BASEMUL_PROOF := ../basemul
BASEMUL_EXTRACTED := ../basemul/extracted
POLY_BASEMUL := ../poly_basemul
POLY_BASEMUL_EXTRACTED := ../poly_basemul/extracted
POLY_BASEMUL_INVNTT := ../poly_basemul_invntt
NTT_SCHEDULE := ../ntt_schedule
NTT_RADIX2_64 := ../ntt_radix2_64
NTT_RADIX2_64_EXTRACTED := ../ntt_radix2_64/extracted
INVNTT_RADIX2_4 := ../invntt_radix2_4
INVNTT_RADIX2_4_EXTRACTED := ../invntt_radix2_4/extracted
INVNTT_RADIX2_8 := ../invntt_radix2_8
INVNTT_RADIX2_8_EXTRACTED := ../invntt_radix2_8/extracted
INVNTT_RADIX2_16 := ../invntt_radix2_16
INVNTT_RADIX2_16_EXTRACTED := ../invntt_radix2_16/extracted
INVNTT_RADIX2_32 := ../invntt_radix2_32
INVNTT_RADIX2_32_EXTRACTED := ../invntt_radix2_32/extracted
INVNTT_RADIX2_64 := ../invntt_radix2_64
INVNTT_RADIX2_64_EXTRACTED := ../invntt_radix2_64/extracted
INVNTT_RADIX3 := ../invntt_radix3
INVNTT_RADIX3_EXTRACTED := ../invntt_radix3/extracted
INVNTT_FINAL := ../invntt_final
INVNTT_FINAL_EXTRACTED := ../invntt_final/extracted
INVNTT := ../invntt
INVNTT_EXTRACTED := ../invntt/extracted
FORMOSA_ARRAYS := ../../../../../external/formosa-mlkem/crypto-specs/arrays
FORMOSA_ECLIB := ../../../../../external/formosa-mlkem/proof/eclib
FORMOSA_COMMON := ../../../../../external/formosa-mlkem/crypto-specs/common
EASYCRYPT_INCLUDES := -I . -I $(BASEMUL_PROOF) -I $(BASEMUL_EXTRACTED) -I $(POLY_BASEMUL) -I $(POLY_BASEMUL_EXTRACTED) -I $(POLY_BASEMUL_INVNTT) -I $(NTT_RADIX2_64) -I $(NTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX2_4) -I $(INVNTT_RADIX2_4_EXTRACTED) -I $(INVNTT_RADIX2_8) -I $(INVNTT_RADIX2_8_EXTRACTED) -I $(INVNTT_RADIX2_16) -I $(INVNTT_RADIX2_16_EXTRACTED) -I $(INVNTT_RADIX2_32) -I $(INVNTT_RADIX2_32_EXTRACTED) -I $(INVNTT_RADIX2_64) -I $(INVNTT_RADIX2_64_EXTRACTED) -I $(INVNTT_RADIX3) -I $(INVNTT_RADIX3_EXTRACTED) -I $(INVNTT_FINAL) -I $(INVNTT_FINAL_EXTRACTED) -I $(INVNTT) -I $(INVNTT_EXTRACTED) -I $(NTT_SCHEDULE) -I $(FORMOSA_ARRAYS) -I $(FORMOSA_ECLIB) -I $(FORMOSA_COMMON)

.PHONY: all check check-canonical

all: check check-canonical

check:
	$(EASYCRYPT) compile -no-eco $(EASYCRYPT_INCLUDES) $(ALGEBRA_PROOF)

.PHONY: check-model-compatibility
check-model-compatibility:
	python3 ../../../../../tests/ntruplus768/toolchain/check_model_compatibility.py --source-only

check: check-model-compatibility

# Official-target validation arithmetic; C/Jasmin binding is a separate obligation.
check-canonical: check-model-compatibility
	@set -eu; \
	tmp=$$(mktemp -d); \
	trap 'rm -rf "$$tmp"' EXIT; \
	if grep -En '(^|[^[:alnum:]_])(axiom|admit|admitted|assume|sorry|abort|pragma)([^[:alnum:]_]|$$)' "$(CANONICAL_PROOF)"; then exit 1; fi; \
	cat "$(CANONICAL_PROOF)" > "$$tmp/NTRUPlus768CanonicalDecoder.ec"; \
	printf '%s\n' \
	  '' \
	  'lemma canonical_decoder_eof_guard a0 :' \
	  '  phoare [CanonicalCheck.run : a = a0 ==>' \
	  '    (res = 0 <=> forall j, 0 <= j < 768 => W16.to_uint (decoded_poly a0).[j] < 3457) /\ (res = 0 \/ res = 1)] = 1%r.' \
	  'proof. exact (canonical_check_success a0). qed.' \
	  'lemma canonical_roundtrip_eof_guard p :' \
	  '  NTRUPlus768PolyToBytesAlgebra.poly_tobytes_input_qrange p =>' \
	  '  phoare [CanonicalCheck.run : a = NTRUPlus768PolyToBytesAlgebra.poly_tobytes_spec p ==> res = 0] = 1%r.' \
	  'proof. exact (canonical_check_tobytes_success p). qed.' \
	  >> "$$tmp/NTRUPlus768CanonicalDecoder.ec"; \
	$(EASYCRYPT) compile -pragmas Proofs:check -no-eco -p Z3 -timeout 30 -max-provers 1 \
	  -I Jasmin:../../../compat/jasmin $(EASYCRYPT_INCLUDES) \
	  -I ../poly_tobytes -I ../poly_tobytes/extracted "$$tmp/NTRUPlus768CanonicalDecoder.ec"
