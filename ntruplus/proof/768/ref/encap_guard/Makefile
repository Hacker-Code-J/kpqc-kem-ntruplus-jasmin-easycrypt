PYTHON ?= python3

.PHONY: all check
all: check

# Strict replay binds Jasmin extraction, proof mains and C ABI tests.
check:
	$(PYTHON) ../../../../../tests/ntruplus768/encap_guard/verify_encap_guard.py
