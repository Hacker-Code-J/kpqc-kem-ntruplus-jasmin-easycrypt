PYTHON ?= python3

.PHONY: all check
all: check

# The complete encapsulation replay checks this encoder and fresh extraction.
check:
	$(PYTHON) ../../../../../tests/ntruplus768/encap_complete/verify_encap_complete.py
