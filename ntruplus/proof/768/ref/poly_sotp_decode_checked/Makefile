PYTHON ?= python3

.PHONY: all check
all: check

# The composed replay also checks the standalone decoder and fresh extraction.
check:
	$(PYTHON) ../../../../../tests/ntruplus768/decap_message/verify_decap_message.py
