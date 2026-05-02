.PHONY: build build-lib build-exe check extract

FILE ?= demo/smoke_linear_gentzen.mypa
THEOREM ?= smoke
OUT ?= demo/extracted/$(notdir $(basename $(FILE)))__$(THEOREM).lean
CHECK_ARG := $(word 2,$(MAKECMDGOALS))
EXTRACT_ARG := $(word 2,$(MAKECMDGOALS))

build: build-lib build-exe

build-lib:
	lake build FastProofTheory

build-exe:
	lake build fast-proof-theory

check:
	node proofAssistant/cli.js verify $(if $(CHECK_ARG),$(CHECK_ARG),$(FILE))

extract:
	@if [ "$(EXTRACT_ARG)" = "all" ]; then \
		set -e; \
		mkdir -p demo/extracted; \
		for f in demo/*.mypa; do \
			rg -o '^(def|theorem)\s+([A-Za-z_][A-Za-z0-9_]*)' -r '$$2' "$$f" | while read -r thm; do \
				out="demo/extracted/$$(basename "$${f%.mypa}")__$$thm.lean"; \
				if node proofAssistant/cli.js extract "$$f" "$$thm" -o "$$out" >/dev/null 2>&1; then \
					echo "$$out"; \
				else \
					echo "SKIP $$f $$thm (not extractable with current backend)" >&2; \
				fi; \
			done; \
		done; \
	else \
		mkdir -p $(dir $(OUT)); \
		node proofAssistant/cli.js extract $(FILE) $(THEOREM) -o $(OUT); \
		echo $(OUT); \
	fi

# Allow: make check path/to/file.mypa
%:
	@:
