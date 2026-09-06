.DEFAULT_GOAL := all

ROCQ ?= rocq
OCAMLC ?= ocamlc

.PHONY: all rocq extract ocaml demo check clean help

all: rocq

Makefile.rocq: _CoqProject
	$(ROCQ) makefile -f _CoqProject -o $@

rocq: Makefile.rocq
	$(MAKE) --no-print-directory -f Makefile.rocq all

# Always regenerate extraction products, including after their removal.
# ExtractDILLref.v is deliberately separate from the reusable library build.
# Extraction must stay first-order: a residual Obj.magic means an index or
# proof leaked into the executable representation.
extract: rocq
	mkdir -p ocaml/generated
	$(ROCQ) compile -Q theories DILLref theories/ExtractDILLref.v
	@if grep -q 'Obj.magic' ocaml/generated/dillref.ml; then \
		echo 'error: extraction introduced Obj.magic'; exit 1; \
	fi

ocaml: extract
	mkdir -p _build
	$(OCAMLC) -c -o _build/dillref.cmi ocaml/generated/dillref.mli
	$(OCAMLC) -I _build -c -o _build/dillref.cmo ocaml/generated/dillref.ml
	$(OCAMLC) -I _build -c -o _build/main.cmo ocaml/main.ml
	$(OCAMLC) -I _build -o _build/dillref _build/dillref.cmo _build/main.cmo

demo: ocaml
	./_build/dillref

check: demo

clean:
	@if test -f Makefile.rocq; then $(MAKE) --no-print-directory -f Makefile.rocq clean; fi
	rm -f Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
	rm -f theories/.*.aux theories/ExtractDILLref.vo theories/ExtractDILLref.vos theories/ExtractDILLref.vok theories/ExtractDILLref.glob
	rm -f ocaml/generated/dillref.ml ocaml/generated/dillref.mli
	rm -rf _build

help:
	@printf '%s\n' 'make          Build the Rocq library and examples' 'make extract  Extract the tool into OCaml' 'make demo     Build and run the OCaml tool on the bundled examples' 'make check    Compile proofs and run the OCaml checks' 'make clean    Remove generated files'
