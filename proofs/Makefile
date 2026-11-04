# Build the mechanized development (ADR 0008, issue #70). See README.md.
#
# `make`        regenerate Goat_ott.v from the Ott source, then compile.
# `make gen`    regenerate Goat_ott.v only.
# `make coq`    compile the committed .v files under coqc.
# `make ci`     check the committed Goat_ott.v matches the Ott source, compile.
# `make clean`  remove generated build artifacts.
#
# Tools come from an opam switch (Coq 8.20.1, Ott 0.34, metalib). metalib is on
# Coq's user-contrib path, so no extra -R is needed for it.

OTT         ?= ott
COQMAKEFILE ?= coq_makefile

OTT_SRC   = goat_ln.ott
GEN       = Goat_ott.v
OTT_FLAGS = -coq_lngen true -coq_expand_list_types true

.PHONY: all gen coq ci check-gen clean

all: gen coq

gen: $(GEN)

$(GEN): $(OTT_SRC)
	$(OTT) -i $(OTT_SRC) -o $(GEN) $(OTT_FLAGS)

coq: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject $(GEN) GoatProofs.v
	$(COQMAKEFILE) -f _CoqProject -o CoqMakefile

# Reproducibility gate: regenerate into a scratch file and compare. A drift
# here means the committed Goat_ott.v no longer matches goat_ln.ott.
check-gen: $(OTT_SRC)
	$(OTT) -i $(OTT_SRC) -o Goat_ott.gen.v $(OTT_FLAGS)
	@diff -u $(GEN) Goat_ott.gen.v \
	  || { echo "ERROR: $(GEN) is stale; run 'make gen' and commit."; rm -f Goat_ott.gen.v; exit 1; }
	@rm -f Goat_ott.gen.v
	@echo "$(GEN) is in sync with $(OTT_SRC)."

ci: check-gen coq

clean:
	-$(MAKE) -f CoqMakefile clean 2>/dev/null || true
	rm -f CoqMakefile CoqMakefile.conf CoqMakefile.d .coqdeps.d Goat_ott.gen.v
	rm -f *.vo *.vok *.vos *.glob .*.aux
