# Build the mechanized development (ADR 0008, issue #70). See README.md.
#
# `make`              regenerate Goat_ott.v from the Ott source, then compile.
# `make gen`          regenerate Goat_ott.v only.
# `make coq`          compile the committed .v files under rocq.
# `make check-admits` fail unless proofs/*.v holds exactly the tracked admits.
# `make gen-grammar`  regenerate GoatGrammar.v from grammar/goat.peg.
# `make check-grammar` fail if GoatGrammar.v is stale against grammar/goat.peg.
# `make check-assumptions` fail unless T1, T2 and T3 are closed under the global context.
# `make ci`           check Ott and grammar sync + admit count, compile, check assumptions.
# `make clean`        remove generated build artifacts.
#
# Tools come from an opam switch (Rocq 9.1.1, Ott 0.34, metalib). metalib is on
# Coq's user-contrib path, so no extra -R is needed for it.

OTT         ?= ott
COQMAKEFILE ?= rocq makefile

OTT_SRC   = goat_ln.ott
GEN       = Goat_ott.v
GRAMMAR   = GoatGrammar.v
EMIT      = cargo run -q --manifest-path ../Cargo.toml -p goat_parser --example emit_coq
OTT_FLAGS = -coq_lngen true -coq_expand_list_types true

.PHONY: all gen coq ci check-gen check-grammar gen-grammar check-assumptions check-admits clean

# No admits are allowed: every proof in proofs/*.v must be closed.
EXPECTED_ADMITS = 0

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

# The grammar enters Coq by generation, never by hand (ADR 0030). A drift here
# means GoatGrammar.v no longer matches grammar/goat.peg.
gen-grammar:
	$(EMIT) > $(GRAMMAR)

check-grammar: ../grammar/goat.peg
	$(EMIT) > GoatGrammar.gen.v
	@diff -u $(GRAMMAR) GoatGrammar.gen.v \
	  || { echo "ERROR: $(GRAMMAR) is stale; run 'make gen-grammar' and commit."; rm -f GoatGrammar.gen.v; exit 1; }
	@rm -f GoatGrammar.gen.v
	@echo "$(GRAMMAR) is in sync with grammar/goat.peg."

# T1, T2 and T3 must rest on no axiom and no admit.
check-assumptions: coq
	@out=$$(rocq compile -R . Goat GoatAssumptions.v) || { echo "$$out"; exit 1; }; \
	n=$$(echo "$$out" | grep -c '^Closed under the global context'); \
	if [ "$$n" != "3" ]; then \
	  echo "ERROR: expected peg_deterministic, parse_denotes_lc and print_parse_roundtrip closed under the global context:"; \
	  echo "$$out"; exit 1; \
	fi; \
	echo "check-assumptions: peg_deterministic, parse_denotes_lc and print_parse_roundtrip are closed -- ok."

# Frozen-admit guard: fail if the `Admitted.` count in the sources drifts from
# EXPECTED_ADMITS, so a green proof build never hides an open lemma.
check-admits:
	@n=$$(grep -rn '^Admitted\.' *.v | wc -l | tr -d '[:space:]'); \
	if [ "$$n" != "$(EXPECTED_ADMITS)" ]; then \
	  echo "ERROR: proofs/*.v has $$n 'Admitted.' (expected $(EXPECTED_ADMITS))."; \
	  grep -rn '^Admitted\.' *.v; \
	  exit 1; \
	fi; \
	echo "check-admits: $$n 'Admitted.' in proofs/*.v (expected $(EXPECTED_ADMITS)) -- ok."

ci: check-gen check-grammar check-admits coq check-assumptions

clean:
	-$(MAKE) -f CoqMakefile clean 2>/dev/null || true
	rm -f CoqMakefile CoqMakefile.conf CoqMakefile.d .coqdeps.d Goat_ott.gen.v GoatGrammar.gen.v
	rm -f *.vo *.vok *.vos *.glob .*.aux
