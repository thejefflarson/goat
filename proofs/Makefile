# Build the mechanized development (ADR 0008, issue #70). See README.md.
#
# `make`              regenerate Goat_ott.v from the Ott source, then compile.
# `make gen`          regenerate Goat_ott.v only.
# `make coq`          compile the committed .v files under coqc.
# `make check-admits` fail unless proofs/*.v holds exactly the tracked admits.
# `make ci`           check Ott sync + admit count, then compile.
# `make clean`        remove generated build artifacts.
#
# Tools come from an opam switch (Coq 8.20.1, Ott 0.34, metalib). metalib is on
# Coq's user-contrib path, so no extra -R is needed for it.

OTT         ?= ott
COQMAKEFILE ?= coq_makefile

OTT_SRC   = goat_ln.ott
GEN       = Goat_ott.v
OTT_FLAGS = -coq_lngen true -coq_expand_list_types true

.PHONY: all gen coq ci check-gen check-admits clean

# The allowed admits: the two canonical Hindley-Milner lemmas in GoatSubst.v
# that term substitution (L6a/L6b), preservation, and soundness are derived
# from -- general weakening (typing_weaken, L4) and context-fixing type/row
# substitution (typing_tsubst_fix, L5). Closing them finishes B3 (issue #151).
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

# Frozen-admit guard: "green Coq" stays honest only while the sole admits are
# the two tracked HM lemmas, so the proof can only get MORE complete. Fail if
# the `Admitted.` count in the sources drifts from EXPECTED_ADMITS. When
# typing_weaken / typing_tsubst_fix close (#151), lower the expected count.
check-admits:
	@n=$$(grep -rn '^Admitted\.' *.v | wc -l | tr -d '[:space:]'); \
	if [ "$$n" != "$(EXPECTED_ADMITS)" ]; then \
	  echo "ERROR: proofs/*.v has $$n 'Admitted.' (expected $(EXPECTED_ADMITS))."; \
	  echo "Allowed: typing_weaken (L4) and typing_tsubst_fix (L5) in GoatSubst.v (#151)."; \
	  grep -rn '^Admitted\.' *.v; \
	  exit 1; \
	fi; \
	echo "check-admits: $$n 'Admitted.' in proofs/*.v (expected $(EXPECTED_ADMITS)) -- ok."

ci: check-gen check-admits coq

clean:
	-$(MAKE) -f CoqMakefile clean 2>/dev/null || true
	rm -f CoqMakefile CoqMakefile.conf CoqMakefile.d .coqdeps.d Goat_ott.gen.v
	rm -f *.vo *.vok *.vos *.glob .*.aux
