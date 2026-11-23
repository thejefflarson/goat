# Build the mechanized development (ADR 0008, issue #70). See README.md.
#
# `make`              regenerate Goat_ott.v from the Ott source, then compile.
# `make gen`          regenerate Goat_ott.v only.
# `make coq`          compile the committed .v files under rocq.
# `make check-admits` fail unless proofs/*.v holds exactly the tracked admits.
# `make gen-grammar`  regenerate GoatGrammar.v from grammar/goat.peg.
# `make check-grammar` fail if GoatGrammar.v is stale against grammar/goat.peg.
# `make check-assumptions` fail unless T1, T2, T3, progress, preservation, soundness, the inference soundness theorem, erase_step, erase_traps, coerce_typing, infer_elab_sound, unroll_eqb_sound, erase_converse, erase_converse_multistep, knot_unrolls, unify_k_sound, coerce_dec_sound, unify_co_sound, infer_guarded, cmp_total, cmp_unerase and the lexer theorems are closed (T1 over text rests on the two Unicode parameters alone).
# `make differential` extract the proven inference algorithm and the lexer, and compare them with the Rust checker and lexer.
# `make ci`           check Ott and grammar sync + admit count, compile, check assumptions, differential.
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
DIFF_DIR  = _differential
CORPUS    = cargo run -q --manifest-path ../Cargo.toml -p goat_checker --example core_corpus
LEXDUMP   = cargo run -q --manifest-path ../Cargo.toml -p goat_parser --example lex_dump

.PHONY: all gen coq ci check-gen check-grammar gen-grammar check-assumptions check-admits differential clean

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

# Every theorem GoatAssumptions.v lists must rest on no axiom and no admit,
# except the lexer's T1 at the Unicode tables (parse_text_denotes_xid), which
# rests on exactly the two declared parameters xid_start_hi and xid_cont_hi.
check-assumptions: coq
	@out=$$(rocq compile -R . Goat GoatAssumptions.v) || { echo "$$out"; exit 1; }; \
	n=$$(echo "$$out" | grep -c '^Closed under the global context'); \
	if [ "$$n" != "27" ]; then \
	  echo "ERROR: expected peg_deterministic, parse_denotes_lc, print_parse_roundtrip, progress, preservation, soundness, infer_closed_sound, erase_step, erase_traps, coerce_typing, infer_elab_sound, unroll_eqb_sound, erase_converse, erase_converse_multistep, knot_unrolls, unify_k_sound, coerce_dec_sound, unify_co_sound, infer_guarded, cmp_total, cmp_unerase, lex_concat, step_longest, word_boundary, parse_text_denotes, edits_preserve_tokens and edits_preserve_parse closed under the global context:"; \
	  echo "$$out"; exit 1; \
	fi; \
	axioms=$$(echo "$$out" | sed -n '/^Axioms:/,$$p' | grep -v '^Axioms:' | sed 's/ :.*//' | sort | tr '\n' ' '); \
	if [ "$$axioms" != "xid_cont_hi xid_start_hi " ]; then \
	  echo "ERROR: parse_text_denotes_xid must rest on exactly xid_start_hi and xid_cont_hi, found: $$axioms"; \
	  echo "$$out"; exit 1; \
	fi; \
	echo "check-assumptions: T1, T2, T3, progress, preservation, soundness, infer_closed_sound, erase_step, erase_traps, coerce_typing, infer_elab_sound, unroll_eqb_sound, erase_converse, erase_converse_multistep, knot_unrolls, unify_k_sound, coerce_dec_sound, unify_co_sound, infer_guarded, cmp_total, cmp_unerase, lex_concat, step_longest, word_boundary, parse_text_denotes, edits_preserve_tokens and edits_preserve_parse are closed, and the lexer's T1 at the Unicode tables rests on xid_start_hi and xid_cont_hi alone -- ok."

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

# The proven algorithm is tied to the Rust checker by running both on the same
# programs (ADR 0037, decision 6; differential/README.md).
differential: coq
	rm -rf $(DIFF_DIR)
	mkdir $(DIFF_DIR)
	cd $(DIFF_DIR) && rocq compile -R .. Goat ../GoatExtract.v
	cp ../differential/driver.ml $(DIFF_DIR)/
	cd $(DIFF_DIR) && ocamlfind ocamlopt -w -a goat_infer.mli goat_infer.ml driver.ml -o driver
	$(CORPUS) > $(DIFF_DIR)/corpus.tsv
	$(DIFF_DIR)/driver $(DIFF_DIR)/corpus.tsv
	cd $(DIFF_DIR) && rocq compile -R .. Goat ../GoatLexExtract.v
	cp ../differential/lex_driver.ml $(DIFF_DIR)/
	cd $(DIFF_DIR) && ocamlfind ocamlopt -w -a goat_lex.mli goat_lex.ml lex_driver.ml -o lex_driver
	$(CORPUS) -- --sources | $(LEXDUMP) > $(DIFF_DIR)/lex.tsv
	$(DIFF_DIR)/lex_driver $(DIFF_DIR)/lex.tsv

ci: check-gen check-grammar check-admits coq check-assumptions differential

clean:
	-$(MAKE) -f CoqMakefile clean 2>/dev/null || true
	rm -f CoqMakefile CoqMakefile.conf CoqMakefile.d .coqdeps.d Goat_ott.gen.v GoatGrammar.gen.v
	rm -f *.vo *.vok *.vos *.glob .*.aux
	rm -rf $(DIFF_DIR)
