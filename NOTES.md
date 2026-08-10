# Lean formalization of SHA-256 analysis — landscape survey

Goal: map the current state of formalization (primarily Lean 4 / mathlib and
adjacent ecosystems) for mathematics relevant to *verifying and analyzing*
SHA-256, including:

- functional-correctness formalizations of SHA-256 itself,
- differential cryptanalysis (theory and machine-checked instances),
- satisfiability (SAT/SMT) tooling inside proof assistants, especially
  bit-vector reasoning usable on hash-function circuits,
- related fields (verified crypto implementations, symbolic/computational
  security proofs, verified SAT proof checking).

Then: identify the contribution boundary — what exists, what is missing, and
which gaps are tractable for individual volunteers.

Status: survey in progress (2026-08-10). Findings will be recorded below as
they come in, then synthesized into a contribution-opportunities section.

## Research threads

1. SHA-2 family in Lean 4 / mathlib and the wider Lean ecosystem.
2. Differential cryptanalysis: any machine-checked formalization anywhere
   (Lean, Coq/Rocq, Isabelle, EasyCrypt), plus the unformalized paper trail
   (Wang et al., De Cannière–Rechberger, Mendel et al., Stevens et al.).
3. SAT in Lean: `bv_decide` / LeanSAT, LRAT checking, external solver
   integration; state of SAT-based SHA-256 preimage/collision search.
4. Adjacent verified-crypto ecosystems (HACL*/F*, SAW/Cryptol, Jasmin/
   EasyCrypt, Isabelle CryptHOL, Coq/Rocq FCF) — where the boundary sits.

## Findings

(to be filled in)

## Contribution boundary and open areas

(to be filled in)
