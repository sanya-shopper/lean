# lean

Two things, done in parallel:

1. **A landscape survey** of the current state of Lean (and adjacent proof
   assistants) formalizing mathematics for *verifying and analyzing SHA-256* —
   differential cryptanalysis, SAT/SMT, and the verified-crypto ecosystem — and a
   map of where individual volunteers *could* contribute. Mapping only; scoping is
   a later decision.
2. **A runnable Lean 4 primer & cookbook** for someone with a math/tech
   background new to the language and to proof assistants.

## Layout

| Path | What it is |
|------|------------|
| `NOTES.md` | The survey: findings from research threads + a ranked contribution-boundary map, including a retrospective (§6) on formalizing what broke MD5/SHA-1. **Start here.** |
| `lean-primer.tex` / `lean-primer.pdf` | **The canonical primer**: a typeset 12-page PDF (source + output). Build/test with `tools/build-primer.sh`. |
| `bibsrc/` | Bibliography source: `lean-refs.bib` + provenance notes (`bibsrc/README.md`). The fetched PDFs themselves live in the sibling tree `../_refs/lean/`. |
| `primer/` | A `lake` project that builds clean on Lean 4.33 with **no mathlib**. |
| `primer/PRIMER.md` | Markdown mirror of the primer (the PDF is canonical). |
| `primer/README.md` | Build/run instructions + cookbook recipes. |
| `primer/Primer/*.lean` | Seven type-checked chapters: `Basics`, `Proofs`, `BitVec` (SHA-256 primitive layer), `Spec` (verify-your-own-code), `Diff` (difference algebra), `Josephus` (a proved closed-form theorem), `Probability` (discrete probability by counting). |
| `mathlib-tour/` | A separate mathlib-backed companion (pinned to mathlib v4.33.0) showing what mathlib buys: `ring`, `Finset` sums, √2 irrational, rational probability. Keeps `primer/` core-only. Its ~6 GB dependency store lives outside the repo in the shared `../_lean-packages/` cache. |
| `site/` | Source for the two published artifact pages. |
| `tools/build-primer.sh` | Builds `lean-primer.pdf` and unit-tests the build (clean LaTeX, references resolved, no `??`). |

## Published artifacts

- **Survey briefing** — the boundary map + ranked contribution areas:
  https://claude.ai/code/artifact/60959a4d-3931-4cbe-981c-ea2cfc9c0787
- **Primer & cookbook** — concept tour + runnable recipes:
  https://claude.ai/code/artifact/10c48786-4472-4763-8f25-1d013d42886e

## Build the primer

```bash
cd primer
lake build                        # type-checks every chapter = checks every proof
lake env lean Primer/Basics.lean  # run one chapter, printing its output
```

## Headline findings (see `NOTES.md` for detail and citations)

- **No cryptographic hash** exists in mathlib / Lean core / Batteries.
- Lean's strongest verified SHA-256 is at the **ZK-circuit** level (`clean`); there
  is **no Lean proof of a software SHA-256 against the FIPS spec** — the Coq/VST
  result from 2015 has no Lean counterpart. (LNSym covers SHA-**512** assembly.)
- **Differential cryptanalysis has never been formalized in any proof assistant.**
  The theory is rigorous-but-paper; the search tools are unverified; SHAttered had
  no machine-checked part.
- Lean's `BitVec` + `bv_decide` (verified bitblasting, LRAT-checked) make it a
  strong *platform* for bit-level crypto proofs, with a real scaling ceiling on
  modular-addition-heavy goals.
- **Top probe** if work is ever scoped: formalize the **Lipmaa–Moriai** algorithm
  for the differential probability of modular addition (`xdp⁺/adp⊕`) — small,
  needs only `BitVec`, and would be a first-of-its-kind machine-checked
  cryptanalysis result.
