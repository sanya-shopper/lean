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
| `NOTES.md` | The survey: findings from four research threads + a ranked contribution-boundary map. **Start here.** |
| `primer/` | A `lake` project that builds clean on Lean 4.33 with **no mathlib**. |
| `primer/PRIMER.md` | Conceptual primer — Lean vs TLA+ vs Haskell, the proof experience, where Lean fits for verifying your own code. |
| `primer/README.md` | Build/run instructions + cookbook recipes. |
| `primer/Primer/*.lean` | Four type-checked chapters: `Basics`, `Proofs`, `BitVec` (SHA-256 primitive layer), `Spec` (verify-your-own-code workflow). |
| `site/` | Source for the two published artifact pages. |

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
