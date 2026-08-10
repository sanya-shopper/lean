# Lean formalization of SHA-256 analysis — landscape survey

Survey date: **2026-08-10**. Method: four parallel research passes (web search +
source/repo inspection) plus local Lean experiments in `primer/`. Findings are
labelled where confidence varies. Boundary and contribution ideas are in the
final section.

**Reading guide.** Two distinct activities get conflated in "verifying SHA-256":
- **Correctness/security verification** — proving an *implementation* matches the
  FIPS 180-4 spec, or a *construction* is secure under an assumption. Mature,
  industrial, spans many tools.
- **Cryptanalysis / analysis** — reasoning about *attacks*: differential
  characteristics, collision search, probability bounds. Essentially **not
  formalized anywhere**, in any proof assistant. This is where the open ground is.

---

## 1. SHA-2 in Lean 4 / mathlib and the wider Lean ecosystem

**mathlib / core / Batteries: nothing.** No SHA-2, SHA-3, MD5, or any
cryptographic hash — and no abstract "cryptographic hash function" definition
(collision resistance etc.). Confirmed by direct GitHub code search; mathlib has
no `Crypto` directory. Executable crypto is out of mathlib's scope by policy.

**The `BitVec` primitive layer is mature — this is where Lean is now strong.**
`BitVec n` lives in Lean *core* (moved out of Std in 2024): `rotateLeft`/
`rotateRight`, shifts, `&&& ||| ^^^ ~~~`, and `+`/`*` that are modular by
construction — exactly SHA-256's operation set — with a large lemma library
whose growth was driven substantially by AWS's LNSym needs. Verified locally in
`primer/Primer/BitVec.lean` (SHA-256's `Ch`/`Maj`/`Sigma0/1`/`sigma0/1` are a
few lines each and evaluate correctly).

**`bv_decide`** (shipped in Lean **v4.12.0**, Oct 2024; author Henrik Böving et
al.; OOPSLA 2025 paper, doi 10.1145/3763167): verified bit-blasting to an AIG,
bundled CaDiCaL SAT solver, LRAT certificate replayed by a Lean-verified checker.
Dispatches SHA rotr/Ch/Maj/Sigma identities over *all* `BitVec 32` instantly.
(See §3.)

**Standalone SHA-256 in Lean: many executable specs, almost no correctness
proofs.** Key artifacts:

- **Verified-zkEVM/`clean`** (zkSecurity; MIT; very active, 172★) — a ZK-circuit
  DSL containing a **full bit-level SHA-256 compression circuit gadget suite**
  (`Clean/Gadgets/SHA256/`: And32, Xor32, Ch32, Maj32, all four sigmas, Add32,
  schedule, round, compress), **proven sound/complete against a Lean SHA-256 spec
  `Clean/Specs/SHA256.lean`**. *The most substantial verified-SHA-256 artifact in
  the ecosystem* — but it verifies a **circuit**, not general software.
- **leanprover/LNSym** (AWS; Apache-2.0; active, 116★) — Armv8 machine-code
  symbolic simulator. Proves the **SHA-512** Arm assembly (`sha512_block_armv8`)
  correct against a Lean spec (`Specs/SHA512.lean`, `Proofs/SHA512/…`), using
  `bv_decide`/`bv_check` on real 64-bit hash lemmas. **SHA-256 is NOT covered —
  only SHA-512.** Closest thing to the Coq/VST style in Lean.
- **ethereum/cryptography-specs** (EF; CC0; active) — clean executable FIPS 180-4
  SHA-256 spec (`EthCryptographySpecs/Bls/Sha256.lean`) for hash-to-curve/KZG.
  Spec only, no SHA-256 correctness theorems.
- **eKisNonos/sha256-gf2-r1cs** — Lean-kernel-checked soundness/completeness/cost
  of a SHA-256 compression **R1CS-over-GF(2) circuit** (zk-golf record). Narrow
  but real machine-checked SHA-256 content.
- **zksecurity/zk-golf-challenges** — SHA-256 + RSASSA-PKCS1-SHA256 challenge
  instances, solutions are kernel-checked R1CS circuits.
- **Executable-only / light-proof**: etheorem/LeanSha256 (CAVP vectors, kernel-
  reducible), leanprover/KLR `Util/SHA256.lean`, katzenpost/CryptWalker,
  unbalancedparentheses/lean4-baremetal (`bv_decide` sub-op proofs + test
  vectors), gdncc/Cryptography (**SHA-3 only**, NCC Group, ePrint 2024/1880),
  many blockchain repos with copy-paste specs.
- **Caution**: SentinelOps-CI/lean-toolchain advertises "proven correct" but the
  theorems are size/shape lemmas only, not functional correctness.
- **Adjacent tooling**: Aeneas/Charon (Rust→Lean) + MSR SymCrypt verified
  **SHA-3 + ML-KEM** (not SHA-2, MSR blog Jul 2026); spitters/libcrux-lean-specs
  (hax-extracted SHA-256/HMAC/HKDF specs).

**Comparison to other proof assistants (verified *implementations*):**
- **Coq/Rocq — far ahead since 2015.** Appel, "Verification of a Cryptographic
  Primitive: SHA-256" (TOPLAS 2015): full functional correctness of **OpenSSL's
  C SHA-256** via VST/CompCert vs a FIPS 180-4 spec; extended to HMAC / HMAC-DRBG.
  *This exact result has no Lean counterpart.*
- **F\*/HACL\*** — verified SHA-2 (incl. vectorized): functional correctness +
  memory safety + secret independence, shipping in Firefox NSS, Linux kernel,
  and **CPython `hashlib` since 3.12**.
- **Cryptol/SAW** — AWS-LC SHA-2 proofs in CI (SHA-384/512); OpenSSL SHA-256 via
  SAW attempted (NFM 2021) but hit SMT scalability limits.
- **Isabelle** — thin on concrete hashes (RIPEMD-160 SPARK is the notable item);
  CryptHOL treats hashes abstractly.

**Net:** Lean **lags** Coq/F\*/SAW on verified hash *implementations*, but its
2024–26 `BitVec`+`bv_decide`+LNSym stack is arguably the best *platform* for
bit-level crypto proofs among ITPs. The strongest Lean SHA-256 result today is at
the **circuit** level (`clean`), not the software-implementation level.

---

## 2. Differential cryptanalysis: formalization status

**Bottom line: differential cryptanalysis has never been formalized in any
general-purpose proof assistant** (Lean, Coq/Rocq, Isabelle, EasyCrypt). No
machine-checked theorems about differential probability, characteristics, DDTs,
or attack advantage exist as of 2026. What exists is a spectrum:

- **[Rigorous paper, not machine-checked]** the whole classical theory:
  Nyberg–Knudsen provable-security-against-DC bounds (CRYPTO'92); Lipmaa–Moriai
  log-time algorithm for differential probability of modular addition (xdp⁺,
  adp⊕; FSE 2001); De Cannière–Rechberger signed-bit / generalized-condition
  notation for SHA-1 paths (ASIACRYPT 2006); Beyne–Rijmen "DC in the Fixed-Key
  Model" / quasidifferential trails (CRYPTO 2022, explaining why some paper
  characteristics are *wrong*).
- **[Tool, unverified]** search tools that *find* characteristics: CryptoSMT
  (Kölbl), Mouha–Preneel SAT framework, MILP/CP approaches, CASCADA/CLAASP,
  "SHA-256 Collision Attack with Programmatic SAT" (arXiv 2406.20072).
- **[Tool, verification-oriented but still unverified internally]** **AutoDiVer**
  (ToSC 2025, ePrint 2025/185) — checks the *correctness of published
  differential characteristics* via CNF + approximate model counting, catching
  wrong probability claims. The closest thing to "machine-checked cryptanalysis,"
  but its own encoding/counter are not formally verified.
- **[Formal semantics, DSL]** **EasyBC** (POPL 2024) — a block-cipher DSL with a
  "differential denotational semantics" that auto-generates MILP models to *bound
  resistance* to DC. Formal-methods-flavored, but a compiler/analysis tool, not a
  proof-assistant development with an end-to-end soundness proof.

**Provable-security tools confirm the boundary.** EasyCrypt (pRHL, game-based)
and Isabelle's CryptHOL are built for *reductions and advantage bounds under
assumptions* — they abstract concrete attacks away and have **never** been used
to mount/bound a differential attack on a concrete round function.

**SHAttered / Wang et al.: no part machine-checked.** The SHA-1 collision
(Stevens et al., CRYPTO 2017) and the Wang MD5/SHA-1 attacks were built with
custom unverified C/GPU code. The only "certificate" is the colliding file pair
(anyone can *recompute* the hash — concrete checking, not a proof of the attack's
probabilistic reasoning). There is **no verified collision-certificate checker**.
Generic verified UNSAT checking (GRAT/gratchk in Isabelle; Lean's own LRAT
checker) *could* underwrite such results but has **never been connected to a DC
claim**.

---

## 3. SAT/SMT and bit-vector decision procedures inside Lean

**`bv_decide` is the headline capability and it fits crypto's primitive layer
perfectly.** Rotations/shifts are free wire-permutations in the AIG; XOR/AND/NOT
are single gates; 32-bit modular add is a linear carry chain. Goals like "this
optimized `Ch`/`Maj`/sigma equals the spec," "two message-schedule computations
agree," or single-round-function equivalence solve in seconds. The OOPSLA'25
paper reports 97.5% of SMT-LIB QF_BV benchmarks solved *including* verified
certificate checking — near an unverified state-of-the-art solver.

**Trust story (a genuine Lean advantage):** the SAT solver is never trusted.
CaDiCaL's UNSAT answer is accepted only via an **LRAT certificate checked by a
checker proved sound in Lean itself**; the bit-blasting and CNF steps are
verified too. The one TCB addition: the checker runs as compiled native code
(`ofReduceBool`), so the **Lean compiler** joins the kernel in the trusted base.
`bv_check` replays a committed `.lrat` file offline (good for CI). Contrast:
Coq's **SMTCoq** uses a verified checker but run *extracted to OCaml* (extraction
in TCB, solver support dated); Isabelle's sledgehammer uses untrusted solvers as
oracles with LCF-kernel *reconstruction* (no verified bitblaster exists there).
Lean occupies a distinctive point: SMTCoq-style verified checking + sledgehammer
ergonomics + solver bundled in core.

**Concrete crypto evidence & limits (from AWS LNSym):** real 64-bit SHA-512
lemmas are discharged with `bv_check` against committed LRAT files — but the repo
itself documents the ceiling: one `sha512h` lemma "takes ~5min with bv_decide and
the generated LRAT file is ~207MB … not a good candidate for bit-blasting"; such
AC-heavy modular-addition-rearrangement lemmas are instead closed instantly with
`simp`+`ac_rfl`. So the workable pattern is: **normalize word-level algebra first,
bitblast only genuinely bit-level residue, structure across rounds/blocks with
induction + per-round `bv_decide` lemmas.** Whole-compression-function SAT
equivalence, or full-64-round collision/preimage search, is out of reach — a
limit of SAT itself (unverified solvers also cap out near ~20-round reduced
SHA-256), not of Lean's harness.

**Other pieces:** Lean's verified **LRAT** checker + verified AIG library (from
the archived leanprover/leansat, now in core); **no DRAT checker, no verified
full-SMT certificate checker** (SMT is handled by reconstruction). **lean-smt**
(ufmg-smite; CAV 2025) reconstructs cvc5 proofs — beta, covers ~200/662 CPC
rules, **bitvector support experimental** (~30% coverage). LRAT-Catcher (2026)
imports standalone SAT certificates by reflection; pblean does verified
pseudo-Boolean checking.

**Gap that matters for SHA-256:** the missing middle is **word-level reasoning
with cheap certificates** — `bv_decide` is all-or-nothing bitblasting and chokes
on the modular-addition AC-rearrangement that pervades SHA-2, producing 100–200MB
certificates. Missing: a verified SMT-level certificate checker (word-level
rewriting checked cheaply, bitblasting only the residual core — the cvc5/Ethos
direction; lean-smt's BV reconstruction is still experimental); certificate
compression / verified DRAT-trimming; and any bridge from per-round `bv_decide`
lemmas to *round-parametric* statements (today that must be hand-rolled
induction, since bitblasting fixes both width and round count).

---

## 4. Adjacent verified-crypto ecosystems (where the boundary sits)

Uniform pattern across **HACL\*/F\*, SAW/Cryptol, VST+FCF/Coq, CryptHOL/Isabelle,
Jasmin+EasyCrypt**: they prove **implementations correct** (code = FIPS spec,
memory-safe, constant-time) and **constructions secure by reduction** (HMAC is a
PRF *if* the compression function is; the sponge is a random oracle *if* Keccak-f
is ideal). In every case the *intrinsic strength* of the primitive — collision/
preimage resistance of SHA-256 itself — enters only as an **unproven assumption
or idealization**. Highlights:

- **HACL\*/EverCrypt** — verified SHA-2 (functional correctness + memory safety +
  secret independence), in Firefox NSS, Linux kernel (Curve25519), **CPython
  hashlib ≥3.12**. (CCS 2017 / S&P 2020.)
- **SAW+Cryptol** — AWS-LC SHA-384/512 + HMAC verified in CI vs Cryptol specs;
  s2n HMAC (CAV 2018); OpenSSL SHA-256 via SAW attempted (NFM 2021, partial).
- **Coq/Rocq** — Appel VST OpenSSL **SHA-256** (TOPLAS 2015, the benchmark);
  FCF game-based security (HMAC-is-a-PRF, USENIX 2015) — hash strength always an
  axiom; Fiat-Crypto is field arithmetic, *no hashes*.
- **Isabelle** — CryptHOL abstract (random oracles); RIPEMD-160 SPARK the one
  concrete correctness item.
- **Jasmin+EasyCrypt (Formosa)** — the ecosystem's strongest hash result:
  verified **SHA-3/Keccak** implementation (correct + constant-time) *plus* sponge
  **indifferentiability** — but that security theorem still *assumes Keccak-f is
  an ideal permutation*.

**None of these does cryptanalysis.** No formalized differential characteristics,
no machine-checked collision-attack theory, no verified probability bounds for
reduced-round SHA-2. That is the deliberately-untouched ground.

---

## 5. Contribution boundary and open areas (for individual volunteers)

**The boundary in one sentence:** the formal-methods world has thoroughly
verified that SHA-256 *implementations compute the spec* and that *constructions
built on it are secure under assumptions*, but has **never formally reasoned
about attacking or analyzing the primitive**, and — narrowly within Lean — has
**not** even reproduced the Coq/F\* *software* correctness proof (Lean's verified
SHA-256 is only at the circuit level).

So there are two kinds of opening. Ordered within each by rough effort/risk for a
volunteer. (All are "map only" — sizing/selection is a later decision.)

### A. Lean-catch-up gaps (well-trodden elsewhere; lower novelty, lower risk)
These reproduce known results in Lean; good for skill-building and genuinely
useful to the ecosystem, but not research-novel.
- **A1. A canonical Lean 4 SHA-256 spec + core property proofs** — padding
  injectivity, message-schedule/`W` length and well-formedness, one-block vs
  multi-block agreement. No single community spec exists; several unconnected
  copies do (consistency-drift risk). *Small–medium.*
- **A2. Equivalence of an *optimized* SHA-256 (efficient Lean, or Rust-via-hax/
  Aeneas) to the reference spec**, using `bv_decide` for the bit-level cores +
  induction across rounds. This is the Appel-2015 / HACL\* result Lean still
  lacks for SHA-256. *Medium–large.*
- **A3. Merkle–Damgård scaffolding** — length-extension structure, padding
  lemmas — that no Lean project has. *Small–medium.*

### B. Analysis/cryptanalysis gaps (untouched in *every* proof assistant; genuinely novel)
Per the differential-cryptanalysis and SAT threads, any of these would be, to the
best of the 2026 literature, a **first machine-checked result of its kind**.
- **B1. Formalize the Lipmaa–Moriai algorithm** for the differential probability
  of modular addition (xdp⁺ / adp⊕), with a machine-checked correctness proof
  against the semantic definition of DP over `BitVec 32`. *Self-contained,
  algorithmic, bounded — the highest-value/lowest-risk novel target.* Lean's
  `BitVec` layer is ideally suited. **Top recommendation for a first bite.**
- **B2. A verified difference-distribution-table (DDT) theory** — define an
  S-box's DDT, prove row-sum / differential-uniformity invariants, machine-check
  a real small S-box's DDT. (SHA-256 has no S-box, so this is more block-cipher-
  facing, but it's foundational DC infrastructure and small.) *Small–medium.*
- **B3. A verified "characteristic-probability calculator"** — formalize
  De Cannière–Rechberger generalized conditions and their propagation, proving
  the computed characteristic probability sound relative to a defined semantics.
  Effectively a *verified core of AutoDiVer/CryptoSMT*, or a Lean-checkable
  certificate format such a tool could emit. *Large; high novelty.*
- **B4. A verified collision / near-collision certificate checker** — bridge
  Lean's existing verified LRAT checker to an actual hash differential result
  (e.g. a machine-checked "the attack search was sound" or "no trail of weight
  < w exists for k rounds"). The missing link between "SHAttered gives two files"
  and a machine-checked attack. *Large; high novelty; depends on §3 certificate-
  size limits.*

### C. Tooling gaps that unblock B (infrastructure)
- **C1. Word-level (SMT-level) certificate checking in Lean** to tame the
  100–200MB LRAT blow-up on modular-addition-heavy goals — or contribute BV
  proof-rule coverage to **lean-smt** (currently experimental, ~30%). *Large;
  collaborative with existing teams.*
- **C2. Round-parametric bitvector reasoning** — lemmas/tactics to lift
  per-round `bv_decide` facts to statements generic over round count. *Medium–
  large; research-flavored.*

**Recommended first probe if any work is ever scoped: B1 (Lipmaa–Moriai).** It is
bounded, needs no mathlib beyond `BitVec`, has a clean paper correctness proof to
follow, sits on exactly the primitive layer where Lean is strongest, and would be
a first-of-its-kind machine-checked cryptanalysis result — while being small
enough for one volunteer. A2 is the best "catch-up" alternative if the goal is
ecosystem-useful rather than novel.

**Caveat (from the DC thread):** the "first-ever" claims rest on web search plus
abstract/PDF reads, not on cloning and grepping mathlib / the Coq & Isabelle AFP
repos directly. That grep should be done before publishing any "first" claim.

---

## Appendix: key sources

Lean: LNSym (github.com/leanprover/LNSym) · Verified-zkEVM/clean
(github.com/Verified-zkEVM/clean, blog.zksecurity.xyz/posts/clean) · ethereum/
cryptography-specs · `bv_decide` (Lean 4.12 release; OOPSLA'25 doi
10.1145/3763167) · lean-smt (arXiv 2505.15796) · eKisNonos/sha256-gf2-r1cs ·
gdncc/Cryptography + ePrint 2024/1880.
Cryptanalysis: Lipmaa–Moriai (FSE 2001) · De Cannière–Rechberger (ASIACRYPT
2006) · Beyne–Rijmen (ePrint 2022/837) · AutoDiVer (ePrint 2025/185) · EasyBC
(POPL 2024) · SHAttered (ePrint 2017/190) · "SHA-256 Collision with Programmatic
SAT" (arXiv 2406.20072) · CryptoSMT (github.com/kste/cryptosmt).
Adjacent verified crypto: Appel SHA-256 (TOPLAS 2015) · HACL\* (CCS 2017) ·
EverCrypt (S&P 2020) · aws-lc-verification · CryptHOL (J. Cryptology 2019) ·
Formosa SHA-3 (CCS 2019, ePrint 2019/1155).
