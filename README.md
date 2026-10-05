# STOG-lean4-v2

Lean 4 formalization accompanying the STOG–MetaMorph paper, **v3 revision**.
This is a revised copy of `STOG-lean4`; the original is left untouched.

## Files

| File | Description |
|---|---|
| `STOG_Five_Theorems_Lean4_Complete_Proof_EN.lean4` | Complete closed proofs of the algebraic kernels of P1–P5 (P5 clause (iii) only) + Conjecture C1 statement. Pure Lean 4 core: no imports, no axioms, no `sorry`. English. |
| `STOG_Five_Theorems_Lean4_Complete_Proof_CN.lean4` | Same as above, Chinese. |
| `STOG-with-mathlib.lean4` | Full analytic statements in Lean 4 + Mathlib (definitions + statement skeletons). Contains `sorry` placeholders — proof sketches only, not closed proofs. Chinese. |
| `STOG-without-mathlib.lean4` | Cloud-safe axiom-based version (abstract scalar type, axioms for the analytic content). English comments. |
| **`STOG_Formal_v4.lean`** | **v4-final: the single authoritative Mathlib file. Compiles clean — 0 error, 0 warning, 0 `sorry`, 0 axiom.** See `CHANGELOG-v4.md`. |
| `CHANGELOG-v4.md` | Item-by-item disposition of the 15 `sorry` placeholders plus the full log of the ~40 real type errors fixed to reach a clean build. |

There is no Lake project for the four `.lean4` files (no `lakefile` /
`lean-toolchain`); those are self-contained and designed to be pasted into an
online Lean 4 environment (e.g. https://lean.math.hhu.de). `STOG_Formal_v4.lean`
imports `Mathlib`, so it needs a real toolchain (or the online Mathlab-enabled
playground that ships Mathlib); a Lake project for it lives in the companion
directory `lean-build/` (`lakefile.toml`, `lean-toolchain`, `Stog/Basic.lean`).

## Mapping: paper (v3) ↔ Lean declarations

| Paper v3 | Content | Lean declarations |
|---|---|---|
| Proposition P1 | Spectral operator risk decomposition | `InnerSpace.risk_decomposition`, `InnerSpace.pythagoras` (complete files); `spectral_operator_risk_decomposition` (mathlib); `theorem1_spectral_operator_risk_decomposition` (axiom file) |
| Proposition P2 | Condition-number regularization | `differencing_contracts_condition_ratio`, `contraction_grows_with_decay`, `differencing_strictly_contracts` (complete); `differencing_lowers_condition_number`, `static_projection_lowers_condition_number` (mathlib); `theorem2_condition_number_regularization` (axiom) |
| Proposition P3 | Robust sufficient statistics | `rawIF_unbounded_above/below`, `huberIF_bounded`, `huberIF_saturates`, `med3_bounded`, `robust_vs_raw` (complete); `raw_influence_unbounded`, `robust_influence_bounded`, `robust_representation_optimal` (mathlib); `theorem3_robust_sufficient_statistics` (axiom) |
| Proposition P4 | Regime separability & gating optimality | `bayes_gate_optimal`, `gating_excess_risk`, `excess_le_overlap_mul_gap`, `implementable_gate_bound` (complete); `regime_gating_optimality` (mathlib, explicit hypothesis `h_balance`); `theorem4_regime_separability_and_gating_optimality` (axiom, explicit hypothesis `amplitudeBalanced`) |
| Proposition P5 | Function-space atlas & fusion geometry | Clause (iii) only in complete files: `hedge_step_pos`, `hedge_odds_fixed`, `hedge_odds_improve`, `hedge_odds_improve_strict`; mathlib: `hedge_natural_gradient` (clause (iii)) and `representation_fusion_superiority` (geometric clause, see below); axiom: `theorem5_function_space_atlas_and_fusion_geometry` |
| Conjecture C1 | Attribution–intervention rank consistency | `attributionInterventionRankConsistent` (all four files) — statement-only `def`, **not asserted** |

## v3 revision notes

1. **Naming.** The paper's "Theorem 1–5" are now "Proposition P1–P5" with explicit
   assumption sets. All docstrings, comments, and section headers were aligned to the
   Proposition naming. Lean declaration names were intentionally **not** renamed, to
   avoid breaking cross-references.

2. **Proposition P4 — empirical falsification of the qualified form.** The qualified
   (amplitude-driven benefit) form of P4 was falsified empirically under
   amplitude-balanced conditions (experiment E4 v4: after the amplitude ratio was
   balanced to 1.026, the oracle benefit dropped from 0.61 to 0.007; the v3 benefit
   was entirely driven by a 6.53× amplitude gap). The formal statements remain
   mathematically valid under their hypotheses and are kept; the amplitude-related
   hypothesis is explicit (`h_balance` in the mathlib file, `amplitudeBalanced` in the
   axiom file, and a recorded assumption in the P4 section headers of the complete
   files). The falsification is recorded in docstrings/comments next to each P4
   statement.

3. **Proposition P5 — geometric sub-clauses demoted to SI.** The geometric
   sub-clauses (paper 5a/5b, e.g. `representation_fusion_superiority` in the mathlib
   file and the atlas/fusion conjuncts in the axiom file) were falsified empirically
   and demoted to Supplementary Information. The (correct-as-stated) formal skeletons
   are kept and annotated; they are no longer main-text claims. Clause (iii)
   (Hedge = Euler discretization of natural-gradient flow on the simplex) is retained
   in the main text.

4. **Conjecture C1 — added, falsified.** Attribution–intervention rank consistency
   (measured Spearman ρ = −0.105, falsified) is recorded in all four files as
   `attributionInterventionRankConsistent`, a statement-only `def` with a docstring
   marking its empirical status. It is deliberately **not** stated as a theorem, so
   the complete-proof files remain free of `sorry` and axioms.

## Verification status

**Updated 2026-10-06.** `STOG_Formal_v4.lean` has now been compiled with a real
toolchain on the authoring machine:

| Item | Value |
|---|---|
| Lean | `leanprover/lean4:v4.35.0-rc3` (installed via elan) |
| Mathlib | pinned to `c20717eaa791af9dd3f7847f5ba91623bda9ab6b` |
| Build | `lake build Stog` → `Build completed successfully (9019 jobs)` |
| Output | **0 error, 0 warning, 0 `sorry`, 0 `admit`, 0 `axiom`, 0 `unsafe`** |

Reproduce with:

```bash
cd lean-build
lake build Stog          # authoritative; pulls the olean cache on first run
```

or, for faster iteration during editing:

```bash
export LEAN_PATH=".lake/packages/batteries/.lake/build/lib/lean:\
.lake/packages/mathlib/.lake/build/lib/lean:.lake/build/lib/lean"
lean Stog/Basic.lean
```

The four `.lean4` files were **not** recompiled with the toolchain — they use the
`.lean4` extension for the online playground and are not part of the Lake project.
Their proof code is unchanged from the previously verified versions; the v3 revision
touched only comments, docstrings, section headers and one new `def` per file, and
all edits were syntax-reviewed by hand.
