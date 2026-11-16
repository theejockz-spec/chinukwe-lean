# Chinukwe — formal core (Lean 4 + Mathlib)

All Rights Reserved
This software and associated documentation files may not be copied, modified, merged, published, distributed, sublicensed, and/or sold without the express written permission of the copyright holder Chanda Chinukwe
For commercial licensing or downstream proprietary use, please contact [ChandaCjr@outlook.com].

Lean development accompanying *A Formal Core for Coupled Barrier-Distance Dynamics*
(`docs/Chinukwe_Formal_Core_Working_Draft.md`).

**Status: the core compiles on Lean v4.36.0-rc2 with no `sorry`.** Every audited theorem
depends only on `propext`, `Classical.choice`, `Quot.sound` (`scripts/check.sh` enforces this).
The only `sorry` in the repository is the isolated conjecture in `Conjectures/`.

## Layout

```
lakefile.toml  lean-toolchain  lake-manifest.json (created by `lake update`)
Chinukwe.lean                  root; imports core modules only
Chinukwe/
  Domains.lean                 Fin 5 index type for the application
  Weights.lean                 Thm 3.2   proportional weights
  Hazard.lean                  Prop 2.2–2.3  reference-shifted hazard
  FixedPoint.lean              Lemma 4.1–4.2, Thm 4.3  coupled critical distance
  PositiveSystems.lean         Lemma 5.0, Thm 5.4 (ii)⇒(iii)
  Spectral.lean                SubUnit; spectral radius < 1 ⇒ some power has row sums < 1 (Gelfand)
  Collatz.lean                 Thm 5.1(b)  positive-vector bridge
  DiscreteCascade.lean         Thm 5.1(a)  generation dynamics
  Empirical.lean, Empirical/   provenance records only; no entries yet
Conjectures.lean, Conjectures/ unproved targets (Thm 4.4 spectral form)
scripts/                       bootstrap, check, audit, syntax fix
docs/                          the paper (Markdown)
.github/workflows/lean.yml     CI
```

Planned, not yet written: `Temporal`, `Welfare`, `Diffusions`, `Association`.

## Setup

```bash
bash scripts/bootstrap.sh    # installs elan if needed, resolves Mathlib, adopts its toolchain,
                             # downloads the Mathlib cache, runs the first build
bash scripts/check.sh        # project invariants (below)
```

After the first green build, pin Mathlib: set `rev` in `lakefile.toml` to the commit shown
in `lake-manifest.json`, and commit `lake-manifest.json`.

## Rules (enforced by `scripts/check.sh`)

1. **No `axiom` in the core.** Parameters are hypotheses of theorems, never constants.
2. **Empirical boundary.** Empirical values and source claims live only in
   `Chinukwe/Empirical/`. Nothing else may import it, and nothing there is an axiom.
   Add an estimate only with `status := .verified` and a full provenance record.
3. **Sorry whitelist.** `scripts/sorry-whitelist.txt` lists files allowed to contain `sorry`
   (currently only the isolated `Conjectures/SpectralFixedPoint.lean`); `scripts/sorry-dependents.txt`
   is empty: no audited core theorem may depend on `sorryAx`.
4. **Conjectures isolated.** `Conjectures/` is a separate library that the core never imports.
5. **Audit.** `scripts/AxiomAudit.lean` prints the axioms of every theorem cited in the paper's
   §7. Only `propext`, `Classical.choice`, `Quot.sound` are allowed (plus `sorryAx` for the
   whitelisted dependents). When you add a theorem the paper cites, add it to this file.

## Status (mirrors paper §7)

| Result | Module | Status |
|---|---|---|
| Proportional weights | Weights | compiled |
| Hazard monotonicity, sign of coupling | Hazard | compiled |
| Scalar and row estimates; contraction, fixed point | FixedPoint | compiled |
| Weighted-norm lemma | PositiveSystems | compiled |
| Hurwitz from positive vector (Thm 5.4 (ii)⇒(iii)) | PositiveSystems | compiled |
| Discrete cascade decay | DiscreteCascade | compiled |
| Collatz–Wielandt bound; finite Neumann construction | Collatz | compiled |
| ρ(Λ) < 1 ⇒ some power has row sums < 1 | Spectral | compiled |
| ρ(Λ) < 1 ⇔ positive vector | Collatz | compiled |
| Spectral form of Thm 4.3 | Conjectures | target |
| Joint absorption | — | open |

## Fixing name drift on a first build

I could not compile these files, so expect a few of these. Fallbacks are already in the
source for the first three.

| Symptom | Likely cause | Fix |
|---|---|---|
| `unknown identifier div_le_div_of_nonneg_left` | renamed | `div_le_div_of_le_left`, or `gcongr` |
| `unknown constant Complex.norm_of_nonneg` | renamed | `Complex.abs_of_nonneg`, or `simp [abs_of_nonneg ..]` |
| `unknown constant Complex.re_le_norm` | renamed | `Complex.re_le_abs` |
| error or warning on `∑ x in s, f x` | new binder syntax | `bash scripts/fix_sum_syntax.sh` |
| `Matrix.mulVec` / `dotProduct` unfold fails | namespace move | try `Matrix.dotProduct` or `Matrix.mulVec_eq_sum` |
| `Real.rpow_inv_natCast_pow` not found | renamed | `Real.rpow_natCast` with `Real.rpow_mul`, or `Real.pow_rpow_inv_natCast` |
| `ContractingWith.fixedPoint_unique` arity | signature | use `hc.fixedPoint_unique'` with two fixed-point proofs |

Tip: fix errors top-down, one module at a time (`lake build Chinukwe.Weights`, then
`Chinukwe.Hazard`, and so on in dependency order: Weights, Hazard, FixedPoint,
PositiveSystems, DiscreteCascade, Collatz).

## The Gelfand step (closed)

`exists_pow_rowsum_lt_one_of_subUnit` in `Chinukwe/Spectral.lean` is proved from Mathlib's
Gelfand formula (`spectrum.pow_nnNorm_pow_one_div_tendsto_nhds_spectralRadius`), the L∞ operator
norm on matrices (`open scoped Matrix.Norms.Operator`), and `Module.End.hasEigenvalue_iff_mem_spectrum`.

## Seen on a real first build (Windows, Lean v4.36.0-rc2)

| Symptom | Cause | Fix |
|---|---|---|
| `failed to read file ...olean.private` | parallel build over a Mathlib cache that was not fully unpacked | re-run `lake build`; if it persists, `lake exe cache get!` |
| `failed to synthesize HPow (Matrix ι ι ℝ) ℕ _` | matrix powers need `[DecidableEq ι]` | add it to the `variable` line (done in Collatz.lean) |
| `unexpected token 'in'; expected ','` | `∑ x in s` removed in newer Mathlib | `bash scripts/fix_sum_syntax.sh` (done in Collatz.lean) |
| `push_neg has been deprecated` | warning only | optional: `push Not` |
| "this tactic is never executed" in a `first | …` block | the first alternative worked | harmless; can delete the dead fallbacks |
