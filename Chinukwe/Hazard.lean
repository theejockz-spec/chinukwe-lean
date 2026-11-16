import Mathlib

/-!
# Chinukwe.Hazard — reference-shifted coupled hazard (core §2)

UNCOMPILED DRAFT. Paper decision (b): coupling is measured relative to a reference
state `dref`, so "coupling raises hazard" has a precise meaning. Without the reference,
dⱼ ≥ 0 makes the coupled hazard ≤ the κ=0 hazard, which inverts the intended sign.
βᵢ here is a log-hazard sensitivity (units 1/[d]); it is NOT the restoring rate ϱ of §5.
-/

open Finset

namespace Chinukwe

structure HazardParams (ι : Type*) [Fintype ι] where
  lam0 : ι → ℝ          -- baseline hazard λᵢ° > 0
  β : ι → ℝ             -- own-distance log-sensitivity ≥ 0
  κ : ι → ι → ℝ         -- κ̄ᵢⱼ = |κᵢⱼ| ≥ 0
  dref : ι → ℝ          -- reference state
  lam0_pos : ∀ i, 0 < lam0 i
  β_nonneg : ∀ i, 0 ≤ β i
  κ_nonneg : ∀ i j, 0 ≤ κ i j
  κ_diag : ∀ i, κ i i = 0

namespace HazardParams

variable {ι : Type*} [Fintype ι] (P : HazardParams ι)

/-- λᵢ(d) = λᵢ° · exp(−βᵢ dᵢ − Σⱼ κ̄ᵢⱼ (dⱼ − dⱼʳᵉᶠ)). -/
noncomputable def hazard (d : ι → ℝ) (i : ι) : ℝ :=
  P.lam0 i * Real.exp (-(P.β i * d i) - ∑ j, P.κ i j * (d j - P.dref j))

/-- Uncoupled baseline (κ = 0). -/
noncomputable def hazard0 (d : ι → ℝ) (i : ι) : ℝ :=
  P.lam0 i * Real.exp (-(P.β i * d i))

/-- Monotonicity: better distances never raise the hazard. -/
theorem hazard_antitone {d d' : ι → ℝ} (hdd : d ≤ d') (i : ι) :
    P.hazard d' i ≤ P.hazard d i := by
  unfold hazard
  refine mul_le_mul_of_nonneg_left ?_ (P.lam0_pos i).le
  apply Real.exp_le_exp.2
  have h1 : P.β i * d i ≤ P.β i * d' i :=
    mul_le_mul_of_nonneg_left (hdd i) (P.β_nonneg i)
  have h2 : ∑ j, P.κ i j * (d j - P.dref j) ≤ ∑ j, P.κ i j * (d' j - P.dref j) :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (by linarith [hdd j]) (P.κ_nonneg i j)
  linarith

/-- Sign of coupling: coupled ≥ uncoupled ⇔ Σⱼ κ̄ᵢⱼ (dⱼ − dⱼʳᵉᶠ) ≤ 0. -/
theorem uncoupled_le_hazard_iff (d : ι → ℝ) (i : ι) :
    P.hazard0 d i ≤ P.hazard d i ↔ ∑ j, P.κ i j * (d j - P.dref j) ≤ 0 := by
  unfold hazard hazard0
  constructor
  · intro h
    have h' := le_of_mul_le_mul_left h (P.lam0_pos i)
    have := Real.exp_le_exp.1 h'
    linarith
  · intro h
    refine mul_le_mul_of_nonneg_left ?_ (P.lam0_pos i).le
    apply Real.exp_le_exp.2
    linarith

/-- Neighbours at or above reference ⇒ coupling lowers hazard. -/
theorem hazard_le_uncoupled_of_ge {d : ι → ℝ} (h : ∀ j, P.dref j ≤ d j) (i : ι) :
    P.hazard d i ≤ P.hazard0 d i := by
  unfold hazard hazard0
  refine mul_le_mul_of_nonneg_left ?_ (P.lam0_pos i).le
  apply Real.exp_le_exp.2
  have : 0 ≤ ∑ j, P.κ i j * (d j - P.dref j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (P.κ_nonneg i j) (by linarith [h j])
  linarith

/-- Neighbours at or below reference ⇒ coupling raises hazard. -/
theorem uncoupled_le_hazard_of_le {d : ι → ℝ} (h : ∀ j, d j ≤ P.dref j) (i : ι) :
    P.hazard0 d i ≤ P.hazard d i := by
  rw [P.uncoupled_le_hazard_iff]
  exact Finset.sum_nonpos fun j _ =>
    mul_nonpos_of_nonneg_of_nonpos (P.κ_nonneg i j) (by linarith [h j])

end HazardParams
end Chinukwe
