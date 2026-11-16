import Mathlib

/-!
# Chinukwe.Weights — Theorem 4.2 (ratio-consistent weights)

UNCOMPILED DRAFT. Lemma names may drift with your Mathlib version.
Pure algebra: no empirical values, no axioms. β is a hypothesis, never a constant.
Ratio consistency is stated in product form (wᵢ βⱼ = wⱼ βᵢ), which avoids division
and needs positivity only for Σβ > 0.
-/

open Finset

namespace Chinukwe

variable {ι : Type*} [Fintype ι]

/-- (W1) in product form: wᵢ/wⱼ = βᵢ/βⱼ. -/
def RatioConsistent (w β : ι → ℝ) : Prop :=
  ∀ i j, w i * β j = w j * β i

/-- The proportional rule wᵢ = βᵢ / Σⱼ βⱼ. -/
noncomputable def propWeight (β : ι → ℝ) (i : ι) : ℝ :=
  β i / ∑ j, β j

lemma sum_pos_of_pos [Nonempty ι] {β : ι → ℝ} (hβ : ∀ i, 0 < β i) :
    0 < ∑ j, β j :=
  Finset.sum_pos (fun j _ => hβ j) Finset.univ_nonempty

/-- Uniqueness: (W1) ∧ (W2) ⇒ wᵢ = βᵢ / Σβ. -/
theorem weights_unique [Nonempty ι] (β w : ι → ℝ) (hβ : ∀ i, 0 < β i)
    (hrc : RatioConsistent w β) (hsum : ∑ i, w i = 1) :
    ∀ i, w i = propWeight β i := by
  intro i
  have hS := sum_pos_of_pos hβ
  unfold propWeight
  rw [eq_div_iff hS.ne']
  calc w i * ∑ j, β j
      = ∑ j, w i * β j := by rw [Finset.mul_sum]
    _ = ∑ j, w j * β i := Finset.sum_congr rfl fun j _ => hrc i j
    _ = (∑ j, w j) * β i := by rw [Finset.sum_mul]
    _ = β i := by rw [hsum, one_mul]

/-- Existence: the proportional rule satisfies (W1). -/
theorem propWeight_ratioConsistent (β : ι → ℝ) :
    RatioConsistent (propWeight β) β := by
  intro i j
  unfold propWeight
  ring

/-- Existence: the proportional rule satisfies (W2). -/
theorem propWeight_sum [Nonempty ι] {β : ι → ℝ} (hβ : ∀ i, 0 < β i) :
    ∑ i, propWeight β i = 1 := by
  have hS := sum_pos_of_pos hβ
  unfold propWeight
  rw [← Finset.sum_div]
  exact div_self hS.ne'

/-- Existence: the proportional rule satisfies (W3). -/
theorem propWeight_pos [Nonempty ι] {β : ι → ℝ} (hβ : ∀ i, 0 < β i) (i : ι) :
    0 < propWeight β i :=
  div_pos (hβ i) (sum_pos_of_pos hβ)

end Chinukwe
