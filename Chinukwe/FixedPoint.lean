import Mathlib

/-!
# Chinukwe.FixedPoint — coupled critical distance (Theorem 4.3′, core §4)

UNCOMPILED DRAFT (no `sorry` left, but lemma names may drift with your Mathlib;
`first | … | …` blocks give fallbacks for the names that churn most).

Design choices:
* Map defined on d* only (the Sixth Edition mixes d° and d*).
* Condition is the ROW-SUM bound  maxᵢ (cᵢ/μᵢ²) Σⱼ κ̄ᵢⱼ ≤ q < 1  (sufficient, not "iff ρ").
* `max (d j) 0` inside the denominator makes T total and globally Lipschitz on
  `ι → ℝ` (complete), so fixed points need no closed-cone bookkeeping.
* cᵢ := σᵢ² · ln 2 / 2 in the application; here only `0 ≤ cᵢ`. No empirical constants.
-/

open Finset NNReal

namespace Chinukwe

structure CritParams (ι : Type*) [Fintype ι] where
  μ : ι → ℝ
  c : ι → ℝ
  κ : ι → ι → ℝ          -- κ i j = |κᵢⱼ|
  μ_pos : ∀ i, 0 < μ i
  c_nonneg : ∀ i, 0 ≤ c i
  κ_nonneg : ∀ i j, 0 ≤ κ i j
  κ_diag : ∀ i, κ i i = 0

namespace CritParams

variable {ι : Type*} [Fintype ι] (P : CritParams ι)

def denom (d : ι → ℝ) (i : ι) : ℝ :=
  P.μ i + ∑ j, P.κ i j * max (d j) 0

lemma denom_ge (d : ι → ℝ) (i : ι) : P.μ i ≤ P.denom d i := by
  unfold denom
  have : 0 ≤ ∑ j, P.κ i j * max (d j) 0 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (P.κ_nonneg i j) (le_max_right _ _)
  linarith

lemma denom_pos (d : ι → ℝ) (i : ι) : 0 < P.denom d i :=
  lt_of_lt_of_le (P.μ_pos i) (P.denom_ge d i)

noncomputable def T (d : ι → ℝ) : ι → ℝ := fun i => P.c i / P.denom d i

/-- Scalar core: |c/a − c/b| ≤ c|a−b|/m² when a, b ≥ m > 0. -/
lemma abs_div_sub_div_le {c a b m : ℝ} (hc : 0 ≤ c) (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) :
    |c / a - c / b| ≤ c * |a - b| / m ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le hm ha
  have hb0 : 0 < b := lt_of_lt_of_le hm hb
  have key : c / a - c / b = c * (b - a) / (a * b) := by
    rw [div_sub_div _ _ ha0.ne' hb0.ne']; ring
  rw [key, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_mul, abs_of_nonneg hc,
    abs_sub_comm b a]
  have hmm : m ^ 2 ≤ a * b := by rw [sq]; exact mul_le_mul ha hb hm.le ha0.le
  have hnum : 0 ≤ c * |a - b| := mul_nonneg hc (abs_nonneg _)
  have hm2 : 0 < m ^ 2 := by positivity
  first
    | exact div_le_div_of_nonneg_left hnum hm2 hmm
    | exact div_le_div_of_le_left hnum hm2 hmm
    | gcongr

lemma abs_denom_sub_le (d d' : ι → ℝ) (i : ι) :
    |P.denom d i - P.denom d' i| ≤ ∑ j, P.κ i j * |d j - d' j| := by
  unfold denom
  have h : P.μ i + ∑ j, P.κ i j * max (d j) 0 - (P.μ i + ∑ j, P.κ i j * max (d' j) 0)
      = ∑ j, P.κ i j * (max (d j) 0 - max (d' j) 0) := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  calc |∑ j, P.κ i j * (max (d j) 0 - max (d' j) 0)|
      ≤ ∑ j, |P.κ i j * (max (d j) 0 - max (d' j) 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, P.κ i j * |max (d j) 0 - max (d' j) 0| :=
        Finset.sum_congr rfl fun j _ => by rw [abs_mul, abs_of_nonneg (P.κ_nonneg i j)]
    _ ≤ ∑ j, P.κ i j * |d j - d' j| :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) (P.κ_nonneg i j)

/-- Row estimate: |Tᵢd − Tᵢd′| ≤ (cᵢ/μᵢ²) Σⱼ κᵢⱼ |dⱼ − d′ⱼ|. -/
lemma abs_T_sub_le (d d' : ι → ℝ) (i : ι) :
    |P.T d i - P.T d' i| ≤ (P.c i / P.μ i ^ 2) * ∑ j, P.κ i j * |d j - d' j| := by
  have h1 := abs_div_sub_div_le (P.c_nonneg i) (P.μ_pos i) (P.denom_ge d i) (P.denom_ge d' i)
  have h2 := P.abs_denom_sub_le d d' i
  have hc2 : 0 ≤ P.c i / P.μ i ^ 2 := div_nonneg (P.c_nonneg i) (by positivity)
  calc |P.T d i - P.T d' i|
      = |P.c i / P.denom d i - P.c i / P.denom d' i| := rfl
    _ ≤ P.c i * |P.denom d i - P.denom d' i| / P.μ i ^ 2 := h1
    _ = (P.c i / P.μ i ^ 2) * |P.denom d i - P.denom d' i| := by ring
    _ ≤ (P.c i / P.μ i ^ 2) * ∑ j, P.κ i j * |d j - d' j| :=
        mul_le_mul_of_nonneg_left h2 hc2

/-- Contraction on the sup-norm space ι → ℝ under the row-sum condition. -/
theorem contracting (q : ℝ≥0) (hq : q < 1)
    (hL : ∀ i, (P.c i / P.μ i ^ 2) * ∑ j, P.κ i j ≤ q) :
    ContractingWith q P.T := by
  refine ⟨hq, LipschitzWith.of_dist_le_mul fun d d' => ?_⟩
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  rw [Real.dist_eq]
  have hrow := P.abs_T_sub_le d d' i
  have hdj : ∀ j, |d j - d' j| ≤ dist d d' := fun j => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist d d' j
  have hsum : ∑ j, P.κ i j * |d j - d' j| ≤ (∑ j, P.κ i j) * dist d d' := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hdj j) (P.κ_nonneg i j)
  have hc2 : 0 ≤ P.c i / P.μ i ^ 2 := div_nonneg (P.c_nonneg i) (by positivity)
  calc |P.T d i - P.T d' i|
      ≤ (P.c i / P.μ i ^ 2) * ∑ j, P.κ i j * |d j - d' j| := hrow
    _ ≤ (P.c i / P.μ i ^ 2) * ((∑ j, P.κ i j) * dist d d') :=
        mul_le_mul_of_nonneg_left hsum hc2
    _ = ((P.c i / P.μ i ^ 2) * ∑ j, P.κ i j) * dist d d' := by ring
    _ ≤ (q : ℝ) * dist d d' := mul_le_mul_of_nonneg_right (hL i) dist_nonneg

/-- Existence and uniqueness of the coupled critical-distance vector. -/
theorem exists_unique_fixedPoint (q : ℝ≥0) (hq : q < 1)
    (hL : ∀ i, (P.c i / P.μ i ^ 2) * ∑ j, P.κ i j ≤ q) :
    ∃! d : ι → ℝ, P.T d = d := by
  have hc := P.contracting q hq hL
  refine ⟨ContractingWith.fixedPoint _ hc, hc.fixedPoint_isFixedPt, fun y hy => ?_⟩
  exact hc.fixedPoint_unique hy

/-- Any fixed point is strictly positive wherever cᵢ > 0. -/
lemma fixedPoint_pos {d : ι → ℝ} (hd : P.T d = d) {i : ι} (hci : 0 < P.c i) :
    0 < d i := by
  have h : d i = P.c i / P.denom d i := by
    simpa [T] using (congrFun hd i).symm
  rw [h]
  exact div_pos hci (P.denom_pos d i)

/-- Upper bound: dᵢ* ≤ cᵢ / μᵢ (coupling can only shrink the critical distance). -/
lemma fixedPoint_le {d : ι → ℝ} (hd : P.T d = d) (i : ι) : d i ≤ P.c i / P.μ i := by
  have h : d i = P.c i / P.denom d i := by
    simpa [T] using (congrFun hd i).symm
  rw [h]
  first
    | exact div_le_div_of_nonneg_left (P.c_nonneg i) (P.μ_pos i) (P.denom_ge d i)
    | exact div_le_div_of_le_left (P.c_nonneg i) (P.μ_pos i) (P.denom_ge d i)

end CritParams
end Chinukwe
