import Mathlib

/-!
# Chinukwe.PositiveSystems — positive-vector stability (core §5)

UNCOMPILED DRAFT; no `sorry`. `Matrix.mulVec`/`dotProduct` and the norm lemma names
(`Complex.norm_of_nonneg`, `Complex.re_le_norm`) have moved between Mathlib versions;
`first | … | …` fallbacks are included where I know they churn.

Shared lemma `mulVec_abs_le`: if Λ ≥ 0, Λv ≤ q v and |x| ≤ r v then |Λx| ≤ q r v.
This is the weighted-max-norm contraction with no Perron–Frobenius, used by
 (i) discrete cascade  xₙ₊₁ = Λ xₙ        (DiscreteCascade.lean), and
 (ii) the continuous theorem for A = K̄ − R   (`hurwitz_of_positive_vector`).
Bridge to ρ(·) < 1 (Collatz–Wielandt / Neumann series) is a later file.
-/

open Finset

namespace Chinukwe

variable {ι : Type*} [Fintype ι]

lemma mulVec_abs_le {Λ : Matrix ι ι ℝ} (hΛ : ∀ i j, 0 ≤ Λ i j)
    {v x : ι → ℝ} {r q : ℝ} (hr : 0 ≤ r)
    (hx : ∀ j, |x j| ≤ r * v j)
    (hq : ∀ i, (Λ.mulVec v) i ≤ q * v i) :
    ∀ i, |(Λ.mulVec x) i| ≤ q * r * v i := by
  intro i
  have hsum : ∑ j, Λ i j * (r * v j) = r * (Λ.mulVec v) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc |(Λ.mulVec x) i|
      = |∑ j, Λ i j * x j| := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, |Λ i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, Λ i j * |x j| :=
        Finset.sum_congr rfl fun j _ => by rw [abs_mul, abs_of_nonneg (hΛ i j)]
    _ ≤ ∑ j, Λ i j * (r * v j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx j) (hΛ i j)
    _ = r * (Λ.mulVec v) i := hsum
    _ ≤ r * (q * v i) := mul_le_mul_of_nonneg_left (hq i) hr
    _ = q * r * v i := by ring

/-- Continuous time: A = K̄ − diag(d), K̄ ≥ 0, d > 0, and ∃ v > 0 with K̄ v < d·v
⇒ every complex eigenvalue of A has negative real part. -/
theorem hurwitz_of_positive_vector
    {K : Matrix ι ι ℝ} (hK : ∀ i j, 0 ≤ K i j) {d v : ι → ℝ}
    (hd : ∀ i, 0 < d i) (hv : ∀ i, 0 < v i)
    (hKv : ∀ i, (K.mulVec v) i < d i * v i)
    (lam : ℂ) (w : ι → ℂ) (hw : w ≠ 0)
    (heig : ∀ i, (∑ j, (K i j : ℂ) * w j) - (d i : ℂ) * w i = lam * w i) :
    lam.re < 0 := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i0, w i0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  haveI : Nonempty ι := ⟨i0⟩
  -- coordinate maximising ‖wᵢ‖ / vᵢ
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => ‖w j‖ / v j)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖w i‖ / v i := ⟨_, rfl⟩
  have hi' : ∀ j, ‖w j‖ / v j ≤ r := fun j => by rw [hr]; exact hi j
  have hrpos : 0 < r :=
    lt_of_lt_of_le (div_pos (norm_pos_iff.2 hi0) (hv i0)) (hi' i0)
  have hwle : ∀ j, ‖w j‖ ≤ r * v j := by
    intro j
    have hvj : v j ≠ 0 := (hv j).ne'
    calc ‖w j‖ = (‖w j‖ / v j) * v j := by field_simp
      _ ≤ r * v j := mul_le_mul_of_nonneg_right (hi' j) (hv j).le
  have hwi : ‖w i‖ = r * v i := by
    have hvi : v i ≠ 0 := (hv i).ne'
    rw [hr]; field_simp
  have hwipos : 0 < ‖w i‖ := by rw [hwi]; exact mul_pos hrpos (hv i)
  have e : (lam + (d i : ℂ)) * w i = ∑ j, (K i j : ℂ) * w j := by
    linear_combination (-1 : ℂ) * heig i
  have hnorm : ‖lam + (d i : ℂ)‖ * ‖w i‖ ≤ r * (K.mulVec v) i := by
    calc ‖lam + (d i : ℂ)‖ * ‖w i‖ = ‖∑ j, (K i j : ℂ) * w j‖ := by rw [← norm_mul, e]
      _ ≤ ∑ j, ‖(K i j : ℂ) * w j‖ := norm_sum_le _ _
      _ = ∑ j, K i j * ‖w j‖ := Finset.sum_congr rfl fun j _ => by
          first
            | rw [norm_mul, Complex.norm_of_nonneg (hK i j)]
            | (rw [norm_mul]; simp [abs_of_nonneg (hK i j)])
      _ ≤ ∑ j, K i j * (r * v j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hwle j) (hK i j)
      _ = r * (K.mulVec v) i := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hlt : ‖lam + (d i : ℂ)‖ < d i := by
    have h1 : r * (K.mulVec v) i < r * (d i * v i) :=
      mul_lt_mul_of_pos_left (hKv i) hrpos
    have h2 : ‖lam + (d i : ℂ)‖ * ‖w i‖ < d i * ‖w i‖ := by
      calc ‖lam + (d i : ℂ)‖ * ‖w i‖ ≤ r * (K.mulVec v) i := hnorm
        _ < r * (d i * v i) := h1
        _ = d i * ‖w i‖ := by rw [hwi]; ring
    exact lt_of_mul_lt_mul_right h2 hwipos.le
  have hre : lam.re + d i ≤ ‖lam + (d i : ℂ)‖ := by
    have h : (lam + (d i : ℂ)).re ≤ ‖lam + (d i : ℂ)‖ := by
      first
        | exact Complex.re_le_norm _
        | exact Complex.re_le_abs _
        | exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
    simpa using h
  linarith

end Chinukwe
