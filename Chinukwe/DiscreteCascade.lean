import Mathlib
import Chinukwe.PositiveSystems

/-!
# Chinukwe.DiscreteCascade — corrected Theorem 5.1a′ (core §5.1)

UNCOMPILED DRAFT. Replaces the Sixth Edition's Theorem 5.1a, which claimed that
ρ(Λ) < 1 gives decay for δλ' = Λ δλ in continuous time (false for Λ ≥ 0, ρ > 0).
The threshold 1 belongs to generation dynamics xₙ₊₁ = Λ xₙ, or to ẋ = (Λ − I) x.
-/

open Filter Topology

namespace Chinukwe

variable {ι : Type*} [Fintype ι]

/-- Cascade generations xₙ = Λⁿ x₀. -/
def cascadeIter (Λ : Matrix ι ι ℝ) (x : ι → ℝ) (n : ℕ) : ι → ℝ :=
  (fun y => Λ.mulVec y)^[n] x

/-- Geometric decay in the v-weighted max norm. -/
theorem cascade_decay {Λ : Matrix ι ι ℝ} (hΛ : ∀ i j, 0 ≤ Λ i j)
    {v x : ι → ℝ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q)
    (hx : ∀ j, |x j| ≤ r * v j)
    (hq : ∀ i, (Λ.mulVec v) i ≤ q * v i) (n : ℕ) :
    ∀ i, |cascadeIter Λ x n i| ≤ q ^ n * r * v i := by
  induction n with
  | zero => intro i; simpa [cascadeIter] using hx i
  | succ n ih =>
    intro i
    unfold cascadeIter at *
    rw [Function.iterate_succ_apply']
    have hr' : 0 ≤ q ^ n * r := mul_nonneg (pow_nonneg hq0 n) hr
    have h := mulVec_abs_le hΛ hr' (fun j => by simpa [mul_assoc] using ih j) hq i
    calc _ ≤ q * (q ^ n * r) * v i := h
      _ = q ^ (n + 1) * r * v i := by ring

/-- Each component of the cascade tends to 0 when q < 1. -/
theorem cascade_tendsto_zero {Λ : Matrix ι ι ℝ} (hΛ : ∀ i j, 0 ≤ Λ i j)
    {v x : ι → ℝ} {r q : ℝ} (hr : 0 ≤ r) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hx : ∀ j, |x j| ≤ r * v j)
    (hq : ∀ i, (Λ.mulVec v) i ≤ q * v i) (i : ι) :
    Tendsto (fun n => cascadeIter Λ x n i) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => q ^ n * r * v i) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (r * v i)
    simpa [mul_assoc] using this
  refine squeeze_zero_norm (fun n => ?_) h0
  simpa [Real.norm_eq_abs] using cascade_decay hΛ hr hq0 hx hq n i

end Chinukwe
