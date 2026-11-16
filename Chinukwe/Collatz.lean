import Mathlib
import Chinukwe.PositiveSystems
import Chinukwe.Spectral

/-!
# Chinukwe.Collatz — the positive-vector bridge (core §5.1, Theorem 5.1(b))

No `sorry`: the Gelfand-type step ("all eigenvalues in the open unit disc ⇒ some power has
row sums < 1") is `Chinukwe.exists_pow_rowsum_lt_one_of_subUnit` in `Chinukwe.Spectral`.
Everything else here is elementary.

Spectral radius is encoded elementarily: `SubUnit Λ` says every complex eigenvalue
of Λ has modulus < 1, i.e. ρ(Λ) < 1 (ι is finite).

Chain proved here, for Λ ≥ 0:
  (P1) ∃ v > 0, q < 1, Λ v ≤ q v
  ⇒ SubUnit Λ                        -- Collatz–Wielandt upper bound   [proved]
  (P0) ∃ N > 0, every row sum of Λ^N is < 1
  ⇒ (P1)                             -- FINITE Neumann series          [proved]
  SubUnit Λ ⇒ (P0)                   -- Gelfand (Chinukwe.Spectral)    [proved]

Finite Neumann trick: v := Σ_{n<N} q⁻ⁿ Λⁿ 𝟙 with q^N ≥ max row sum of Λ^N.
Then Λ v = q (v − 𝟙 + q⁻ᴺ Λ^N 𝟙) ≤ q v, so no convergence/tsum is needed.
-/

open Finset

namespace Chinukwe

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pow_mulVec_succ (Λ : Matrix ι ι ℝ) (n : ℕ) (x : ι → ℝ) :
    (Λ ^ (n + 1)).mulVec x = Λ.mulVec ((Λ ^ n).mulVec x) := by
  rw [pow_succ', Matrix.mulVec_mulVec]

/-- Collatz–Wielandt upper bound: Λ ≥ 0, v > 0, Λ v ≤ q v ⇒ every eigenvalue has |λ| ≤ q. -/
theorem eigen_norm_le_of_positive_vector {Λ : Matrix ι ι ℝ}
    (hΛ : ∀ i j, 0 ≤ Λ i j) {v : ι → ℝ} {q : ℝ}
    (hv : ∀ i, 0 < v i) (hq : ∀ i, (Λ.mulVec v) i ≤ q * v i)
    (lam : ℂ) (w : ι → ℂ) (hw : w ≠ 0)
    (heig : ∀ i, ∑ j, (Λ i j : ℂ) * w j = lam * w i) : ‖lam‖ ≤ q := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i0, w i0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  haveI : Nonempty ι := ⟨i0⟩
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
  have hnorm : ‖lam‖ * ‖w i‖ ≤ r * (Λ.mulVec v) i := by
    calc ‖lam‖ * ‖w i‖ = ‖lam * w i‖ := (norm_mul _ _).symm
      _ = ‖∑ j, (Λ i j : ℂ) * w j‖ := by rw [heig i]
      _ ≤ ∑ j, ‖(Λ i j : ℂ) * w j‖ := norm_sum_le _ _
      _ = ∑ j, Λ i j * ‖w j‖ := Finset.sum_congr rfl fun j _ => by
          first
            | rw [norm_mul, Complex.norm_of_nonneg (hΛ i j)]
            | (rw [norm_mul]; simp [abs_of_nonneg (hΛ i j)])
      _ ≤ ∑ j, Λ i j * (r * v j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hwle j) (hΛ i j)
      _ = r * (Λ.mulVec v) i := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ‖lam‖ * ‖w i‖ ≤ q * ‖w i‖ := by
    calc ‖lam‖ * ‖w i‖ ≤ r * (Λ.mulVec v) i := hnorm
      _ ≤ r * (q * v i) := mul_le_mul_of_nonneg_left (hq i) hrpos.le
      _ = q * ‖w i‖ := by rw [hwi]; ring
  exact le_of_mul_le_mul_right h2 hwipos

theorem subUnit_of_positive_vector {Λ : Matrix ι ι ℝ} (hΛ : ∀ i j, 0 ≤ Λ i j)
    {v : ι → ℝ} {q : ℝ} (hv : ∀ i, 0 < v i) (hq1 : q < 1)
    (hq : ∀ i, (Λ.mulVec v) i ≤ q * v i) : SubUnit Λ := fun lam w hw heig =>
  lt_of_le_of_lt (eigen_norm_le_of_positive_vector hΛ hv hq lam w hw heig) hq1

/-- FINITE Neumann series: some power with all row sums < 1 gives a positive vector. -/
theorem exists_positive_vector_of_pow_rowsum_lt_one [Nonempty ι]
    {Λ : Matrix ι ι ℝ} (hΛ : ∀ i j, 0 ≤ Λ i j) {N : ℕ} (hN : 0 < N)
    (hrow : ∀ i, ((Λ ^ N).mulVec (fun _ => (1 : ℝ))) i < 1) :
    ∃ (v : ι → ℝ) (q : ℝ), (∀ i, 1 ≤ v i) ∧ 0 < q ∧ q < 1 ∧
      ∀ i, (Λ.mulVec v) i ≤ q * v i := by
  classical
  obtain ⟨u, hu_def⟩ : ∃ u : ℕ → ι → ℝ,
      ∀ n, u n = (Λ ^ n).mulVec (fun _ => (1 : ℝ)) := ⟨_, fun _ => rfl⟩
  have hu0 : ∀ i, u 0 i = 1 := by intro i; simp [hu_def]
  have hu_nonneg : ∀ n i, 0 ≤ u n i := by
    intro n i
    rw [hu_def]
    simp only [Matrix.mulVec, dotProduct, mul_one]
    exact Finset.sum_nonneg fun j _ => pow_entries_nonneg hΛ n i j
  have hu_succ : ∀ n, u (n + 1) = Λ.mulVec (u n) := by
    intro n; rw [hu_def, hu_def]; exact pow_mulVec_succ Λ n _
  have huN_lt : ∀ i, u N i < 1 := fun i => by rw [hu_def]; exact hrow i
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => u N i)
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = max (u N i₀) (1 / 2) := ⟨_, rfl⟩
  have hs_lt : s < 1 := by rw [hs_def]; exact max_lt (huN_lt i₀) (by norm_num)
  have hs_pos : 0 < s := by
    rw [hs_def]; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have huN : ∀ i, u N i ≤ s := fun i => by
    rw [hs_def]; exact (hi₀ i).trans (le_max_left _ _)
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = s ^ ((N : ℝ)⁻¹) := ⟨_, rfl⟩
  have hq_pos : 0 < q := by rw [hq_def]; exact Real.rpow_pos_of_pos hs_pos _
  have hq_lt : q < 1 := by
    rw [hq_def]
    exact Real.rpow_lt_one hs_pos.le hs_lt (inv_pos.2 (Nat.cast_pos.2 hN))
  have hqN : q ^ N = s := by
    rw [hq_def]; exact Real.rpow_inv_natCast_pow hs_pos.le hN.ne'
  have hqinv_nn : 0 ≤ q⁻¹ := inv_nonneg.2 hq_pos.le
  obtain ⟨v, hv⟩ : ∃ v : ι → ℝ, ∀ i, v i = ∑ n ∈ range N, q⁻¹ ^ n * u n i :=
    ⟨_, fun _ => rfl⟩
  refine ⟨v, q, ?_, hq_pos, hq_lt, ?_⟩
  · -- v ≥ 1 : the n = 0 term is 1, the rest are ≥ 0
    intro i
    rw [hv i]
    obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    rw [hm, Finset.sum_range_succ']
    have h0 : q⁻¹ ^ 0 * u 0 i = 1 := by simp [hu0]
    have hrest : 0 ≤ ∑ n ∈ range m, q⁻¹ ^ (n + 1) * u (n + 1) i :=
      Finset.sum_nonneg fun n _ => mul_nonneg (pow_nonneg hqinv_nn _) (hu_nonneg _ _)
    linarith
  · intro i
    -- (1) Λ v = Σ_{n<N} q⁻ⁿ u_{n+1}
    have hlin : (Λ.mulVec v) i = ∑ n ∈ range N, q⁻¹ ^ n * u (n + 1) i := by
      calc (Λ.mulVec v) i = ∑ j, Λ i j * v j := by simp [Matrix.mulVec, dotProduct]
        _ = ∑ j, Λ i j * ∑ n ∈ range N, q⁻¹ ^ n * u n j := by simp only [hv]
        _ = ∑ j, ∑ n ∈ range N, Λ i j * (q⁻¹ ^ n * u n j) := by
            simp only [Finset.mul_sum]
        _ = ∑ n ∈ range N, ∑ j, Λ i j * (q⁻¹ ^ n * u n j) := Finset.sum_comm
        _ = ∑ n ∈ range N, q⁻¹ ^ n * ∑ j, Λ i j * u n j := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ n ∈ range N, q⁻¹ ^ n * u (n + 1) i := by
            refine Finset.sum_congr rfl fun n _ => ?_
            rw [hu_succ n]
            simp [Matrix.mulVec, dotProduct]
    -- (2) telescoping
    have hmq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq_pos.ne'
    have h1 : ∑ n ∈ range N, q⁻¹ ^ n * u (n + 1) i
        = q * ∑ n ∈ range N, q⁻¹ ^ (n + 1) * u (n + 1) i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [pow_succ]
      calc q⁻¹ ^ n * u (n + 1) i
          = (q * q⁻¹) * (q⁻¹ ^ n * u (n + 1) i) := by rw [hmq, one_mul]
        _ = q * (q⁻¹ ^ n * q⁻¹ * u (n + 1) i) := by ring
    have h2 : ∑ n ∈ range (N + 1), q⁻¹ ^ n * u n i
        = ∑ n ∈ range N, q⁻¹ ^ (n + 1) * u (n + 1) i + q⁻¹ ^ 0 * u 0 i :=
      Finset.sum_range_succ' _ _
    have h3 : ∑ n ∈ range (N + 1), q⁻¹ ^ n * u n i
        = ∑ n ∈ range N, q⁻¹ ^ n * u n i + q⁻¹ ^ N * u N i :=
      Finset.sum_range_succ _ _
    have key : ∑ n ∈ range N, q⁻¹ ^ (n + 1) * u (n + 1) i
        = ∑ n ∈ range N, q⁻¹ ^ n * u n i + q⁻¹ ^ N * u N i - u 0 i := by
      rw [pow_zero, one_mul] at h2
      linarith
    -- (3) q⁻ᴺ u_N ≤ q⁻ᴺ s = 1
    have hcN : q⁻¹ ^ N * u N i ≤ 1 := by
      have e : q⁻¹ ^ N * s = 1 := by
        rw [← hqN, ← mul_pow, inv_mul_cancel₀ hq_pos.ne', one_pow]
      calc q⁻¹ ^ N * u N i ≤ q⁻¹ ^ N * s :=
            mul_le_mul_of_nonneg_left (huN i) (pow_nonneg hqinv_nn _)
        _ = 1 := e
    rw [hlin, h1, key, hv i]
    have hle : ∑ n ∈ range N, q⁻¹ ^ n * u n i + q⁻¹ ^ N * u N i - u 0 i
        ≤ ∑ n ∈ range N, q⁻¹ ^ n * u n i := by
      have := hu0 i
      linarith
    exact mul_le_mul_of_nonneg_left hle hq_pos.le

/-- Theorem 5.1(b): for Λ ≥ 0, ρ(Λ) < 1 ⇔ a positive vector with Λ v ≤ q v, q < 1. -/
theorem positive_vector_iff_subUnit [Nonempty ι] {Λ : Matrix ι ι ℝ}
    (hΛ : ∀ i j, 0 ≤ Λ i j) :
    (∃ (v : ι → ℝ) (q : ℝ), (∀ i, 0 < v i) ∧ q < 1 ∧
        ∀ i, (Λ.mulVec v) i ≤ q * v i) ↔ SubUnit Λ := by
  constructor
  · rintro ⟨v, q, hv, hq1, hq⟩
    exact subUnit_of_positive_vector hΛ hv hq1 hq
  · intro hspec
    obtain ⟨N, hN, hrow⟩ := exists_pow_rowsum_lt_one_of_subUnit hΛ hspec
    obtain ⟨v, q, hv1, _, hq1, hq⟩ :=
      exists_positive_vector_of_pow_rowsum_lt_one hΛ hN hrow
    exact ⟨v, q, fun i => lt_of_lt_of_le one_pos (hv1 i), hq1, hq⟩

end Chinukwe
