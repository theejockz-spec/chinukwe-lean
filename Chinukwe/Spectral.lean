import Mathlib

/-!
# Chinukwe.Spectral — spectral radius < 1 ⇒ some power has row sums < 1

Closes the Gelfand step used by `Chinukwe.Collatz`. Compiled on Lean v4.36.0-rc2.

`SubUnit Λ` encodes ρ(Λ) < 1 through eigenvalues: every complex eigenvalue has modulus < 1.

Proof (all steps from current Mathlib):
 1. Complexify Λ to M and give `Matrix ι ι ℂ` the L∞-operator norm
    (`open scoped Matrix.Norms.Operator`), making it a complex Banach algebra.
 2. spectrum ℂ M = eigenvalues (`Matrix.toLinAlgEquiv'`, `Module.End.hasEigenvalue_iff_mem_spectrum`),
    so `SubUnit` gives ‖z‖₊ < 1 on the spectrum, hence `spectralRadius ℂ M < 1`.
 3. Gelfand's formula: ‖M^n‖₊^(1/n) → spectralRadius < 1, so ‖M^N‖₊ < 1 for some N ≥ 1.
 4. ‖·‖₊ is the maximal row sum of norms; for the nonnegative Λ^N it equals (Λ^N 𝟙)ᵢ.
-/

namespace Chinukwe

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- ρ(Λ) < 1, stated through eigenvalues. -/
def SubUnit (Λ : Matrix ι ι ℝ) : Prop :=
  ∀ (lam : ℂ) (w : ι → ℂ), w ≠ 0 →
    (∀ i, ∑ j, (Λ i j : ℂ) * w j = lam * w i) → ‖lam‖ < 1

lemma pow_entries_nonneg {Λ : Matrix ι ι ℝ} (hΛ : ∀ i j, 0 ≤ Λ i j) (n : ℕ) :
    ∀ i j, 0 ≤ (Λ ^ n) i j := by
  induction n with
  | zero =>
    intro i j
    rw [pow_zero]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ n ih =>
    intro i j
    rw [pow_succ']
    simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hΛ i k) (ih k j)

section Gelfand

open scoped Matrix.Norms.Operator NNReal Topology ENNReal
open Filter Finset

/-- Some power of a nonnegative matrix with spectral radius < 1 has all row sums < 1. -/
theorem exists_pow_rowsum_lt_one_of_subUnit [Nonempty ι] {Λ : Matrix ι ι ℝ} (hΛ : ∀ i j, 0 ≤ Λ i j)
    (hspec : SubUnit Λ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ((Λ ^ N).mulVec (fun _ => (1 : ℝ))) i < 1 := by
  classical
  -- 1. complexification
  obtain ⟨M, hM⟩ : ∃ M : Matrix ι ι ℂ, M = Complex.ofRealHom.mapMatrix Λ := ⟨_, rfl⟩
  have hMentry : ∀ i j, M i j = (Λ i j : ℂ) := by
    intro i j; rw [hM]; simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  have hMpow : ∀ n : ℕ, M ^ n = Complex.ofRealHom.mapMatrix (Λ ^ n) := by
    intro n; rw [hM]; exact (map_pow Complex.ofRealHom.mapMatrix Λ n).symm
  -- 2. spectral radius < 1
  have hrad : spectralRadius ℂ M < 1 := by
    have h := spectrum.spectralRadius_lt_of_forall_lt M (r := 1) (by
      intro z hz
      have hz' : z ∈ spectrum ℂ (Matrix.toLinAlgEquiv' M) := by
        rw [AlgEquiv.spectrum_eq]; exact hz
      have hev : Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' M) z :=
        Module.End.hasEigenvalue_iff_mem_spectrum.2 hz'
      obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
      have hw0 : w ≠ 0 := hw.2
      have happ : (Matrix.toLinAlgEquiv' M) w = z • w := hw.apply_eq_smul
      have hmul : M.mulVec w = z • w := by
        first
          | exact happ
          | simpa [Matrix.toLinAlgEquiv', Matrix.toLin'_apply] using happ
      have heig : ∀ i, ∑ j, (Λ i j : ℂ) * w j = z * w i := by
        intro i
        have := congrFun hmul i
        simpa [Matrix.mulVec, dotProduct, hMentry, smul_eq_mul] using this
      have hlt : ‖z‖ < 1 := hspec z w hw0 heig
      exact_mod_cast hlt)
    simpa using h
  -- 3. Gelfand's formula
  have hlim := spectrum.pow_nnNorm_pow_one_div_tendsto_nhds_spectralRadius M
  have hev : ∀ᶠ n : ℕ in atTop, (‖M ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) < 1 :=
    hlim.eventually (gt_mem_nhds hrad)
  obtain ⟨N, hN1, hN2⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hNpos : (0 : ℝ) < 1 / (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN2
    positivity
  have hnorm : ‖M ^ N‖₊ < 1 := by
    by_contra hge
    have h1 : (1 : ℝ≥0∞) ≤ (‖M ^ N‖₊ : ℝ≥0∞) := by exact_mod_cast not_lt.1 hge
    exact absurd hN1 (not_lt.2 (ENNReal.one_le_rpow h1 hNpos))
  -- 4. row sums
  refine ⟨N, hN2, fun i => ?_⟩
  have hentry : ∀ j, ‖(M ^ N) i j‖ = (Λ ^ N) i j := by
    intro j
    have hnn := pow_entries_nonneg hΛ N i j
    simp [hMpow N, RingHom.mapMatrix_apply, Matrix.map_apply, abs_of_nonneg hnn]
  have hsum_le : ∑ j, ‖(M ^ N) i j‖₊ ≤ ‖M ^ N‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ j, ‖(M ^ N) i j‖₊) (Finset.mem_univ i)
  calc ((Λ ^ N).mulVec (fun _ => (1 : ℝ))) i
      = ∑ j, (Λ ^ N) i j := by simp [Matrix.mulVec, dotProduct]
    _ = ∑ j, ‖(M ^ N) i j‖ := Finset.sum_congr rfl fun j _ => (hentry j).symm
    _ = ((∑ j, ‖(M ^ N) i j‖₊ : ℝ≥0) : ℝ) := by simp [NNReal.coe_sum]
    _ ≤ ((‖M ^ N‖₊ : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 hsum_le
    _ < 1 := by exact_mod_cast hnorm

end Gelfand

end Chinukwe
