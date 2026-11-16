import Chinukwe.FixedPoint
import Chinukwe.Collatz

/-!
# Conjectures.SpectralFixedPoint — Theorem 4.4 (spectral form)

Target statement, NOT proved. Lives outside the core library so no core module can depend
on it. Planned proof: show some iterate `T^[N]` is a row-sum contraction (via `Collatz`),
apply Banach to `T^[N]`, and transfer uniqueness to `T`.
-/

namespace Conjectures

open Chinukwe

theorem spectral_exists_unique_fixedPoint {ι : Type*} [Fintype ι] (P : CritParams ι)
    (hM : SubUnit (Matrix.of fun i j => P.c i / P.μ i ^ 2 * P.κ i j)) :
    ∃! d : ι → ℝ, P.T d = d := by
  sorry

end Conjectures
