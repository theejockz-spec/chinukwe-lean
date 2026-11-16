import Mathlib

/-!
# Chinukwe.Empirical.Provenance

The ONLY place empirical values and source claims may live.

Rules (checked by `scripts/check.sh`):
* The core never imports this module.
* Nothing here is an `axiom`.
* An estimate is data with provenance and a verification status, not a hypothesis of any
  core theorem. Core theorems take parameters as hypotheses (`hβ : ∀ i, 0 < β i`).
* No entries yet: Table 4.2 of the Sixth Edition is pending primary-source re-verification.
  Add an entry only with `status := .verified` and a complete provenance record.
-/

namespace Chinukwe.Empirical

inductive Status
  | verified
  | pending
  | withdrawn
  deriving Repr, DecidableEq

structure Provenance where
  source : String      -- full citation
  outcome : String     -- outcome variable (e.g. all-cause mortality)
  contrast : String    -- exposure contrast (e.g. isolated vs. not, per SD, quartiles)
  statistic : String   -- HR, log-HR, correlation, ...
  status : Status
  deriving Repr

structure Estimate where
  name : String
  value : ℝ
  prov : Provenance

end Chinukwe.Empirical
