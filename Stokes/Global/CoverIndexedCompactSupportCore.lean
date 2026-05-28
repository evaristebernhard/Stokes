import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Cover-indexed compact-support Stokes core

This file records the final finite-index algebra for the cover-indexed route.
The analytic work is deliberately kept outside this file:

* bulk reconstruction identifies the global bulk integral with a finite sum of
  local bulk terms;
* local Stokes identifies each local bulk term with the corresponding true
  boundary term;
* boundary reconstruction identifies that finite boundary sum with the global
  boundary integral.

The theorem below is the small algebraic hinge where these three facts become
the compact-support Stokes equality.
-/

noncomputable section

open scoped BigOperators

namespace Stokes

section CoverIndexedCompactSupportCore

universe u

/--
Finite-index data sufficient for the final algebraic assembly of the
compact-support Stokes equality.

The index type is intentionally arbitrary: later files can instantiate it with
the mixed chart-box cover index instead of forcing the old `M`-indexed selected
partition shape.
-/
structure CoverIndexedStokesSums (ι : Type u) where
  /-- Finite family of local pieces. -/
  active : Finset ι
  /-- Represented global bulk integral, i.e. the integral of `dω`. -/
  globalBulk : Real
  /-- Represented global boundary integral. -/
  globalBoundary : Real
  /-- Local bulk term attached to each cover piece. -/
  localBulk : ι -> Real
  /-- True boundary term attached to each cover piece. -/
  localBoundary : ι -> Real
  /-- Bulk reconstruction. -/
  globalBulk_eq_localBulkSum :
    globalBulk = active.sum localBulk
  /-- Boundary reconstruction. -/
  localBoundarySum_eq_globalBoundary :
    active.sum localBoundary = globalBoundary
  /-- Local Stokes on each active piece after artificial faces vanish. -/
  localBulk_eq_localBoundary :
    forall i, i ∈ active -> localBulk i = localBoundary i

namespace CoverIndexedStokesSums

variable {ι : Type u}

/-- Local Stokes summed over all active cover pieces. -/
theorem localBulkSum_eq_localBoundarySum
    (D : CoverIndexedStokesSums ι) :
    D.active.sum D.localBulk = D.active.sum D.localBoundary := by
  exact Finset.sum_congr rfl D.localBulk_eq_localBoundary

/--
The cover-indexed compact-support Stokes equality once the three finite-sum
ingredients have been constructed.
-/
theorem stokes (D : CoverIndexedStokesSums ι) :
    D.globalBulk = D.globalBoundary := by
  calc
    D.globalBulk = D.active.sum D.localBulk :=
      D.globalBulk_eq_localBulkSum
    _ = D.active.sum D.localBoundary :=
      D.localBulkSum_eq_localBoundarySum
    _ = D.globalBoundary :=
      D.localBoundarySum_eq_globalBoundary

end CoverIndexedStokesSums

end CoverIndexedCompactSupportCore

end Stokes

end
