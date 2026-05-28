import Stokes.Global.CoverIndexedBulkLocalIntegral
import Stokes.Global.CoverIndexedNaturalConstructor
import Stokes.Global.BulkMeasureCanonicalLocalFacts

/-!
# Bulk support from compact-support local fields

This file closes the bulk-side support gap for the represented compact-support
route.

The mathematical point is simple: the scalar top-degree bulk integrand is a
coordinate of the exterior derivative of the chart representative, so its
topological support is contained in the topological support of that chart
representative.  The support-controlled local Stokes fields already put each
self-chart localized representative inside its assigned strict coordinate box;
therefore the corresponding self-chart bulk scalar is also supported in that
assigned box.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

open ManifoldForm

section BulkSupportFromCompact

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
The scalar bulk integrand has topological support contained in the
topological support of the chart representative from which it is computed.
-/
theorem bulkIntegrand_tsupport_subset_transitionPullbackInChart_tsupport
    (x0 x1 : M) (η : ManifoldForm I M n) :
    tsupport (fun y => bulkIntegrand I x0 x1 η y) ⊆
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 η) := by
  exact
    closure_minimal
      (bulkIntegrand_support_subset_tsupport
        (I := I) (x0 := x0) (x1 := x1) η)
      isClosed_closure

/--
If a chart representative is supported in `s`, then the associated scalar bulk
integrand is supported in `s`.
-/
theorem bulkIntegrand_tsupport_subset_of_transitionPullbackInChart_tsupport_subset
    {x0 x1 : M} {η : ManifoldForm I M n}
    {s : Set (Fin (n + 1) → Real)}
    (hsupp :
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 η) ⊆ s) :
    tsupport (fun y => bulkIntegrand I x0 x1 η y) ⊆ s :=
  (bulkIntegrand_tsupport_subset_transitionPullbackInChart_tsupport
    (I := I) x0 x1 η).trans hsupp

namespace SupportControlledCoverIndexedLocalStokesFields

/--
The localized self-chart representative attached to any selected cover index
is supported in that index's assigned strict coordinate box.
-/
theorem localized_tsupport_subset_assignedCoordinateBox
    (D : SupportControlledCoverIndexedLocalStokesFields P ω)
    (j : C.CoverIndex) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (C.assignedChart j) (C.assignedChart j)
          (P.coverIndexLocalizedForm ω j)) ⊆
      C.assignedCoordinateBox j := by
  rcases j with i | i
  · simpa [CompactSupportChartCoverSelection.assignedChart,
      CompactSupportChartCoverSelection.assignedCoordinateBox] using
      D.interiorLocalizedSupportSubset i
  · have hcoeff :
        tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.partition (Sum.inr i))) ∩
            D.boundaryCoordSupport i ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1) :=
      P.boundary_transitionCoefficient_inter_coordSupport_subset_box'
        (i := i) (coordSupport := D.boundaryCoordSupport i)
        (D.boundaryCoordMapsToSupport i) (D.boundaryCoordSubsetTarget i)
    have hsupp :
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (C.boundaryChart i.1) (C.boundaryChart i.1)
              (P.coverIndexLocalizedForm ω (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
      simpa [SupportControlledSelectedPartition.coverIndexLocalizedForm] using
        transitionPullbackInChart_localizedForm_tsupport_subset_halfSpaceSupportBox_of_coordSupport
          (I := I)
          (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
          (ρ := P.partition (Sum.inr i)) (ω := ω)
          (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
          (D.boundaryBaseSupport i) hcoeff
    simpa [CompactSupportChartCoverSelection.assignedChart,
      CompactSupportChartCoverSelection.assignedCoordinateBox] using hsupp

/--
Self-chart bulk scalar support for every cover index, in the exact assigned-box
shape used by the bulk local-integral and closed-carrier constructors.
-/
theorem bulkIntegrand_tsupport_subset_assignedCoordinateBox_self
    (D : SupportControlledCoverIndexedLocalStokesFields P ω)
    (j : C.CoverIndex) :
    tsupport
        (fun y =>
          bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
            (P.coverIndexLocalizedForm ω j) y) ⊆
      C.assignedCoordinateBox j :=
  bulkIntegrand_tsupport_subset_of_transitionPullbackInChart_tsupport_subset
    (I := I)
    (x0 := C.assignedChart j) (x1 := C.assignedChart j)
    (η := P.coverIndexLocalizedForm ω j)
    (D.localized_tsupport_subset_assignedCoordinateBox j)

/--
The self-chart local bulk term is the integral over the assigned strict box,
with the support hypothesis generated from the compact-support local fields.
-/
theorem localBulk_eq_setIntegral_assigned_self
    (D : SupportControlledCoverIndexedLocalStokesFields P ω)
    (j : C.CoverIndex) :
    P.coverIndexLocalBulkTerm ω j =
      ∫ y in C.assignedCoordinateBox j,
        bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
          (P.coverIndexLocalizedForm ω j) y :=
  P.coverIndexLocalBulkTerm_eq_setIntegral_assigned_self_of_tsupport_subset
    (C := C) (ω := ω)
    D.bulkIntegrand_tsupport_subset_assignedCoordinateBox_self j

end SupportControlledCoverIndexedLocalStokesFields

namespace CoverIndexedAssignedBoxLocalData

/--
Assigned-box local data produces the self-chart bulk support field expected by
the per-index assigned-chart bulk route.
-/
theorem bulkIntegrand_tsupport_subset_assignedCoordinateBox_self
    [IsManifold I ⊤ M]
    (D : CoverIndexedAssignedBoxLocalData C P ω)
    (j : C.CoverIndex) :
    tsupport
        (fun y =>
          bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
            (P.coverIndexLocalizedForm ω j) y) ⊆
      C.assignedCoordinateBox j :=
  D.toLocalFields.bulkIntegrand_tsupport_subset_assignedCoordinateBox_self j

/--
Assigned-box local data also gives the corresponding self-chart local
set-integral identity over the assigned strict box.
-/
theorem localBulk_eq_setIntegral_assigned_self
    [IsManifold I ⊤ M]
    (D : CoverIndexedAssignedBoxLocalData C P ω)
    (j : C.CoverIndex) :
    P.coverIndexLocalBulkTerm ω j =
      ∫ y in C.assignedCoordinateBox j,
        bulkIntegrand I (C.assignedChart j) (C.assignedChart j)
          (P.coverIndexLocalizedForm ω j) y :=
  D.toLocalFields.localBulk_eq_setIntegral_assigned_self j

end CoverIndexedAssignedBoxLocalData

end BulkSupportFromCompact

end Stokes

end
