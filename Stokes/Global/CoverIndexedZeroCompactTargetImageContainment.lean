import Stokes.Global.CoverIndexedZeroCompactLocalizedPartitionSupport
import Stokes.Global.CoverIndexedBoundaryTargetSupportFromImage

/-!
# Target-image containment for compact zero endpoints

This file isolates the geometric containment needed after localized partition
support has put a boundary piece inside its selected source boundary
chart-box.  Selected boundary target-image data controls the lower-zero face.
For a whole half-space source neighborhood, the honest input is a `MapsTo`
statement for the ambient chart transition on that source half-space box.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section TargetImageContainment

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}

namespace BoundaryChartTargetBoxSelection

variable {x0 x1 : M}
variable {a b : Fin (n + 1) -> Real}

/-- A selected target boundary box sends the ambient re-embedded lower-zero
boundary image into its ambient target `Icc`. -/
theorem ambientBoundaryImage_subset_Icc
    (target : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    boundaryChartTransitionAmbientBoundaryImage I x0 x1 a b ⊆
      Icc target.lowerCorner target.upperCorner :=
  boundaryChartTransitionAmbientBoundaryImage_subset_Icc_of_imageData
    (I := I) target.lowerCorner_zero target.lower_le_upper target.imageData

end BoundaryChartTargetBoxSelection

/-- If the ambient chart transition maps a selected source half-space support
box into a target coordinate box, then the corresponding manifold-side
boundary chart-box neighborhood is contained in the target-chart preimage of
that box. -/
theorem boundaryChartBoxNeighborhood_subset_targetPreimage_of_chartTransition_mapsTo
    {x0 x1 : M} {a b c d : Fin (n + 1) -> Real}
    (hmap :
      MapsTo (ManifoldForm.chartTransition I x0 x1)
        (halfSpaceSupportBox a b) (Icc c d)) :
    boundaryChartBoxNeighborhood I x0 a b ⊆
      {p : M | (extChartAt I x1) p ∈ Icc c d} := by
  intro p hp
  rcases hp with ⟨hpsource, hpbox⟩
  have htarget :
      ManifoldForm.chartTransition I x0 x1 ((extChartAt I x0) p) ∈ Icc c d :=
    hmap hpbox
  have hleft :
      (extChartAt I x0).symm ((extChartAt I x0) p) = p :=
    (extChartAt I x0).left_inv hpsource
  rw [ManifoldForm.chartTransition, hleft] at htarget
  exact htarget

section CoverIndexed

variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

variable
  (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- Cover-indexed target-preimage containment produced from ambient chart
transition `MapsTo` data on the selected boundary half-space source boxes. -/
theorem boundaryChartBox_subset_targetPreimage_of_chartTransition_mapsTo
    (hmap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        MapsTo
          (ManifoldForm.chartTransition I
            (C.boundaryChart i.1) (D.targetChart i))
          (halfSpaceSupportBox (C.boundaryLower i.1)
            (C.boundaryUpper i.1))
          (Icc (D.targetLower i) (D.targetUpper i))) :
    ∀ i : {x : M // x ∈ C.boundaryCenters},
      boundaryChartBoxNeighborhood I (C.boundaryChart i.1)
          (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
        {p : M | (extChartAt I (D.targetChart i)) p ∈
          Icc (D.targetLower i) (D.targetUpper i)} := by
  intro i
  exact
    boundaryChartBoxNeighborhood_subset_targetPreimage_of_chartTransition_mapsTo
      (I := I) (x0 := C.boundaryChart i.1) (x1 := D.targetChart i)
      (a := C.boundaryLower i.1) (b := C.boundaryUpper i.1)
      (c := D.targetLower i) (d := D.targetUpper i)
      (hmap i)

/-- Direct compact-zero support field from global support and ambient
source-box-to-target-box chart-transition containment. -/
theorem targetInChartZero_tsupport_subset_Icc_of_chartTransition_mapsTo
    (homegaSupport : ManifoldForm.support I omega ⊆ K)
    (hmap :
      ∀ i : {x : M // x ∈ C.boundaryCenters},
        MapsTo
          (ManifoldForm.chartTransition I
            (C.boundaryChart i.1) (D.targetChart i))
          (halfSpaceSupportBox (C.boundaryLower i.1)
            (C.boundaryUpper i.1))
          (Icc (D.targetLower i) (D.targetUpper i))) :
    D.TargetInChartZeroTSupportSubsetIccField :=
  D.targetInChartZero_tsupport_subset_Icc_of_boundaryBox_subset_preimage
    (I := I) (K := K) (C := C) (P := P) (ω := omega)
    homegaSupport
    (D.boundaryChartBox_subset_targetPreimage_of_chartTransition_mapsTo
      (I := I) (K := K) (C := C) (P := P) (omega := omega) hmap)

end CoverIndexedBoundaryTargetBoxData

end CoverIndexed

end TargetImageContainment

end Stokes

end
