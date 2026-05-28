import Stokes.Global.CoverIndexedZeroCompactLocalizedPartitionSupport
import Stokes.Global.CoverIndexedZeroCompactRelativeTargetBox
import Stokes.Global.CoverIndexedZeroCompactTargetBoxSelection
import Stokes.BoundaryChart.SelectedBoxImageConstructor
import Stokes.BoundaryChart.TargetBoxCompactImage

/-!
# Geometry API audit for compact zero endpoints

This file is intentionally small and executable.  It records, as `#check`
anchors and projection lemmas, where the current boundary-chart geometry API
stores the image-containment and local-inverse facts needed by the compact
represented Stokes route.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section SingleChartAudit

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d : Fin (n + 1) → Real}
variable {omega : ManifoldForm I M n}

/-- `boundaryChartCompactImageBoxSelection` is exactly source-box image
containment in the selected target lower-zero box. -/
theorem boundaryChartCompactImageBoxSelection.source_image_subset_targetBox
    (hcompact : boundaryChartCompactImageBoxSelection I x0 x1 a b c d) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
      lowerZeroFaceDomain c d :=
  hcompact

/-- `boundaryChartSelectedBoxImageData` also projects to source-image
containment, via its `MapsTo` half. -/
theorem boundaryChartSelectedBoxImageData.source_image_subset_targetBox
    (himage : boundaryChartSelectedBoxImageData I x0 x1 a b c d) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
      lowerZeroFaceDomain c d := by
  intro y hy
  rcases hy with ⟨u, hu, rfl⟩
  exact himage.mapsTo hu

namespace BoundaryChartTargetBoxSelection

/-- A selected target box already contains the source-box image containment
needed for boundary change of variables. -/
theorem source_image_subset_selectedTargetBox
    (D : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
      lowerZeroFaceDomain D.lowerCorner D.upperCorner :=
  D.compactImage

/-- The same fact in `MapsTo` form. -/
theorem mapsTo_sourceBox_selectedTargetBox
    (D : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    MapsTo (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (lowerZeroFaceDomain D.lowerCorner D.upperCorner) :=
  D.compactImage.mapsTo

/-- The selected target box also stores the local-inverse/surjectivity half. -/
theorem surjOn_sourceBox_selectedTargetBox
    (D : BoundaryChartTargetBoxSelection I x0 x1 a b) :
    SurjOn (boundaryChartTransition I x0 x1)
      (lowerZeroFaceDomain a b)
      (lowerZeroFaceDomain D.lowerCorner D.upperCorner) :=
  D.localInverse.surjOn

end BoundaryChartTargetBoxSelection

namespace BoundaryChartSelectedBoxImageConstructorData

/-- The unified selected-box constructor exposes source-image containment
through `targetSelection.compactImage`. -/
theorem source_image_subset_targetBox
    (D : BoundaryChartSelectedBoxImageConstructorData I x0 x1 omega a b) :
    (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
      lowerZeroFaceDomain D.targetLowerCorner D.targetUpperCorner :=
  D.compactImage

end BoundaryChartSelectedBoxImageConstructorData

end SingleChartAudit

section CoverIndexedAudit

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedBoundaryTargetBoxData

variable
    (D : CoverIndexedBoundaryTargetBoxData (I := I) (K := K) C P omega)

/-- Cover-indexed projection: the per-boundary selected target box stores
image containment of the selected source boundary box. -/
theorem source_image_subset_targetBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    (boundaryChartTransition I (C.boundaryChart i.1) (D.targetChart i)) ''
        lowerZeroFaceDomain (C.boundaryLower i.1) (C.boundaryUpper i.1) ⊆
      lowerZeroFaceDomain (D.targetLower i) (D.targetUpper i) :=
  (D.targetSelection i).compactImage

/-- Cover-indexed projection: the local inverse data stores an actual inverse
map, its `MapsTo` field, and the pointwise right-inverse identity. -/
theorem exists_localInverse_mapsTo_sourceBox
    (i : {x : M // x ∈ C.boundaryCenters}) :
    ∃ g : (Fin n → Real) → (Fin n → Real),
      MapsTo g
        (lowerZeroFaceDomain (D.targetLower i) (D.targetUpper i))
        (lowerZeroFaceDomain (C.boundaryLower i.1) (C.boundaryUpper i.1)) ∧
        ∀ y ∈ lowerZeroFaceDomain (D.targetLower i) (D.targetUpper i),
          boundaryChartTransition I (C.boundaryChart i.1) (D.targetChart i) (g y) = y :=
  (D.targetSelection i).localInverse

end CoverIndexedBoundaryTargetBoxData

namespace CoverIndexedZeroCompactRelativeTargetBoxData

variable
    {transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega}

/-- The `targetBox_subset_target` field is not stored in
`BoundaryChartTargetBoxSelection`; it is stored in the compact relative
target-box package after adding target-chart neighborhood/box data. -/
theorem selectedTargetBox_subset_extChartTarget
    (D :
      CoverIndexedZeroCompactRelativeTargetBoxData
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData)
    (i : {x : M // x ∈ C.boundaryCenters}) :
    Icc (D.targetBox.targetLower i) (D.targetBox.targetUpper i) ⊆
      (extChartAt I (D.targetBox.targetChart i)).target :=
  D.targetBox_subset_target i

end CoverIndexedZeroCompactRelativeTargetBoxData

end CoverIndexedAudit

end Stokes

end
