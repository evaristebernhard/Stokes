import Stokes.Global.CoverIndexedZeroCompactRepresentedStokesRaw
import Stokes.Global.CoverIndexedZeroCompactRelativeOpenCover

/-!
# Ambient-open lift for raw compact-support represented Stokes

This file builds the manifold-side open-cover data needed by the raw
selected-cover route directly from the coordinate `openPart`s of the generated
finite half-space cover.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section RawAmbientOpen

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable [FiniteDimensional Real (Fin (n + 1) → Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

namespace CoverIndexedZeroCompactRepresentedStokesRawInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesRawInput
        (I := I) (K := K) (ω := ω) C)

/-- The canonical manifold-side ambient open set associated to one generated
finite half-space `openPart`.  It is the selected boundary cover set, restricted
to the source chart, intersected with the chart preimage of the coordinate
open part. -/
def ambientOpenPartPreimage
    (_i : CoverIndexedBoundaryIndex (I := I) C)
    (q :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).BoundaryPiece (I := I) (K := K)) :
    Set M :=
  let F :=
    (X.generatedFromRaw
      (I := I) (K := K) (ω := ω)).finiteHalfSpaceCover
        (I := I) (K := K) (C := C)
  C.assignedCoverSet (Sum.inr q.1) ∩
    ((extChartAt I (C.boundaryChart q.1.1)).source ∩
      (extChartAt I (C.boundaryChart q.1.1)) ⁻¹'
        F.openPart q.1 q.2)

/-- The canonical `openPart` ambient lift is open on the manifold side. -/
theorem isOpen_ambientOpenPartPreimage
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).BoundaryPiece (I := I) (K := K))
    (_hq :
      q ∈ (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).boundaryPieces
          (I := I) (K := K) i) :
    IsOpen (X.ambientOpenPartPreimage (I := I) (K := K) (ω := ω) i q) := by
  classical
  let G := X.generatedFromRaw (I := I) (K := K) (ω := ω)
  let F := G.finiteHalfSpaceCover (I := I) (K := K) (C := C)
  have hassigned : IsOpen (C.assignedCoverSet (Sum.inr q.1)) :=
    X.base.assignedCoverSet_isOpen (Sum.inr q.1)
  have hopenPart : IsOpen (F.openPart q.1 q.2) :=
    F.isOpen_openPart q.1 q.2
  have hchart :
      IsOpen
        ((extChartAt I (C.boundaryChart q.1.1)).source ∩
          (extChartAt I (C.boundaryChart q.1.1)) ⁻¹'
            F.openPart q.1 q.2) :=
    isOpen_extChartAt_preimage' (I := I) (x := C.boundaryChart q.1.1) hopenPart
  simpa [ambientOpenPartPreimage, G, F] using hassigned.inter hchart

/-- Active carrier points are covered by the manifold-side `openPart`
preimages selected from the generated finite half-space cover. -/
theorem activeCarrier_subset_iUnion_ambientOpenPartPreimage
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    (X.generatedFromRaw
      (I := I) (K := K) (ω := ω)).activeCarrier (I := I) (K := K) i ⊆
      ⋃ q ∈
        (X.generatedFromRaw
          (I := I) (K := K) (ω := ω)).boundaryPieces
            (I := I) (K := K) i,
        X.ambientOpenPartPreimage (I := I) (K := K) (ω := ω) i q := by
  classical
  let G := X.generatedFromRaw (I := I) (K := K) (ω := ω)
  let P := X.selectedPartition (I := I) (K := K) (ω := ω)
  let F := G.finiteHalfSpaceCover (I := I) (K := K) (C := C)
  intro x hx
  have hxP : x ∈ P.boundaryActiveCarrier (I := I) i := by
    simpa [G, CoverIndexedZeroCompactFromCollarGenerated.activeCarrier, P] using hx
  have hycoord :
      (extChartAt I (C.boundaryChart i.1)) x ∈
        G.coordCarrier (I := I) (K := K) i := by
    refine ⟨x, ?_, rfl⟩
    simpa [G, CoverIndexedZeroCompactFromCollarGenerated.coordCarrier, P,
      SupportControlledSelectedPartition.boundaryActiveCoordCarrier] using hxP
  have hcover :
      (extChartAt I (C.boundaryChart i.1)) x ∈
        ⋃ q : {q // q ∈ F.activePieces i}, F.openPart i q.1 :=
    F.carrier_subset_iUnion_openPart i hycoord
  rcases mem_iUnion.mp hcover with ⟨q, hxopen⟩
  let qflat :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).BoundaryPiece (I := I) (K := K) :=
    ⟨i, q.1⟩
  have hqflat :
      qflat ∈ G.boundaryPieces (I := I) (K := K) i := by
    simp [qflat, G, CoverIndexedZeroCompactFromCollarGenerated.boundaryPieces,
      CoverIndexedFiniteHalfSpaceBoxCover.sigmaBoundaryPieces]
  refine mem_iUnion_of_mem qflat ?_
  refine mem_iUnion_of_mem hqflat ?_
  have hxassigned :
      x ∈ C.assignedCoverSet (Sum.inr i) := by
    simpa [P] using
      P.boundaryActiveCarrier_subset_assigned (I := I) i hxP
  have hxsource :
      x ∈ (extChartAt I (C.boundaryChart i.1)).source :=
    (P.boundaryActiveCarrier_subset_chart_source (I := I) i hxP)
  exact
    ⟨by simpa [qflat] using hxassigned,
      ⟨by simpa [qflat] using hxsource, by simpa [qflat] using hxopen⟩⟩

/-- Each canonical manifold-side `openPart` lift lies in the corresponding
generated boundary chart box. -/
theorem ambientOpenPartPreimage_subset_boundaryChartBox
    (i : CoverIndexedBoundaryIndex (I := I) C)
    (q :
      (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).BoundaryPiece (I := I) (K := K))
    (hq :
      q ∈ (X.generatedFromRaw
        (I := I) (K := K) (ω := ω)).boundaryPieces
          (I := I) (K := K) i) :
    X.ambientOpenPartPreimage (I := I) (K := K) (ω := ω) i q ⊆
      boundaryChartBoxNeighborhood I
        ((X.generatedFromRaw
          (I := I) (K := K) (ω := ω)).sourceChart
            (I := I) (K := K) i q)
        ((X.generatedFromRaw
          (I := I) (K := K) (ω := ω)).lower
            (I := I) (K := K) i q)
        ((X.generatedFromRaw
          (I := I) (K := K) (ω := ω)).upper
            (I := I) (K := K) i q) := by
  classical
  let G := X.generatedFromRaw (I := I) (K := K) (ω := ω)
  let F := G.finiteHalfSpaceCover (I := I) (K := K) (C := C)
  intro x hx
  have hqF : q ∈ F.sigmaBoundaryPieces i := by
    simpa [G, CoverIndexedZeroCompactFromCollarGenerated.boundaryPieces, F] using hq
  have hactive : q.2 ∈ F.activePieces q.1 :=
    F.sigmaBoundaryPieces_active hqF
  have hxassigned :
      x ∈ C.assignedCoverSet (Sum.inr q.1) := hx.1
  have hxsource :
      x ∈ (extChartAt I (C.boundaryChart q.1.1)).source := hx.2.1
  have hxopen :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈ F.openPart q.1 q.2 := hx.2.2
  have hxupper :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈ upperHalfSpace n := by
    have hbox :
        (extChartAt I (C.boundaryChart q.1.1)) x ∈
          halfSpaceSupportBox (C.boundaryLower q.1.1) (C.boundaryUpper q.1.1) := by
      simpa [CompactSupportChartCoverSelection.assignedCoverSet,
        boundaryChartBoxNeighborhood] using hxassigned.2
    have hzero : C.boundaryLower q.1.1 0 = 0 :=
      C.boundary_lower_zero q.1.1 q.1.2
    simpa [upperHalfSpace, hzero] using hbox.1
  have hbox :
      (extChartAt I (C.boundaryChart q.1.1)) x ∈
        halfSpaceSupportBox (F.lowerCorner q.1 q.2) (F.upperCorner q.1 q.2) := by
    exact
      upperHalfSpace_inter_halfSpaceSupportBoxOpenPart_subset
        (n := n)
        (a := F.lowerCorner q.1 q.2)
        (b := F.upperCorner q.1 q.2)
        (by
          simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces,
            CoverIndexedFiniteHalfSpaceBoxCover.lowerCorner] using
            (F.cover q.1).lowerCorner_zero q.2 hactive)
        ⟨hxupper, by simpa [CoverIndexedFiniteHalfSpaceBoxCover.openPart] using hxopen⟩
  exact
    ⟨by simpa [G, CoverIndexedZeroCompactFromCollarGenerated.sourceChart] using hxsource,
      by
        simpa [G, F, CoverIndexedZeroCompactFromCollarGenerated.sourceChart,
          CoverIndexedZeroCompactFromCollarGenerated.lower,
          CoverIndexedZeroCompactFromCollarGenerated.upper,
          boundaryChartBoxNeighborhood] using hbox⟩

/-- Canonical ambient-open lift for the raw selected-cover route, built from
the generated finite half-space cover's coordinate `openPart`s. -/
def ambientOpenDataOfOpenPartPreimage :
    (X.generatedFromRaw
      (I := I) (K := K) (ω := ω)).FiniteCoverAmbientOpenData
        (I := I) (K := K) (C := C)
        (P := X.selectedPartition (I := I) (K := K) (ω := ω)) where
  ambientOpen :=
    X.ambientOpenPartPreimage (I := I) (K := K) (ω := ω)
  ambientOpen_isOpen :=
    X.isOpen_ambientOpenPartPreimage (I := I) (K := K) (ω := ω)
  activeCarrier_subset_iUnion_ambientOpen :=
    X.activeCarrier_subset_iUnion_ambientOpenPartPreimage
      (I := I) (K := K) (ω := ω)
  ambientOpen_subset_boundaryChartBox :=
    X.ambientOpenPartPreimage_subset_boundaryChartBox
      (I := I) (K := K) (ω := ω)

end CoverIndexedZeroCompactRepresentedStokesRawInput

end RawAmbientOpen

end Stokes

end
