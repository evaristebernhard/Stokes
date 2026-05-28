import Stokes.Global.CoverIndexedZeroCompactFromCollarGenerated
import Stokes.Global.CoverIndexedZeroCompactFromCollarPartition
import Stokes.Global.CoverIndexedZeroCompactFromCollarSmoothness
import Stokes.Global.CoverIndexedZeroCompactFromCollarEndpoint
import Stokes.Global.CoverIndexedZeroCompactFromCollarImageControl

/-!
# Natural compact-support represented Stokes from collar-generated data

This module compresses the large from-collar certificate into a theorem-facing
input.  The final input no longer asks callers to provide a hand-built
`smoothRefinement`, `refinedPartition`, transition-coordinate smoothness
fields, image-control family, or endpoint adapter.  These are generated from:

* the natural boundary active carriers and collar-prism geometry;
* a small manifold-side ambient-open lift for the finite collar cover;
* source/target chart compatibility and source-chart coefficient smoothness;
* whole-box closed-preimage image control.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalCore

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
Core generated data for the natural compact-support represented Stokes route.

This is the mathematical part that turns collar-compatible boundary active
carriers into the refined half-space boxes consumed by local Stokes.  The
remaining fields are the honest chart-transition compatibility assumptions
needed to use those boxes as source boxes.
-/
structure CoverIndexedZeroCompactRepresentedStokesNaturalCore where
  /-- Natural collar-generated finite-cover data. -/
  generated :
    CoverIndexedZeroCompactFromCollarGenerated (I := I) (K := K) C P
  /-- Manifold-side ambient open lift for the generated finite cover. -/
  ambientOpenData :
    generated.FiniteCoverAmbientOpenData (I := I) (K := K) (C := C) (P := P)
  /-- Target chart attached to each generated finite half-space box. -/
  targetChart :
    CoverIndexedBoundaryIndex (I := I) C →
      (Fin (n + 1) → Real) → M
  /-- Base transition-pullback support lies in the generated coordinate carrier. -/
  base_tsupport_subset_coordCarrier :
    ∀ i q,
      q ∈ (generated.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i →
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (generated.sourceChart (I := I) (K := K) i ⟨i, q⟩)
              (targetChart i q) ω) ⊆
          generated.coordCarrier (I := I) (K := K) i
  /-- Generated ambient regions lie in the boundary chart-transition domain. -/
  ambient_subset_boundaryChartDomain :
    ∀ i q,
      q ∈ (generated.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i →
        generated.ambient i ⊆
          boundaryChartDomain I
            (generated.sourceChart (I := I) (K := K) i ⟨i, q⟩)
            (targetChart i q)
  /-- Generated coordinate carriers map back into the compact support. -/
  coordCarrier_mapsTo_K :
    ∀ i q,
      q ∈ (generated.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i →
        ∀ y ∈ generated.coordCarrier (I := I) (K := K) i,
          (extChartAt I
            (generated.sourceChart (I := I) (K := K) i ⟨i, q⟩)).symm y ∈ K
  /-- Generated coordinate carriers lie in the source chart target. -/
  coordCarrier_subset_sourceTarget :
    ∀ i q,
      q ∈ (generated.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i →
        generated.coordCarrier (I := I) (K := K) i ⊆
          (extChartAt I
            (generated.sourceChart (I := I) (K := K) i ⟨i, q⟩)).target
  /-- Generated coordinate carriers lie in the source/target chart overlap. -/
  coordCarrier_subset_overlap :
    ∀ i q,
      q ∈ (generated.finiteHalfSpaceCover
        (I := I) (K := K) (C := C)).activePieces i →
        generated.coordCarrier (I := I) (K := K) i ⊆
          ManifoldForm.chartOverlap I
            (generated.sourceChart (I := I) (K := K) i ⟨i, q⟩)
            (targetChart i q)

namespace CoverIndexedZeroCompactRepresentedStokesNaturalCore

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesNaturalCore
        (I := I) (K := K) (ω := ω) (C := C) (P := P))

/-- The generated smooth box refinement. -/
def smoothRefinement
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M] :
    BoundarySmoothBoxRefinement
      (I := I) (K := K) C P
      (X.generated.BoundaryPiece (I := I) (K := K)) :=
  X.generated.smoothRefinementOfFiniteOpenCover
    (I := I) (K := K) X.ambientOpenData

/-- The generated box-refined boundary partition consumed by local Stokes. -/
def refinedPartition
    [FiniteDimensional Real (Fin (n + 1) → Real)]
    [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M] :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω
      (X.generated.BoundaryPiece (I := I) (K := K)) := by
  classical
  letI : DecidableEq (X.generated.BoundaryPiece (I := I) (K := K)) :=
    X.generated.instDecidableEqBoundaryPiece (I := I) (K := K)
  exact
    (X.smoothRefinement
      (I := I) (K := K) (ω := ω)).toRefinedPartitionOfFiniteHalfSpaceCoverOfAmbientDomain
        (I := I) (K := K) (ω := ω)
        (X.generated.finiteHalfSpaceCover (I := I) (K := K) (C := C))
        X.targetChart
        (by intro i; rfl)
        (by intro i q hq; rfl)
        (by intro i q hq; rfl)
        (by
          intro i q hq
          simpa [smoothRefinement] using
            X.base_tsupport_subset_coordCarrier i q hq)
        (X.generated.coordCarrier_subset_upperHalfSpace
          (I := I) (K := K))
        (X.generated.isCompact_coordCarrier (I := I) (K := K))
        (by
          intro i q hq
          simpa [smoothRefinement] using
            X.ambient_subset_boundaryChartDomain i q hq)
        (by
          intro i q hq
          simpa [smoothRefinement] using
            X.coordCarrier_mapsTo_K i q hq)
        (by
          intro i q hq
          simpa [smoothRefinement] using
            X.coordCarrier_subset_sourceTarget i q hq)
        (by
          intro i q hq
          simpa [smoothRefinement] using
            X.coordCarrier_subset_overlap i q hq)

end CoverIndexedZeroCompactRepresentedStokesNaturalCore

end NaturalCore

section NaturalImageData

universe uH uM uB uι

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {ImageIndex : Type uι} [Fintype ImageIndex]

/--
Small image-control input for a generated refined partition.

It exposes target boxes and a whole-box closed-preimage shrink condition,
rather than the older pair of fields `imageControlFamily` and
`imageControl_mapsTo`.
-/
structure CoverIndexedZeroCompactRepresentedStokesNaturalImageData
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)
    (ImageIndex : Type uι) [Fintype ImageIndex] where
  /-- Boundary chart owning each finite image-control index. -/
  owner : ImageIndex → CoverIndexedBoundaryIndex (I := I) C
  /-- Refined piece attached to each finite image-control index. -/
  piece : ImageIndex → BoundaryPiece
  /-- The selected piece belongs to its owner's refined finite family. -/
  piece_mem : ∀ r : ImageIndex, piece r ∈ D.boundaryPieces (owner r)
  /-- Refined source charts agree with the selected boundary charts. -/
  sourceChart_eq_boundaryChart :
    ∀ r : ImageIndex,
      D.sourceChart (owner r) (piece r) = C.boundaryChart (owner r).1
  /-- Lower corner of the target box for each refined box. -/
  targetLower : ImageIndex → Fin (n + 1) → Real
  /-- Upper corner of the target box for each refined box. -/
  targetUpper : ImageIndex → Fin (n + 1) → Real

namespace CoverIndexedZeroCompactRepresentedStokesNaturalImageData

variable
    {D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece}
    (Y :
      CoverIndexedZeroCompactRepresentedStokesNaturalImageData
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        D ImageIndex)

/-- The generated flattened image-control family. -/
def imageControlFamily :
    CoverIndexedRefinedBoxImageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      D ImageIndex where
  owner := Y.owner
  piece := Y.piece
  piece_mem := Y.piece_mem
  sourceChart_eq_boundaryChart := Y.sourceChart_eq_boundaryChart
  targetLower := Y.targetLower
  targetUpper := Y.targetUpper

/-- Whole-box closed-preimage image-control field for the generated family. -/
def ClosedPreimageShrinkField : Prop :=
  (Y.imageControlFamily
    (I := I) (K := K) (C := C) (P := P) (ω := ω)).ClosedPreimageShrinkField
    (I := I) (K := K) (C := C)

/-- Whole-box ambient `MapsTo` generated from the closed-preimage field. -/
theorem chartTransitionMapsToField_of_closedPreimageShrink
    (hpre : Y.ClosedPreimageShrinkField (I := I) (K := K) (C := C)) :
    (Y.imageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω)).ChartTransitionMapsToField
        (I := I) (K := K) (C := C) := by
  exact
    (Y.imageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω))
      |>.chartTransitionMapsToField_of_refined_closedPreimageShrink
        (I := I) (K := K) (C := C) hpre

end CoverIndexedZeroCompactRepresentedStokesNaturalImageData

end NaturalImageData

section NaturalInput

universe uH uM uι

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable {ImageIndex : Type uι} [Fintype ImageIndex]
variable [FiniteDimensional Real (Fin (n + 1) → Real)]
variable [IsManifold I ⊤ M] [T2Space M] [SigmaCompactSpace M]

/--
Natural compact-support represented Stokes input.

Compared with `CoverIndexedZeroCompactRepresentedStokesFromCollarInput`, this
input does not expose `smoothRefinement`, `refinedPartition`,
`smoothnessFields`, `imageControlFamily`, `imageControl_mapsTo`, or
`endpointAdapter`; each is generated by the constructors above.
-/
structure CoverIndexedZeroCompactRepresentedStokesNaturalInput where
  /-- Collar-generated core and chart-transition compatibility. -/
  core :
    CoverIndexedZeroCompactRepresentedStokesNaturalCore
      (I := I) (K := K) (ω := ω) (C := C) (P := P)
  /-- Chartwise smoothness of the base form. -/
  chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω
  /-- Smoothness neighborhood for each generated refined box. -/
  smoothnessNeighborhood :
    CoverIndexedBoundaryIndex (I := I) C →
      core.generated.BoundaryPiece (I := I) (K := K) →
        Set (Fin (n + 1) → Real)
  /-- Smoothness neighborhoods are open. -/
  smoothnessNeighborhood_isOpen :
    ∀ i,
      i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q,
          q ∈ (core.refinedPartition
            (I := I) (K := K) (ω := ω)).boundaryPieces i →
            IsOpen (smoothnessNeighborhood i q)
  /-- Each generated closed source box lies in its smoothness neighborhood. -/
  sourceIcc_subset_smoothnessNeighborhood :
    ∀ i,
      i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) →
        ∀ q,
          q ∈ (core.refinedPartition
            (I := I) (K := K) (ω := ω)).boundaryPieces i →
            Icc
                ((core.refinedPartition
                  (I := I) (K := K) (ω := ω)).lower i q)
                ((core.refinedPartition
                  (I := I) (K := K) (ω := ω)).upper i q) ⊆
              smoothnessNeighborhood i q
  /-- Smoothness neighborhoods lie in the source chart target. -/
  smoothnessNeighborhood_subset_target :
    ∀ i q,
      q ∈ (core.refinedPartition
        (I := I) (K := K) (ω := ω)).boundaryPieces i →
        smoothnessNeighborhood i q ⊆
          (extChartAt I
            ((core.refinedPartition
              (I := I) (K := K) (ω := ω)).sourceChart i q)).target
  /-- Smoothness neighborhoods lie in the source/target chart overlap. -/
  smoothnessNeighborhood_subset_overlap :
    ∀ i q,
      q ∈ (core.refinedPartition
        (I := I) (K := K) (ω := ω)).boundaryPieces i →
        smoothnessNeighborhood i q ⊆
          ManifoldForm.chartOverlap I
            ((core.refinedPartition
              (I := I) (K := K) (ω := ω)).sourceChart i q)
            ((core.refinedPartition
              (I := I) (K := K) (ω := ω)).targetChart i q)
  /-- Source-chart smoothness of the generated refined scalar coefficients. -/
  coefficientInChart_contDiffOn :
    ∀ i q,
      q ∈ (core.refinedPartition
        (I := I) (K := K) (ω := ω)).boundaryPieces i →
        ContDiffOn Real ⊤
          (ManifoldForm.coefficientInChart I
            ((core.refinedPartition
              (I := I) (K := K) (ω := ω)).sourceChart i q)
            ((core.refinedPartition
              (I := I) (K := K) (ω := ω)).coefficient i q))
          (smoothnessNeighborhood i q)
  /-- Target-box image-control data for the generated refined partition. -/
  imageData :
    CoverIndexedZeroCompactRepresentedStokesNaturalImageData
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (core.refinedPartition (I := I) (K := K) (ω := ω))
      ImageIndex
  /-- Whole-box closed-preimage shrink field for the generated image data. -/
  closedPreimageShrink :
    imageData.ClosedPreimageShrinkField (I := I) (K := K) (C := C)

namespace CoverIndexedZeroCompactRepresentedStokesNaturalInput

variable
    (X :
      CoverIndexedZeroCompactRepresentedStokesNaturalInput
        (I := I) (K := K) (ω := ω) (C := C) (P := P)
        (ImageIndex := ImageIndex))

/-- Generated smooth box refinement. -/
def smoothRefinement :
    BoundarySmoothBoxRefinement
      (I := I) (K := K) C P
      (X.core.generated.BoundaryPiece (I := I) (K := K)) :=
  X.core.smoothRefinement (I := I) (K := K) (ω := ω)

/-- Generated box-refined boundary partition. -/
def refinedPartition :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P ω
      (X.core.generated.BoundaryPiece (I := I) (K := K)) :=
  X.core.refinedPartition (I := I) (K := K) (ω := ω)

/-- Generated smoothness fields from source-chart coefficient smoothness. -/
def smoothnessFields :
    CoverIndexedBoundaryBoxRefinedSmoothnessFields
      (I := I) (K := K) (omega := ω) (C := C) (P := P)
      (X.refinedPartition (I := I) (K := K) (ω := ω))
      X.smoothnessNeighborhood :=
  CoverIndexedBoundaryBoxRefinedSmoothnessFields.ofGeneratedCoefficientInChart
    (I := I) (K := K) (omega := ω) (C := C) (P := P)
    (D := X.refinedPartition (I := I) (K := K) (ω := ω))
    (U := X.smoothnessNeighborhood)
    X.chartwiseSmooth
    X.smoothnessNeighborhood_subset_target
    X.smoothnessNeighborhood_subset_overlap
    X.coefficientInChart_contDiffOn

/-- Generated image-control family from finite target-box data. -/
def imageControlFamily :
    CoverIndexedRefinedBoxImageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      (X.refinedPartition (I := I) (K := K) (ω := ω))
      ImageIndex :=
  X.imageData.imageControlFamily (I := I) (K := K) (C := C) (P := P) (ω := ω)

/-- Generated whole-box ambient chart-transition control. -/
def imageControlMapsTo :
    (X.imageControlFamily
      (I := I) (K := K) (ω := ω)).ChartTransitionMapsToField
        (I := I) (K := K) (C := C) :=
  X.imageData.chartTransitionMapsToField_of_closedPreimageShrink
    (I := I) (K := K) (C := C) X.closedPreimageShrink

/-- The endpoint-facing generated input, with canonical endpoint adapter. -/
def toFromCollarEndpointInput :
    CoverIndexedZeroCompactFromCollarEndpointInput
      (I := I) (K := K) (ω := ω) (C := C) (P := P)
      (BoundaryPiece := X.core.generated.BoundaryPiece (I := I) (K := K))
      (ImageIndex := ImageIndex) := by
  classical
  letI : DecidableEq (X.core.generated.BoundaryPiece (I := I) (K := K)) :=
    X.core.generated.instDecidableEqBoundaryPiece (I := I) (K := K)
  exact
    { coordCarrier :=
        X.core.generated.coordCarrier (I := I) (K := K)
      ambient := X.core.generated.ambient
      coordCarrier_isCompact :=
        X.core.generated.isCompact_coordCarrier (I := I) (K := K)
      coordCarrier_subset_upperHalfSpace :=
        X.core.generated.coordCarrier_subset_upperHalfSpace (I := I) (K := K)
      collar_prisms := X.core.generated.collar_prisms
      smoothRefinement := X.smoothRefinement (I := I) (K := K) (ω := ω)
      refinedPartition := X.refinedPartition (I := I) (K := K) (ω := ω)
      smoothnessNeighborhood := X.smoothnessNeighborhood
      smoothnessFields := X.smoothnessFields (I := I) (K := K) (ω := ω)
      smoothnessNeighborhood_isOpen := X.smoothnessNeighborhood_isOpen
      sourceIcc_subset_smoothnessNeighborhood :=
        X.sourceIcc_subset_smoothnessNeighborhood
      imageControlFamily := X.imageControlFamily (I := I) (K := K) (ω := ω)
      imageControl_mapsTo := X.imageControlMapsTo (I := I) (K := K) (ω := ω) }

/-- Canonical represented bulk integral generated by the refined partition. -/
def representedBulkIntegral : Real :=
  (X.toFromCollarEndpointInput
    (I := I) (K := K) (ω := ω)).representedBulkIntegral
      (I := I) (K := K)

/-- Canonical represented boundary integral generated by the refined partition. -/
def representedBoundaryIntegral : Real :=
  (X.toFromCollarEndpointInput
    (I := I) (K := K) (ω := ω)).representedBoundaryIntegral
      (I := I) (K := K)

/--
Compact-support represented Stokes from natural collar-generated data.

The proof delegates to the existing from-collar theorem after constructing the
large certificate internally.
-/
theorem representedStokes :
    X.representedBulkIntegral (I := I) (K := K) (ω := ω) =
      X.representedBoundaryIntegral (I := I) (K := K) (ω := ω) := by
  exact
    (X.toFromCollarEndpointInput
      (I := I) (K := K) (ω := ω)).representedStokes
        (I := I) (K := K)

end CoverIndexedZeroCompactRepresentedStokesNaturalInput

end NaturalInput

end Stokes

end
