import Stokes.Global.BoundaryAtlasMembershipAuto
import Stokes.Global.NaturalCompactSupportCombinedEndpoint

/-!
# Boundary chart-change data from target-image COV inputs

This module removes one layer of manual boundary chart-change input at the
global endpoints.  A resolved target-image family already contains the selected
source boxes, the local inverse/target-image selections, and the selected
target boxes.  Together with oriented-atlas data and project-local field
compatibility, it constructs the selected chart-change family consumed by the
canonical boundary route.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryChartChangeFromCOVAuto

universe u w c p b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p} {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}

namespace BoundaryChartTargetImageResolvedFamily

variable {F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece}
variable {D : ProjectLocalGlobalStokesData I omega Chart Piece}

/-- One selected chart-change piece built directly from resolved target-image data
and an oriented boundary atlas. -/
def selectedPieceDataOfOrientedAtlas [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (atlasMembership : F.BoundaryAtlasMembership A)
    (C : ProjectLocalCompatibility F D)
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.localPieces x) :
    BoundaryChartChangeSelectedPieceData I omega (D.sourceChart x q)
      (D.targetChart x q) (D.lowerCorner x q) (D.upperCorner x q) where
  boundaryTargetChart := F.boundaryTargetChart x q
  targetLowerCorner := F.targetLowerCorner x q
  targetUpperCorner := F.targetUpperCorner x q
  changeOfVariables := by
    simpa [C.sourceChart_eq x q, C.targetChart_eq x q,
      C.lowerCorner_eq x q, C.upperCorner_eq x q] using
      F.orientedChangeOfVariablesOfOrientedAtlas A x (C.mem_active hx) q
        (C.mem_localPiece hq)
        (atlasMembership.sourceChart_mem x (C.mem_active hx) q
          (C.mem_localPiece hq))
        (atlasMembership.boundarySourceChart_mem x (C.mem_active hx) q
          (C.mem_localPiece hq))
  targetBox := by
    simpa [C.targetChart_eq x q] using
      F.selectedTargetBox x (C.mem_active hx) q (C.mem_localPiece hq)

/-- Selected chart-change family built directly from resolved target-image data
and an oriented boundary atlas. -/
def toBoundaryChartChangeSelectedFamilyDataOfOrientedAtlas [IsManifold I 1 M]
    (A : BoundaryChartOrientedAtlas I M)
    (atlasMembership : F.BoundaryAtlasMembership A)
    (C : ProjectLocalCompatibility F D) :
    BoundaryChartChangeSelectedFamilyData D where
  pieceData := fun x hx q hq =>
    F.selectedPieceDataOfOrientedAtlas A atlasMembership C x hx q hq
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [selectedPieceDataOfOrientedAtlas, C.targetChart_eq x q] using
      C.boundaryPartitionTerm_eq x (C.mem_active hx) q (C.mem_localPiece hq)

/-- One selected chart-change piece built directly from resolved target-image data
and global oriented-boundary-manifold data. -/
def selectedPieceDataOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (C : ProjectLocalCompatibility F D)
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.localPieces x) :
    BoundaryChartChangeSelectedPieceData I omega (D.sourceChart x q)
      (D.targetChart x q) (D.lowerCorner x q) (D.upperCorner x q) where
  boundaryTargetChart := F.boundaryTargetChart x q
  targetLowerCorner := F.targetLowerCorner x q
  targetUpperCorner := F.targetUpperCorner x q
  changeOfVariables := by
    simpa [C.sourceChart_eq x q, C.targetChart_eq x q,
      C.lowerCorner_eq x q, C.upperCorner_eq x q] using
      F.orientedChangeOfVariablesOfOrientedManifold x (C.mem_active hx) q
        (C.mem_localPiece hq)
  targetBox := by
    simpa [C.targetChart_eq x q] using
      F.selectedTargetBox x (C.mem_active hx) q (C.mem_localPiece hq)

/-- Selected chart-change family built directly from resolved target-image data
and global oriented-boundary-manifold data. -/
def toBoundaryChartChangeSelectedFamilyDataOfOrientedManifold
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (C : ProjectLocalCompatibility F D) :
    BoundaryChartChangeSelectedFamilyData D where
  pieceData := fun x hx q hq =>
    F.selectedPieceDataOfOrientedManifold C x hx q hq
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [selectedPieceDataOfOrientedManifold, C.targetChart_eq x q] using
      C.boundaryPartitionTerm_eq x (C.mem_active hx) q (C.mem_localPiece hq)

end BoundaryChartTargetImageResolvedFamily

section Route

variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}
variable
    {T :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece}
variable {P : ProjectLocalGlobalStokesData I omega M BoundaryPiece}

namespace ProjectLocalBoundaryGlobalMeasureFacts

variable (G : ProjectLocalBoundaryGlobalMeasureFacts P)

/-- Canonical route input from resolved target-image COV data and the endpoint's
oriented boundary atlas, without a hand-supplied selected chart-change family. -/
def toBoundaryCanonicalRouteMeasureInputOfOrientedAtlasTargetImageResolved
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toBoundaryCanonicalRouteMeasureInputOfSelected faceContinuity sourceAlignment
    (F.toBoundaryChartChangeSelectedFamilyDataOfOrientedAtlas
      orientedBoundaryAtlas
      (BoundaryChartTargetImageResolvedFamily.boundaryAtlasMembershipOfProjectLocalAlignment
        (T := T) (P := P) (F := F) sourceAlignment C)
      C)

/-- Canonical route input from resolved target-image COV data and
oriented-manifold data, without a hand-supplied selected chart-change family. -/
def toBoundaryCanonicalRouteMeasureInputOfOrientedManifoldTargetImageResolved
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toBoundaryCanonicalRouteMeasureInputOfSelected faceContinuity sourceAlignment
    (F.toBoundaryChartChangeSelectedFamilyDataOfOrientedManifold C)

end ProjectLocalBoundaryGlobalMeasureFacts

namespace ProjectLocalBoundarySupportFiniteMeasureFacts

variable (G : ProjectLocalBoundarySupportFiniteMeasureFacts P)

/-- Support-finite route input from resolved target-image COV data and the
endpoint's oriented boundary atlas. -/
def toBoundaryCanonicalRouteMeasureInputOfOrientedAtlasTargetImageResolved
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toGlobalMeasureFacts
    |>.toBoundaryCanonicalRouteMeasureInputOfOrientedAtlasTargetImageResolved
      faceContinuity sourceAlignment F C

/-- Support-finite route input from resolved target-image COV data and
oriented-manifold data. -/
def toBoundaryCanonicalRouteMeasureInputOfOrientedManifoldTargetImageResolved
    [IsManifold I 1 M] [BoundaryChartOrientedManifold I M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toGlobalMeasureFacts
    |>.toBoundaryCanonicalRouteMeasureInputOfOrientedManifoldTargetImageResolved
      faceContinuity sourceAlignment F C

end ProjectLocalBoundarySupportFiniteMeasureFacts

end Route

section Endpoint

variable {ρ : SmoothPartitionOfUnity M I M univ}
variable {μ : Measure (Fin (n + 1) → Real)}
variable [IsFiniteMeasureOnCompacts μ]
variable [IsManifold I 1 M]

namespace NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

variable
    (B :
      NaturalCompactSupportBulkProjectLocalAutoCollapsedInput
        ExtInteriorPiece ExtBoundaryPiece
        I omega BoundaryPiece ρ μ)

/--
Combined endpoint base input from resolved boundary target-image COV data.

This constructor removes the endpoint path that asked callers to supply a
selected chart-change family by hand.  The selected family is reconstructed
from the resolved target-image/local-inverse family and `B.orientedBoundaryAtlas`.
-/
def toBulkBoundarySeparatedBaseInputOfOrientedAtlasTargetImageResolved
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceProjectLocalAlignment B.targetImageInput boundaryProjectLocal)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal
    (globalMeasure.toBoundaryCanonicalRouteMeasureInputOfOrientedAtlasTargetImageResolved
      faceContinuity sourceAlignment F C)

@[simp]
theorem toBulkBoundarySeparatedBaseInputOfOrientedAtlasTargetImageResolved_boundaryRoute
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (globalMeasure :
      ProjectLocalBoundaryGlobalMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceProjectLocalAlignment B.targetImageInput boundaryProjectLocal)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility boundaryProjectLocal) :
    (B.toBulkBoundarySeparatedBaseInputOfOrientedAtlasTargetImageResolved
      boundaryProjectLocal globalMeasure faceContinuity sourceAlignment F
      C).boundaryRoute =
      globalMeasure.toBoundaryCanonicalRouteMeasureInputOfOrientedAtlasTargetImageResolved
        faceContinuity sourceAlignment F C := by
  rfl

/-- Support-finite global-measure variant of the resolved target-image endpoint
constructor. -/
def toBulkBoundarySeparatedBaseInputOfSupportFiniteOrientedAtlasTargetImageResolved
    (boundaryProjectLocal :
      ProjectLocalGlobalStokesData I omega M BoundaryPiece)
    (supportFinite :
      ProjectLocalBoundarySupportFiniteMeasureFacts boundaryProjectLocal)
    (faceContinuity :
      ProjectLocalBoundaryCanonicalFaceContinuityData boundaryProjectLocal)
    (sourceAlignment :
      BoundarySourceProjectLocalAlignment B.targetImageInput boundaryProjectLocal)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility boundaryProjectLocal) :
    NaturalCompactSupportBulkBoundarySeparatedBaseInput
      ExtInteriorPiece ExtBoundaryPiece I omega BoundaryPiece ρ μ :=
  B.toBulkBoundarySeparatedBaseInput boundaryProjectLocal
    (supportFinite.toBoundaryCanonicalRouteMeasureInputOfOrientedAtlasTargetImageResolved
      faceContinuity sourceAlignment F C)

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

end Endpoint

end BoundaryChartChangeFromCOVAuto

end Stokes

end
