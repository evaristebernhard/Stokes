import Stokes.Global.BoundaryChartChangeFromCOVAuto
import Stokes.BoundaryChart.OrientationMembershipAuto

/-!
# Global boundary orientation membership to COV

This module is the global-facing adapter for
`BoundaryChartOrientationMembership`.  It keeps the lower boundary-chart COV
facades acyclic: global endpoint data projects its `source_mem` /
`boundarySource_mem` fields into a bundled two-chart membership record, and
then calls the selected-box COV constructors through that package.

The file is deliberately proof-thin.  It does not add new analytic content;
it only removes duplicated membership plumbing from the boundary chart-change
and boundary-partition routes.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryOrientationMembershipToCOVAuto

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
variable {A : BoundaryChartOrientedAtlas I M}

namespace BoundaryAtlasMembership

/-- Project the two resolved-family atlas membership fields into one local
orientation-membership package. -/
def orientationMembership
    (D : F.BoundaryAtlasMembership A)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    BoundaryChartOrientationMembership A.charts
      (F.sourceChart x q) (F.boundarySourceChart x q) :=
  BoundaryChartOrientationMembership.of_mem
    (D.sourceChart_mem x hx q hq) (D.boundarySourceChart_mem x hx q hq)

@[simp]
theorem orientationMembership_source_mem
    (D : F.BoundaryAtlasMembership A)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    (D.orientationMembership x hx q hq).source_mem =
      D.sourceChart_mem x hx q hq := by
  rfl

@[simp]
theorem orientationMembership_boundarySource_mem
    (D : F.BoundaryAtlasMembership A)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    (D.orientationMembership x hx q hq).boundarySource_mem =
      D.boundarySourceChart_mem x hx q hq := by
  rfl

end BoundaryAtlasMembership

/-- Pointwise selected COV for a resolved target-image family, using bundled
orientation membership instead of two independent atlas-membership proofs. -/
theorem orientedChangeOfVariablesOfOrientationMembership [IsManifold I 1 M]
    (F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (atlasMembership : F.BoundaryAtlasMembership A)
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    boundaryChartOrientedChangeOfVariables I
      (F.sourceChart x q) (F.boundarySourceChart x q) omega
      (F.sourceLowerCorner x q) (F.sourceUpperCorner x q)
      (F.targetLowerCorner x q) (F.targetUpperCorner x q) :=
  F.orientedChangeOfVariablesOfOrientedAtlas A x hx q hq
    (atlasMembership.orientationMembership x hx q hq).source_mem
    (atlasMembership.orientationMembership x hx q hq).boundarySource_mem

variable {D : ProjectLocalGlobalStokesData I omega Chart Piece}

/-- One selected chart-change piece, with its COV proof obtained from projected
orientation membership. -/
def selectedPieceDataOfOrientationMembership [IsManifold I 1 M]
    (F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (atlasMembership : F.BoundaryAtlasMembership A)
    (C : F.ProjectLocalCompatibility D)
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
      F.orientedChangeOfVariablesOfOrientationMembership A atlasMembership x
        (C.mem_active hx) q (C.mem_localPiece hq)
  targetBox := by
    simpa [C.targetChart_eq x q] using
      F.selectedTargetBox x (C.mem_active hx) q (C.mem_localPiece hq)

/-- Selected chart-change family, with membership projected once from the global
resolved-family route. -/
def toBoundaryChartChangeSelectedFamilyDataOfOrientationMembership
    [IsManifold I 1 M]
    (F : BoundaryChartTargetImageResolvedFamily I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (atlasMembership : F.BoundaryAtlasMembership A)
    (C : F.ProjectLocalCompatibility D) :
    BoundaryChartChangeSelectedFamilyData D where
  pieceData := fun x hx q hq =>
    F.selectedPieceDataOfOrientationMembership A atlasMembership C x hx q hq
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [selectedPieceDataOfOrientationMembership, C.targetChart_eq x q] using
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

/-- Canonical boundary route from resolved target-image COV data, with the
endpoint membership fields first projected into
`BoundaryChartOrientationMembership`. -/
def toBoundaryCanonicalRouteMeasureInputOfOrientationMembershipTargetImageResolved
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toBoundaryCanonicalRouteMeasureInputOfSelected faceContinuity sourceAlignment
    (F.toBoundaryChartChangeSelectedFamilyDataOfOrientationMembership
      orientedBoundaryAtlas
      (BoundaryChartTargetImageResolvedFamily.boundaryAtlasMembershipOfProjectLocalAlignment
        (T := T) (P := P) (F := F) sourceAlignment C)
      C)

end ProjectLocalBoundaryGlobalMeasureFacts

namespace ProjectLocalBoundarySupportFiniteMeasureFacts

variable (G : ProjectLocalBoundarySupportFiniteMeasureFacts P)

/-- Support-finite variant of the resolved target-image route through bundled
orientation membership. -/
def toBoundaryCanonicalRouteMeasureInputOfOrientationMembershipTargetImageResolved
    [IsManifold I 1 M]
    (faceContinuity : ProjectLocalBoundaryCanonicalFaceContinuityData P)
    (sourceAlignment : BoundarySourceProjectLocalAlignment T P)
    (F : BoundaryChartTargetImageResolvedFamily I omega M BoundaryPiece)
    (C : F.ProjectLocalCompatibility P) :
    BoundaryCanonicalRouteMeasureInput T P :=
  G.toGlobalMeasureFacts
    |>.toBoundaryCanonicalRouteMeasureInputOfOrientationMembershipTargetImageResolved
      faceContinuity sourceAlignment F C

end ProjectLocalBoundarySupportFiniteMeasureFacts

end Route

namespace BoundaryOrientationSelectedAssemblyInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Project the boundary-partition chart-pair membership into the bundled local
membership record consumed by the selected COV route. -/
def boundaryPartitionOrientationMembership
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundaryTargetChart x q ∈ A.charts)
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.boundaryPieces x) :
    BoundaryChartOrientationMembership A.charts
      (D.boundarySourceChart x q) (D.boundaryTargetChart x q) :=
  BoundaryChartOrientationMembership.of_mem
    (hboundarySource x hx q hq) (hboundaryTarget x hx q hq)

/-- Pointwise COV constructor for the boundary partition term, phrased using a
bundled orientation-membership selector. -/
theorem boundaryPartitionSelectedCOVOfOrientationMembership [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (membership :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          BoundaryChartOrientationMembership A.charts
            (D.boundarySourceChart x q) (D.boundaryTargetChart x q))
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.boundaryPieces x) :
    boundaryChartOrientedChangeOfVariables I
      (D.boundarySourceChart x q) (D.boundaryTargetChart x q) omega
      (D.targetLowerCorner x q) (D.targetUpperCorner x q)
      (D.partitionLowerCorner x q) (D.partitionUpperCorner x q) := by
  simpa [toBoundaryChartSelectedBoxCOVFamilyData, partitionLowerCorner,
    partitionUpperCorner] using
    (D.toBoundaryChartSelectedBoxCOVFamilyData
      |>.orientedChangeOfVariablesOfOrientedAtlas A x hx q hq
        (membership x hx q hq).source_mem
        (membership x hx q hq).boundarySource_mem)

/-- Selected boundary assembly data from a boundary-partition membership
selector.  This is the endpoint-facing constructor: the only orientation input
needed by the partition chart-change field is the bundled chart-pair
membership. -/
def toSelectedBoundaryAssemblyData_of_orientationMembership
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (membership :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          BoundaryChartOrientationMembership A.charts
            (D.boundarySourceChart x q) (D.boundaryTargetChart x q)) :
    SelectedBoundaryAssemblyData I omega Chart Piece where
  activeCharts := D.activeCharts
  boundaryPieces := D.boundaryPieces
  sourceChart := D.sourceChart
  boundarySourceChart := D.boundarySourceChart
  boundaryTargetChart := D.boundaryTargetChart
  sourceLowerCorner := D.sourceLowerCorner
  sourceUpperCorner := D.sourceUpperCorner
  targetLowerCorner := D.targetLowerCorner
  targetUpperCorner := D.targetUpperCorner
  sourceExtendedBox := D.sourceExtendedBox
  targetSelectedBox := D.targetSelectedBox
  imageData := D.imageData
  partitionTargetChart := D.partitionTargetChart
  partitionLowerCorner := D.partitionLowerCorner
  partitionUpperCorner := D.partitionUpperCorner
  chartChangeOfVariables := by
    intro x hx q hq
    exact D.boundaryPartitionSelectedCOVOfOrientationMembership A membership
      x hx q hq
  partitionSelectedBox := by
    intro x hx q hq
    simpa [partitionLowerCorner, partitionUpperCorner] using
      D.partitionSelectedBox x hx q hq
  boundaryPartitionTerm := D.boundaryPartitionTerm
  boundaryPartitionTerm_eq := by
    intro x hx q hq
    simpa [partitionLowerCorner, partitionUpperCorner] using
      D.boundaryPartitionTerm_eq x hx q hq

/-- Convenience wrapper recovering the membership selector from the two
traditional oriented-atlas membership fields. -/
def toSelectedBoundaryAssemblyData_of_orientedAtlasMembership
    [IsManifold I 1 M]
    (D : BoundaryOrientationSelectedAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (hboundarySource :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundarySourceChart x q ∈ A.charts)
    (hboundaryTarget :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x → D.boundaryTargetChart x q ∈ A.charts) :
    SelectedBoundaryAssemblyData I omega Chart Piece :=
  D.toSelectedBoundaryAssemblyData_of_orientationMembership A
    (fun x hx q hq =>
      D.boundaryPartitionOrientationMembership A hboundarySource hboundaryTarget
        x hx q hq)

end BoundaryOrientationSelectedAssemblyInput

namespace BoundaryTargetImageToAssemblyInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Boundary-target assembly wrapper for endpoint code that already works with
the reduced target-image assembly package. -/
def toSelectedBoundaryAssemblyData_of_orientationMembership
    [IsManifold I 1 M]
    (D : BoundaryTargetImageToAssemblyInput I omega Chart Piece)
    (A : BoundaryChartOrientedAtlas I M)
    (membership :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          BoundaryChartOrientationMembership A.charts
            (D.boundarySourceChart x q) (D.boundaryTargetChart x q)) :
    SelectedBoundaryAssemblyData I omega Chart Piece :=
  D.toBoundaryOrientationSelectedAssemblyInput
    |>.toSelectedBoundaryAssemblyData_of_orientationMembership A
      (by
        intro x hx q hq
        simpa [toBoundaryOrientationSelectedAssemblyInput] using
          membership x hx q hq)

end BoundaryTargetImageToAssemblyInput

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

/-- Endpoint base input from resolved target-image data using the membership
projection route. -/
def toBulkBoundarySeparatedBaseInputOfOrientationMembershipTargetImageResolved
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
    (globalMeasure.toBoundaryCanonicalRouteMeasureInputOfOrientationMembershipTargetImageResolved
      faceContinuity sourceAlignment F C)

end NaturalCompactSupportBulkProjectLocalAutoCollapsedInput

end Endpoint

end BoundaryOrientationMembershipToCOVAuto

end Stokes

end
