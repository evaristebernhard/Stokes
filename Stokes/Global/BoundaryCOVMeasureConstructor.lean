import Stokes.BoundaryChart.JacobianCOVBridge
import Stokes.Global.BoundaryCOVToChartChange
import Stokes.Global.BoundaryIntegralPartitionReconstruction

/-!
# Boundary COV measure reconstruction constructor

This file connects the boundary-chart COV family layer to the intermediate
`boundaryMeasureIntegral` field in `BoundaryIntegralPartitionReconstructionData`.

The analytic equality is still supplied piecewise by the boundary chart COV
packages, ultimately through the Jacobian COV bridge.  This module only performs
the finite-sum bookkeeping needed to turn those per-piece equalities into the
measure-reconstruction field.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasurePiecewise

universe c p

namespace BoundaryIntegralPartitionReconstructionData

variable {Chart : Type c} {Piece : Type p}
variable {activeCharts : Finset Chart}
variable {boundaryPieces : Chart → Finset Piece}
variable {boundaryMeasureTerm boundaryPartitionTerm : Chart → Piece → Real}
variable {manifoldBoundaryIntegral : Real}

/--
Build boundary partition reconstruction from an intermediate boundary-measure
piece family and a per-piece equality to the chosen boundary partition terms.
-/
def ofBoundaryMeasurePiecewiseEq
    (boundaryMeasureIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum activeCharts boundaryPieces boundaryMeasureTerm)
    (hpiece :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryMeasureTerm x q = boundaryPartitionTerm x q) :
    BoundaryIntegralPartitionReconstructionData activeCharts boundaryPieces
      boundaryPartitionTerm manifoldBoundaryIntegral :=
  ofBoundaryMeasureEq boundaryMeasureIntegral hmeasure <| by
    calc
      boundaryMeasureIntegral =
          selectedBoundaryPieceSum activeCharts boundaryPieces
            boundaryMeasureTerm := hboundaryMeasure
      _ =
          selectedBoundaryPieceSum activeCharts boundaryPieces
            boundaryPartitionTerm := by
            simpa [selectedBoundaryPieceSum] using
              boundaryChartChangeOfVariables_sum_eq_of_forall_eq activeCharts
                boundaryPieces boundaryMeasureTerm boundaryPartitionTerm hpiece

@[simp]
theorem ofBoundaryMeasurePiecewiseEq_boundaryMeasureIntegral
    (boundaryMeasureIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure :
      boundaryMeasureIntegral =
        selectedBoundaryPieceSum activeCharts boundaryPieces boundaryMeasureTerm)
    (hpiece :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ boundaryPieces x →
          boundaryMeasureTerm x q = boundaryPartitionTerm x q) :
    (ofBoundaryMeasurePiecewiseEq boundaryMeasureIntegral hmeasure
        hboundaryMeasure hpiece).boundaryMeasureIntegral =
      boundaryMeasureIntegral :=
  rfl

end BoundaryIntegralPartitionReconstructionData

end BoundaryMeasurePiecewise

section BoundaryCOVMeasureConstructor

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartChangeOfVariablesFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Per-piece boundary-measure equality supplied by a COV family, after identifying
the transported target boundary term with the selected boundary partition term.
-/
theorem pointwise_sourceBoundaryTerm_eq_partitionTerm [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = boundaryPartitionTerm x q) :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        F.sourceBoundaryTerm x q = boundaryPartitionTerm x q := by
  intro x hx q hq
  exact (F.pointwise_eq_targetBoundary x hx q hq).trans
    (htarget x hx q hq)

/--
Finite boundary-measure reconstruction from a COV family.  The measure side is
the source boundary-chart sum; COV transports each piece to the selected
boundary partition term.
-/
theorem sourceBoundarySum_eq_partitionSum [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = boundaryPartitionTerm x q) :
    F.sourceBoundarySum =
      selectedBoundaryPieceSum F.activeCharts F.localPieces boundaryPartitionTerm := by
  simpa [selectedBoundaryPieceSum] using
    F.sum_eq_of_targetBoundaryTerm_eq boundaryPartitionTerm htarget

/--
Signed Jacobian source term for one COV-family piece.

This is the boundary-measure representative exposed by
`BoundaryChart.JacobianCOVBridge`, with the outward-first boundary orientation
sign used by the project-local boundary terms.
-/
def jacobianSourceBoundaryTerm
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  outwardFirstBoundaryOrientationSign n *
    ∫ u in lowerZeroFaceDomain (F.sourceLowerCorner x q) (F.sourceUpperCorner x q),
      boundaryChartTransitionJacobianIntegrand I (F.sourceChart x q)
        (F.boundarySourceChart x q) ω u

/-- Finite sum of signed Jacobian source boundary terms. -/
def jacobianSourceBoundarySum
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) : Real :=
  Finset.sum F.activeCharts fun x =>
    Finset.sum (F.localPieces x) fun q => F.jacobianSourceBoundaryTerm x q

/--
Per-piece signed Jacobian COV equality, before rewriting the target in an
auxiliary boundary chart.
-/
theorem jacobianSourceBoundaryTerm_eq_targetInChartTerm [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        F.jacobianSourceBoundaryTerm x q = F.targetInChartTerm x q := by
  intro x hx q hq
  unfold jacobianSourceBoundaryTerm targetInChartTerm
    outwardFirstBoundaryInChartIntegral
  rw [(F.changeOfVariables x hx q hq).2.2]

/--
Per-piece signed Jacobian COV equality after rewriting the target using the
selected auxiliary boundary chart.
-/
theorem jacobianSourceBoundaryTerm_eq_targetBoundaryTerm [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        F.jacobianSourceBoundaryTerm x q = F.targetBoundaryTerm x q := by
  intro x hx q hq
  calc
    F.jacobianSourceBoundaryTerm x q = F.targetInChartTerm x q :=
      F.jacobianSourceBoundaryTerm_eq_targetInChartTerm x hx q hq
    _ = F.targetBoundaryTerm x q := by
      exact
        (outwardFirstBoundaryChartIntegral_eq_inChart_of_boundaryFace_subset_overlap
          (F.boundarySourceChart x q) (F.boundaryTargetChart x q) ω
          (F.targetLowerCorner x q) (F.targetUpperCorner x q)
          (F.targetSelectedBox x hx q hq).boundaryFace_subset_overlap).symm

/-- The COV source boundary term is the signed Jacobian source term piecewise. -/
theorem sourceBoundaryTerm_eq_jacobianSourceBoundaryTerm [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        F.sourceBoundaryTerm x q = F.jacobianSourceBoundaryTerm x q := by
  intro x hx q hq
  calc
    F.sourceBoundaryTerm x q = F.targetInChartTerm x q :=
      F.pointwise_eq_inChart x hx q hq
    _ = F.jacobianSourceBoundaryTerm x q :=
      (F.jacobianSourceBoundaryTerm_eq_targetInChartTerm x hx q hq).symm

/-- The signed Jacobian source sum agrees with the COV source boundary sum. -/
theorem jacobianSourceBoundarySum_eq_sourceBoundarySum [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece) :
    F.jacobianSourceBoundarySum = F.sourceBoundarySum := by
  exact
    boundaryChartChangeOfVariables_sum_eq_of_forall_eq F.activeCharts
      F.localPieces F.jacobianSourceBoundaryTerm F.sourceBoundaryTerm
      (fun x hx q hq =>
        (F.sourceBoundaryTerm_eq_jacobianSourceBoundaryTerm x hx q hq).symm)

/--
Finite boundary-measure reconstruction from the signed Jacobian source sum.
-/
theorem jacobianSourceBoundarySum_eq_partitionSum [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = boundaryPartitionTerm x q) :
    F.jacobianSourceBoundarySum =
      selectedBoundaryPieceSum F.activeCharts F.localPieces boundaryPartitionTerm :=
  F.jacobianSourceBoundarySum_eq_sourceBoundarySum.trans
    (F.sourceBoundarySum_eq_partitionSum boundaryPartitionTerm htarget)

/--
Minimal fieldized interface for the missing global boundary measure.

Until the repository has a canonical global boundary measure, this record
states only that its represented integral agrees with the COV source sum and
that each transported target term is the chosen partition term.
-/
structure BoundaryCOVMeasureReconstructionFields
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (manifoldBoundaryIntegral : Real) where
  /-- The genuine boundary measure integral represented by the COV source side. -/
  boundaryMeasureIntegral : Real
  /-- The represented manifold boundary integral agrees with the measure integral. -/
  manifoldBoundaryIntegral_eq_boundaryMeasureIntegral :
    manifoldBoundaryIntegral = boundaryMeasureIntegral
  /-- The boundary measure integral is the finite COV source-boundary sum. -/
  boundaryMeasureIntegral_eq_sourceBoundarySum :
    boundaryMeasureIntegral = F.sourceBoundarySum
  /-- The transported COV target terms are the selected boundary partition terms. -/
  targetBoundaryTerm_eq_partitionTerm :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        F.targetBoundaryTerm x q = boundaryPartitionTerm x q

namespace BoundaryCOVMeasureReconstructionFields

variable {F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece}
variable {boundaryPartitionTerm : Chart → Piece → Real}
variable {manifoldBoundaryIntegral : Real}

/-- The fieldized COV-measure interface supplies the per-piece source equality. -/
theorem pointwise_sourceBoundaryTerm_eq_partitionTerm [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        manifoldBoundaryIntegral) :
    ∀ x, x ∈ F.activeCharts →
      ∀ q, q ∈ F.localPieces x →
        F.sourceBoundaryTerm x q = boundaryPartitionTerm x q :=
  F.pointwise_sourceBoundaryTerm_eq_partitionTerm boundaryPartitionTerm
    D.targetBoundaryTerm_eq_partitionTerm

/-- The fieldized COV-measure interface reconstructs the boundary measure sum. -/
theorem boundaryMeasureIntegral_eq_partitionSum [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        manifoldBoundaryIntegral) :
    D.boundaryMeasureIntegral =
      selectedBoundaryPieceSum F.activeCharts F.localPieces boundaryPartitionTerm :=
  D.boundaryMeasureIntegral_eq_sourceBoundarySum.trans
    (F.sourceBoundarySum_eq_partitionSum boundaryPartitionTerm
      D.targetBoundaryTerm_eq_partitionTerm)

/-- Convert the fieldized COV-measure interface to partition reconstruction. -/
def toBoundaryIntegralPartitionReconstructionData [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        manifoldBoundaryIntegral) :
    BoundaryIntegralPartitionReconstructionData F.activeCharts F.localPieces
      boundaryPartitionTerm manifoldBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofBoundaryMeasureEq
    D.boundaryMeasureIntegral
    D.manifoldBoundaryIntegral_eq_boundaryMeasureIntegral
    D.boundaryMeasureIntegral_eq_partitionSum

@[simp]
theorem toBoundaryIntegralPartitionReconstructionData_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        manifoldBoundaryIntegral) :
    D.toBoundaryIntegralPartitionReconstructionData.boundaryMeasureIntegral =
      D.boundaryMeasureIntegral :=
  rfl

/--
Projection from the fieldized COV-measure interface to the final boundary
partition finite sum, in the shape consumed by global assembly layers.
-/
theorem toBoundaryIntegralPartitionReconstructionData_globalBoundaryIntegral_eq_boundaryPartitionSum
    [IsManifold I 1 M]
    (D :
      BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
        manifoldBoundaryIntegral) :
    manifoldBoundaryIntegral =
      Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q => boundaryPartitionTerm x q :=
  D.toBoundaryIntegralPartitionReconstructionData
    |>.globalBoundaryIntegral_eq_boundaryPartitionSum

end BoundaryCOVMeasureReconstructionFields

/--
Build the minimal fieldized COV-measure interface directly from a measure/source
sum equality.
-/
def boundaryCOVMeasureReconstructionFields
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (manifoldBoundaryIntegral boundaryMeasureIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure : boundaryMeasureIntegral = F.sourceBoundarySum)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = boundaryPartitionTerm x q) :
    BoundaryCOVMeasureReconstructionFields F boundaryPartitionTerm
      manifoldBoundaryIntegral where
  boundaryMeasureIntegral := boundaryMeasureIntegral
  manifoldBoundaryIntegral_eq_boundaryMeasureIntegral := hmeasure
  boundaryMeasureIntegral_eq_sourceBoundarySum := hboundaryMeasure
  targetBoundaryTerm_eq_partitionTerm := htarget

/--
Fill `BoundaryIntegralPartitionReconstructionData` from a boundary-chart COV
family and an identification of the genuine boundary measure integral with the
source boundary-chart sum.
-/
def boundaryIntegralPartitionReconstructionData [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (manifoldBoundaryIntegral boundaryMeasureIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure : boundaryMeasureIntegral = F.sourceBoundarySum)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = boundaryPartitionTerm x q) :
    BoundaryIntegralPartitionReconstructionData F.activeCharts F.localPieces
      boundaryPartitionTerm manifoldBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofBoundaryMeasureEq
    boundaryMeasureIntegral hmeasure <|
      hboundaryMeasure.trans
        (F.sourceBoundarySum_eq_partitionSum boundaryPartitionTerm htarget)

@[simp]
theorem boundaryIntegralPartitionReconstructionData_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (manifoldBoundaryIntegral boundaryMeasureIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure : boundaryMeasureIntegral = F.sourceBoundarySum)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = boundaryPartitionTerm x q) :
    (F.boundaryIntegralPartitionReconstructionData boundaryPartitionTerm
        manifoldBoundaryIntegral boundaryMeasureIntegral hmeasure hboundaryMeasure
        htarget).boundaryMeasureIntegral =
      boundaryMeasureIntegral :=
  rfl

/--
Projection from the COV-measure constructor to the final boundary partition
finite sum, avoiding constructor unfolding at M8/assembly call sites.
-/
theorem boundaryIntegralPartitionReconstructionData_globalBoundaryIntegral_eq_boundaryPartitionSum
    [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (manifoldBoundaryIntegral boundaryMeasureIntegral : Real)
    (hmeasure : manifoldBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure : boundaryMeasureIntegral = F.sourceBoundarySum)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = boundaryPartitionTerm x q) :
    manifoldBoundaryIntegral =
      Finset.sum F.activeCharts fun x =>
        Finset.sum (F.localPieces x) fun q => boundaryPartitionTerm x q :=
  (F.boundaryIntegralPartitionReconstructionData boundaryPartitionTerm
    manifoldBoundaryIntegral boundaryMeasureIntegral hmeasure hboundaryMeasure
    htarget).globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Tautological version in which the represented manifold boundary integral is the
COV source boundary-chart sum itself.
-/
def boundaryIntegralPartitionReconstructionData_sourceBoundarySum
    [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = boundaryPartitionTerm x q) :
    BoundaryIntegralPartitionReconstructionData F.activeCharts F.localPieces
      boundaryPartitionTerm F.sourceBoundarySum :=
  F.boundaryIntegralPartitionReconstructionData boundaryPartitionTerm
    F.sourceBoundarySum F.sourceBoundarySum rfl rfl htarget

/--
The COV family reconstructs a project-local boundary partition after the
compatibility adapter from `BoundaryCOVToChartChange` has aligned the target
terms with the project-local package.
-/
theorem boundaryMeasureIntegral_eq_projectLocalPartitionSum [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    {D : ProjectLocalGlobalStokesData I ω Chart Piece}
    (C : ProjectLocalChartChangeCompatibility F D)
    (boundaryMeasureIntegral : Real)
    (hboundaryMeasure : boundaryMeasureIntegral = F.sourceBoundarySum) :
    boundaryMeasureIntegral =
      selectedBoundaryPieceSum D.activeCharts D.localPieces
        D.boundaryPartitionTerm := by
  refine hboundaryMeasure.trans ?_
  have htarget :
      ∀ x, x ∈ F.activeCharts →
        ∀ q, q ∈ F.localPieces x →
          F.targetBoundaryTerm x q = D.boundaryPartitionTerm x q := by
    intro x hx q hq
    exact (C.boundaryPartitionTerm_eq x hx q hq).symm
  have hF :
      F.sourceBoundarySum =
        selectedBoundaryPieceSum F.activeCharts F.localPieces
          D.boundaryPartitionTerm :=
    F.sourceBoundarySum_eq_partitionSum D.boundaryPartitionTerm htarget
  simpa [selectedBoundaryPieceSum, C.activeCharts_eq, C.localPieces_eq] using hF

/--
Project-local wrapper that fills the `boundaryMeasureIntegral` field from a
COV-family source measure sum and the compatibility adapter.
-/
def boundaryIntegralPartitionReconstructionData_projectLocal [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    {D : ProjectLocalGlobalStokesData I ω Chart Piece}
    (C : ProjectLocalChartChangeCompatibility F D)
    (boundaryMeasureIntegral : Real)
    (hmeasure : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure : boundaryMeasureIntegral = F.sourceBoundarySum) :
    BoundaryIntegralPartitionReconstructionData D.activeCharts D.localPieces
      D.boundaryPartitionTerm D.globalBoundaryIntegral :=
  BoundaryIntegralPartitionReconstructionData.ofBoundaryMeasureEq
    boundaryMeasureIntegral hmeasure
      (F.boundaryMeasureIntegral_eq_projectLocalPartitionSum C
        boundaryMeasureIntegral hboundaryMeasure)

@[simp]
theorem boundaryIntegralPartitionReconstructionData_projectLocal_boundaryMeasureIntegral
    [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    {D : ProjectLocalGlobalStokesData I ω Chart Piece}
    (C : ProjectLocalChartChangeCompatibility F D)
    (boundaryMeasureIntegral : Real)
    (hmeasure : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure : boundaryMeasureIntegral = F.sourceBoundarySum) :
    (F.boundaryIntegralPartitionReconstructionData_projectLocal C
        boundaryMeasureIntegral hmeasure hboundaryMeasure).boundaryMeasureIntegral =
      boundaryMeasureIntegral :=
  rfl

/--
Project-local projection from the COV-measure constructor to the exact finite
boundary-partition equality required by the assembly/global records.
-/
theorem boundaryCOV_projectLocal_globalBoundaryIntegral_eq_boundaryPartitionSum
    [IsManifold I 1 M]
    (F : BoundaryChartChangeOfVariablesFamily I ω Chart Piece)
    {D : ProjectLocalGlobalStokesData I ω Chart Piece}
    (C : ProjectLocalChartChangeCompatibility F D)
    (boundaryMeasureIntegral : Real)
    (hmeasure : D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hboundaryMeasure : boundaryMeasureIntegral = F.sourceBoundarySum) :
    D.globalBoundaryIntegral =
      Finset.sum D.activeCharts fun x =>
        Finset.sum (D.localPieces x) fun q => D.boundaryPartitionTerm x q :=
  (F.boundaryIntegralPartitionReconstructionData_projectLocal C
    boundaryMeasureIntegral hmeasure hboundaryMeasure)
    |>.projectLocal_globalBoundaryIntegral_eq_boundaryPartitionSum

end BoundaryChartChangeOfVariablesFamily

end BoundaryCOVMeasureConstructor

end Stokes

end
