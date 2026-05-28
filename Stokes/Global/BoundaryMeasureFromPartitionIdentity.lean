import Stokes.Global.BoundaryCompactMeasureFromPartition
import Stokes.Global.BoundaryPartitionTermAlignment
import Stokes.Global.NaturalCompactSupportMeasureConstructor

/-!
# Boundary measure reconstruction from a boundary partition identity

This file is the L7 handoff from a genuine boundary finite-partition identity
to the compact-support measure package.

The measure proof often first identifies each active boundary piece with the
geometric term carried by `BoundaryPieceFamilyInput.boundaryBoundaryTerm`.
The selected compact-support statement, however, uses the partition term stored
in the boundary assembly.  The chart-change/orientation work proves these terms
are pointwise equal on active pieces, so the constructors below transport the
measure reconstruction across that equality.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryMeasureFromPartitionIdentity

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {alpha : Type a} [MeasurableSpace alpha]
variable {mu : Measure alpha}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace M8TargetImageInput

variable
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)

/--
Boundary compact measure fields from a reconstruction proved for the geometric
boundary term `BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages`.

The only transport is the already-proved boundary chart-change identity
identifying that geometric term with `D.assembly.boundaryPartitionTerm`.
-/
def boundaryCompactMeasureFieldsOfIntegrableOnBoundaryBoundaryTerm
    [IsManifold I 1 M]
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceIntegrableOn :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          IntegrableOn (boundaryPieceIntegrand x q)
            (boundaryPieceSet x q) mu)
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields mu selectedPartition.active
      D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofSetIntegralBoundaryTermEq
    (mu := mu) (activeCharts := selectedPartition.active)
    (boundaryPieces := D.targetImages.boundaryPieces)
    (oldTerm := BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages)
    (newTerm := D.assembly.boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral boundaryMeasureIntegral_eq_integral
    boundaryPieceSet_measurable boundaryPieceIntegrableOn
    boundaryBoundaryTerm_eq_setIntegral
    (fun x hx q hq =>
      D.boundaryBoundaryTerm_eq_assemblyBoundaryPartitionTerm x hx q hq)
    boundaryIntegrand_ae_eq_indicatorSum

section CompactSupport

variable [TopologicalSpace alpha] [OpensMeasurableSpace alpha] [T2Space alpha]
variable [IsFiniteMeasureOnCompacts mu]

/--
Compact-support version of
`boundaryCompactMeasureFieldsOfIntegrableOnBoundaryBoundaryTerm`.
-/
def boundaryCompactMeasureFieldsOfCompactSupportBoundaryBoundaryTerm
    [IsManifold I 1 M]
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    BoundaryCompactMeasureFields mu selectedPartition.active
      D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofCompactSupportBoundaryTermEq
    (mu := mu) (activeCharts := selectedPartition.active)
    (boundaryPieces := D.targetImages.boundaryPieces)
    (oldTerm := BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages)
    (newTerm := D.assembly.boundaryPartitionTerm)
    boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
    boundaryMeasureIntegral boundaryMeasureIntegral_eq_integral
    boundaryPieceSet_measurable boundaryPieceCompactSupport
    boundaryBoundaryTerm_eq_setIntegral
    (fun x hx q hq =>
      D.boundaryBoundaryTerm_eq_assemblyBoundaryPartitionTerm x hx q hq)
    boundaryIntegrand_ae_eq_indicatorSum

/--
The exact boundary set-integral identity needed by
`compactSupportToM8MeasureDataOfReconstruction`, transported from the geometric
boundary term by boundary chart-change/orientation compatibility.
-/
theorem assemblyBoundaryPartitionTerm_eq_setIntegral_of_boundaryBoundaryTerm
    [IsManifold I 1 M]
    (boundaryPieceSet : M -> BoundaryPiece -> Set alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> alpha -> Real)
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu) :
    forall x, x ∈ selectedPartition.active ->
      forall q, q ∈ D.targetImages.boundaryPieces x ->
        D.assembly.boundaryPartitionTerm x q =
          ∫ y in boundaryPieceSet x q,
            boundaryPieceIntegrand x q y ∂mu := by
  intro x hx q hq
  exact
    (D.boundaryBoundaryTerm_eq_assemblyBoundaryPartitionTerm x hx q hq).symm.trans
      (boundaryBoundaryTerm_eq_setIntegral x hx q hq)

/--
Natural compact-support measure package from a boundary reconstruction proved
for `BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages`.

This is the L7 constructor in the shape consumed by
`compactSupportToM8MeasureDataOfReconstruction`: the boundary finite-sum/a.e.
reconstruction and compact-support integrability remain the genuine analytic
hypotheses, while the selected partition term is obtained by transport.
-/
def compactSupportToM8MeasureDataOfBoundaryBoundaryTerm
    [IsManifold I 1 M]
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := alpha) (μ := mu)
        selectedPartition D.targetImages globalBulkIntegral)
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    CompactSupportToM8MeasureData
      (α := alpha) I omega selectedPartition D.targetImages mu :=
  compactSupportToM8MeasureDataOfReconstruction
    (α := alpha) (μ := mu) (I := I) (omega := omega)
    (selectedPartition := selectedPartition) (targetImages := D.targetImages)
    bulk D.assembly.boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
    boundaryPieceIntegrand boundaryMeasureIntegral
    globalBoundaryIntegral_eq_boundaryMeasureIntegral
    boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
    boundaryPieceCompactSupport
    (D.assemblyBoundaryPartitionTerm_eq_setIntegral_of_boundaryBoundaryTerm
      boundaryPieceSet boundaryPieceIntegrand
      boundaryBoundaryTerm_eq_setIntegral)
    boundaryIntegrand_ae_eq_indicatorSum

/--
The boundary reconstruction supplied by
`compactSupportToM8MeasureDataOfBoundaryBoundaryTerm` is the selected finite
sum of the assembly boundary partition terms.
-/
theorem compactSupportToM8MeasureDataOfBoundaryBoundaryTerm_boundaryMeasureIntegral_eq_partitionSum
    [IsManifold I 1 M]
    {globalBulkIntegral globalBoundaryIntegral : Real}
    (bulk :
      BulkMeasureFromPartitionData (α := alpha) (μ := mu)
        selectedPartition D.targetImages globalBulkIntegral)
    (boundaryIntegrand : alpha -> Real)
    (boundaryPieceSet : M -> BoundaryPiece -> Set alpha)
    (boundaryPieceIntegrand : M -> BoundaryPiece -> alpha -> Real)
    (boundaryMeasureIntegral : Real)
    (globalBoundaryIntegral_eq_boundaryMeasureIntegral :
      globalBoundaryIntegral = boundaryMeasureIntegral)
    (boundaryMeasureIntegral_eq_integral :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂mu)
    (boundaryPieceSet_measurable :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          MeasurableSet (boundaryPieceSet x q))
    (boundaryPieceCompactSupport :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          CompactSupportIntegrabilityData (boundaryPieceIntegrand x q))
    (boundaryBoundaryTerm_eq_setIntegral :
      forall x, x ∈ selectedPartition.active ->
        forall q, q ∈ D.targetImages.boundaryPieces x ->
          BoundaryPieceFamilyInput.boundaryBoundaryTerm D.targetImages x q =
            ∫ y in boundaryPieceSet x q,
              boundaryPieceIntegrand x q y ∂mu)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[mu]
        boundaryMeasureIndicatorSum selectedPartition.active
          D.targetImages.boundaryPieces boundaryPieceSet
          boundaryPieceIntegrand) :
    (D.compactSupportToM8MeasureDataOfBoundaryBoundaryTerm
      bulk boundaryIntegrand boundaryPieceSet boundaryPieceIntegrand
      boundaryMeasureIntegral globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
      boundaryPieceCompactSupport boundaryBoundaryTerm_eq_setIntegral
      boundaryIntegrand_ae_eq_indicatorSum).boundary.boundaryMeasureIntegral =
      selectedBoundaryPieceSum selectedPartition.active
        D.targetImages.boundaryPieces D.assembly.boundaryPartitionTerm := by
  simpa [compactSupportToM8MeasureDataOfBoundaryBoundaryTerm] using
    compactSupportToM8MeasureDataOfReconstruction_boundaryMeasureIntegral_eq_partitionSum
      (α := alpha) (μ := mu) (I := I) (omega := omega)
      (selectedPartition := selectedPartition) (targetImages := D.targetImages)
      bulk D.assembly.boundaryPartitionTerm boundaryIntegrand boundaryPieceSet
      boundaryPieceIntegrand boundaryMeasureIntegral
      globalBoundaryIntegral_eq_boundaryMeasureIntegral
      boundaryMeasureIntegral_eq_integral boundaryPieceSet_measurable
      boundaryPieceCompactSupport
      (D.assemblyBoundaryPartitionTerm_eq_setIntegral_of_boundaryBoundaryTerm
        boundaryPieceSet boundaryPieceIntegrand
        boundaryBoundaryTerm_eq_setIntegral)
      boundaryIntegrand_ae_eq_indicatorSum

end CompactSupport

end M8TargetImageInput

end BoundaryMeasureFromPartitionIdentity

end Stokes

end
