import Stokes.Global.CoverIndexedFromSupportControlledCover
import Stokes.Global.MeasureBoxAPI

/-!
# Cover-indexed bulk measure facts

This file isolates small bulk-side facts for the cover-indexed
compact-support route.  The main constructor removes one common manual field:
from an unlocalized finite-sum reconstruction

`F =ᵐ[μ] fun y => ∑ j, f j y`

and topological support control of each `f j`, it builds the indicator-level
bulk set-integral fields consumed by `SupportControlledCoverIndexedMeasureInput`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoordinateSupportBoxes

/-- The strict coordinate support box used for interior pieces is Borel-measurable. -/
theorem measurableSet_boxInteriorSupportBox {n : Nat}
    (a b : Fin (n + 1) → Real) :
    MeasurableSet (boxInteriorSupportBox a b) := by
  classical
  have hcoord :
      ∀ i : Fin (n + 1),
        MeasurableSet
          {y : Fin (n + 1) → Real | a i < y i ∧ y i < b i} := by
    intro i
    have hlower :
        MeasurableSet {y : Fin (n + 1) → Real | a i < y i} := by
      exact measurableSet_lt measurable_const (continuous_apply i).measurable
    have hupper :
        MeasurableSet {y : Fin (n + 1) → Real | y i < b i} := by
      exact measurableSet_lt (continuous_apply i).measurable measurable_const
    simpa [Set.setOf_and] using hlower.inter hupper
  have hall :
      MeasurableSet
        {y : Fin (n + 1) → Real |
          ∀ i : Fin (n + 1), a i < y i ∧ y i < b i} := by
    simpa [Set.setOf_forall] using (MeasurableSet.iInter hcoord)
  simpa [boxInteriorSupportBox] using hall

universe u w

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}

namespace CompactSupportChartCoverSelection

/--
The coordinate support box assigned to a selected cover index is measurable.

Notice that this is deliberately only a measurability fact: the assigned
support boxes are strict in the artificial directions and are not compact in
general.  Compact carriers for integrability should use closed boxes such as
`Set.Icc`.
-/
theorem measurableSet_assignedCoordinateBox
    (C : CompactSupportChartCoverSelection I K) (j : C.CoverIndex) :
    MeasurableSet (C.assignedCoordinateBox j) := by
  rcases j with j | j
  · simpa [assignedCoordinateBox] using
      measurableSet_boxInteriorSupportBox
        (C.interiorLower j.1) (C.interiorUpper j.1)
  · simpa [assignedCoordinateBox] using
      measurableSet_halfSpaceSupportBox
        (C.boundaryLower j.1) (C.boundaryUpper j.1)

end CompactSupportChartCoverSelection

end CoordinateSupportBoxes

section BulkSetIntegralConstructors

universe u w a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {αBulk : Type a} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]

namespace SupportControlledSelectedPartition

variable {C : CompactSupportChartCoverSelection I K}

/--
Bulk set-integral fields from an unlocalized cover-indexed finite-sum
reconstruction.

This is the bulk-side constructor that should be used before asking callers
for an explicit `bulkIntegrand_ae_eq_indicatorSum`: the indicator insertion is
derived from the `tsupport` containment of each local bulk scalar
representative.
-/
def coverIndexBulkSetIntegralFieldsOfPieceSum
    (P : SupportControlledSelectedPartition C)
    (bulkIntegrand : αBulk → Real)
    (bulkPieceSet : C.CoverIndex → Set αBulk)
    (bulkPieceIntegrand : C.CoverIndex → αBulk → Real)
    (globalBulkIntegral : Real)
    (hglobal :
      globalBulkIntegral = ∫ y, bulkIntegrand y ∂μBulk)
    (hcompact :
      ∀ j : C.CoverIndex, IsCompact (bulkPieceSet j))
    (hcontinuous :
      ∀ j : C.CoverIndex,
        ContinuousOn (bulkPieceIntegrand j) (bulkPieceSet j))
    (htsupport :
      ∀ j : C.CoverIndex,
        tsupport (bulkPieceIntegrand j) ⊆ bulkPieceSet j)
    (hlocal :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in bulkPieceSet j, bulkPieceIntegrand j y ∂μBulk)
    (hpiece :
      bulkIntegrand =ᵐ[μBulk]
        fun y => ∑ j : C.CoverIndex, bulkPieceIntegrand j y) :
    CoverIndexedSetIntegralFields
      (α := αBulk) (Finset.univ : Finset C.CoverIndex) μBulk
      (P.coverIndexLocalBulkTerm ω) := by
  classical
  exact
    CoverIndexedSetIntegralFields.ofTSupportSubsetCompactBoxPieceSum
      (μ := μBulk) (active := (Finset.univ : Finset C.CoverIndex))
      (localTerm := P.coverIndexLocalBulkTerm ω)
      bulkIntegrand bulkPieceSet bulkPieceIntegrand
      globalBulkIntegral hglobal
      (fun j _hj => hcompact j)
      (fun j _hj => hcontinuous j)
      (fun j _hj => htsupport j)
      (fun j _hj => hlocal j)
      (by simpa using hpiece)

/-- The previous constructor reconstructs the represented bulk integral as the finite sum. -/
theorem coverIndexBulkMeasureIntegral_eq_localBulkSum_of_pieceSum
    (P : SupportControlledSelectedPartition C)
    (bulkIntegrand : αBulk → Real)
    (bulkPieceSet : C.CoverIndex → Set αBulk)
    (bulkPieceIntegrand : C.CoverIndex → αBulk → Real)
    (globalBulkIntegral : Real)
    (hglobal :
      globalBulkIntegral = ∫ y, bulkIntegrand y ∂μBulk)
    (hcompact :
      ∀ j : C.CoverIndex, IsCompact (bulkPieceSet j))
    (hcontinuous :
      ∀ j : C.CoverIndex,
        ContinuousOn (bulkPieceIntegrand j) (bulkPieceSet j))
    (htsupport :
      ∀ j : C.CoverIndex,
        tsupport (bulkPieceIntegrand j) ⊆ bulkPieceSet j)
    (hlocal :
      ∀ j : C.CoverIndex,
        P.coverIndexLocalBulkTerm ω j =
          ∫ y in bulkPieceSet j, bulkPieceIntegrand j y ∂μBulk)
    (hpiece :
      bulkIntegrand =ᵐ[μBulk]
        fun y => ∑ j : C.CoverIndex, bulkPieceIntegrand j y) :
    globalBulkIntegral =
      ∑ j : C.CoverIndex, P.coverIndexLocalBulkTerm ω j := by
  classical
  let D :=
    P.coverIndexBulkSetIntegralFieldsOfPieceSum
      (ω := ω) (μBulk := μBulk)
      bulkIntegrand bulkPieceSet bulkPieceIntegrand
      globalBulkIntegral hglobal hcompact hcontinuous htsupport hlocal hpiece
  simpa [D, coverIndexBulkSetIntegralFieldsOfPieceSum]
    using D.measureIntegral_eq_localTermSum

end SupportControlledSelectedPartition

end BulkSetIntegralConstructors

section SupportControlledInputConstructors

universe u w a b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {αBulk : Type a} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
variable {αBoundary : Type b} [TopologicalSpace αBoundary]
variable [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
variable [T2Space αBoundary]
variable {μBoundary : Measure αBoundary}
variable [IsFiniteMeasureOnCompacts μBoundary]

namespace SupportControlledCoverIndexedMeasureInput

/--
Constructor for the support-controlled cover-indexed input where the bulk
measure reconstruction is supplied as an unlocalized finite sum.  The bulk
indicator reconstruction field is generated automatically from
`bulkPiece_tsupport_subset`.
-/
def ofBulkPieceSum
    (chartBoxCover : CompactSupportChartCoverSelection I K)
    (controlledPartition :
      SupportControlledSelectedPartition chartBoxCover)
    (localFields :
      SupportControlledCoverIndexedLocalStokesFields
        controlledPartition ω)
    (bulkIntegrand : αBulk → Real)
    (bulkPieceSet : chartBoxCover.CoverIndex → Set αBulk)
    (bulkPieceIntegrand :
      chartBoxCover.CoverIndex → αBulk → Real)
    (globalBulkIntegral : Real)
    (globalBulkIntegral_eq_integral :
      globalBulkIntegral = ∫ y, bulkIntegrand y ∂μBulk)
    (bulkPiece_isCompact :
      ∀ j : chartBoxCover.CoverIndex, IsCompact (bulkPieceSet j))
    (bulkPiece_continuousOn :
      ∀ j : chartBoxCover.CoverIndex,
        ContinuousOn (bulkPieceIntegrand j) (bulkPieceSet j))
    (bulkPiece_tsupport_subset :
      ∀ j : chartBoxCover.CoverIndex,
        tsupport (bulkPieceIntegrand j) ⊆ bulkPieceSet j)
    (localBulk_eq_setIntegral :
      ∀ j : chartBoxCover.CoverIndex,
        controlledPartition.coverIndexLocalBulkTerm ω j =
          ∫ y in bulkPieceSet j, bulkPieceIntegrand j y ∂μBulk)
    (bulkIntegrand_ae_eq_pieceSum :
      bulkIntegrand =ᵐ[μBulk]
        fun y => ∑ j : chartBoxCover.CoverIndex,
          bulkPieceIntegrand j y)
    (boundaryIntegrand : αBoundary → Real)
    (boundaryPieceSet :
      chartBoxCover.CoverIndex → Set αBoundary)
    (boundaryPieceIntegrand :
      chartBoxCover.CoverIndex → αBoundary → Real)
    (globalBoundaryIntegral : Real)
    (globalBoundaryIntegral_eq_integral :
      globalBoundaryIntegral = ∫ y, boundaryIntegrand y ∂μBoundary)
    (boundaryPiece_isCompact :
      ∀ j : chartBoxCover.CoverIndex, IsCompact (boundaryPieceSet j))
    (boundaryPiece_continuousOn :
      ∀ j : chartBoxCover.CoverIndex,
        ContinuousOn (boundaryPieceIntegrand j) (boundaryPieceSet j))
    (boundaryPiece_tsupport_subset :
      ∀ j : chartBoxCover.CoverIndex,
        tsupport (boundaryPieceIntegrand j) ⊆ boundaryPieceSet j)
    (localBoundary_eq_setIntegral :
      ∀ j : chartBoxCover.CoverIndex,
        controlledPartition.coverIndexLocalBoundaryTerm ω j =
          ∫ y in boundaryPieceSet j,
            boundaryPieceIntegrand j y ∂μBoundary)
    (boundaryIntegrand_ae_eq_indicatorSum :
      boundaryIntegrand =ᵐ[μBoundary]
        fun y => ∑ j : chartBoxCover.CoverIndex,
          (boundaryPieceSet j).indicator
            (boundaryPieceIntegrand j) y) :
    SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary) where
  chartBoxCover := chartBoxCover
  controlledPartition := controlledPartition
  localFields := localFields
  bulkIntegrand := bulkIntegrand
  bulkPieceSet := bulkPieceSet
  bulkPieceIntegrand := bulkPieceIntegrand
  globalBulkIntegral := globalBulkIntegral
  globalBulkIntegral_eq_integral := globalBulkIntegral_eq_integral
  bulkPiece_isCompact := bulkPiece_isCompact
  bulkPiece_continuousOn := bulkPiece_continuousOn
  bulkPiece_tsupport_subset := bulkPiece_tsupport_subset
  localBulk_eq_setIntegral := localBulk_eq_setIntegral
  bulkIntegrand_ae_eq_indicatorSum := by
    classical
    have hindicator :
        bulkIntegrand =ᵐ[μBulk]
          coverIndexedBulkIndicatorSum
            (Finset.univ : Finset chartBoxCover.CoverIndex)
            bulkPieceSet bulkPieceIntegrand :=
      coverIndexed_bulkIntegrand_ae_eq_indicator_sum_of_tsupport_subset
        (μ := μBulk) (active := (Finset.univ : Finset chartBoxCover.CoverIndex))
        bulkIntegrand bulkPieceSet bulkPieceIntegrand
        (by simpa using bulkIntegrand_ae_eq_pieceSum)
        (fun j _hj => bulkPiece_tsupport_subset j)
    simpa [coverIndexedBulkIndicatorSum] using hindicator
  boundaryIntegrand := boundaryIntegrand
  boundaryPieceSet := boundaryPieceSet
  boundaryPieceIntegrand := boundaryPieceIntegrand
  globalBoundaryIntegral := globalBoundaryIntegral
  globalBoundaryIntegral_eq_integral := globalBoundaryIntegral_eq_integral
  boundaryPiece_isCompact := boundaryPiece_isCompact
  boundaryPiece_continuousOn := boundaryPiece_continuousOn
  boundaryPiece_tsupport_subset := boundaryPiece_tsupport_subset
  localBoundary_eq_setIntegral := localBoundary_eq_setIntegral
  boundaryIntegrand_ae_eq_indicatorSum := boundaryIntegrand_ae_eq_indicatorSum

end SupportControlledCoverIndexedMeasureInput

end SupportControlledInputConstructors

end Stokes

end
