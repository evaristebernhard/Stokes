import Stokes.Global.BoundaryMeasureFromPartition

/-!
# Boundary-piece integrability to boundary measure localization

This file connects the lower-zero-face integrability facts proved in
`BoundaryIntegrabilityCompactSupport` to the boundary measure-localization
constructors in `BoundaryCompactMeasure` and `BoundaryMeasureFromPartition`.

The genuine global measure statement is still explicit: callers must supply the
represented boundary integral, the piecewise set-integral terms, and the a.e.
finite indicator reconstruction of the boundary integrand.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryPieceIntegrabilityToMeasure

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Finite boundary-piece data equipped with the three local integrability outputs
from `BoundaryIntegrabilityData`.

For each active piece, the source lower-zero face supports the transition
pullback and Jacobian-weighted integrands; the target lower-zero face supports
the target in-chart integrand.
-/
structure BoundaryPieceIntegrabilityFamilyData {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (Piece : Type p) where
  /-- Active chart labels in the finite boundary decomposition. -/
  activeCharts : Finset Chart
  /-- Boundary pieces assigned to each active chart. -/
  boundaryPieces : Chart → Finset Piece
  /-- Source chart for the local boundary transition. -/
  sourceChart : Chart → Piece → M
  /-- Boundary-source chart for the local boundary transition. -/
  boundarySourceChart : Chart → Piece → M
  /-- Lower corner of the source lower-zero face box. -/
  sourceLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the source lower-zero face box. -/
  sourceUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Lower corner of the target lower-zero face box. -/
  targetLowerCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Upper corner of the target lower-zero face box. -/
  targetUpperCorner : Chart → Piece → Fin (n + 1) → Real
  /-- Integrability data for every active boundary piece. -/
  integrability :
    ∀ x, x ∈ activeCharts →
      ∀ q, q ∈ boundaryPieces x →
        BoundaryIntegrabilityData I (sourceChart x q) (boundarySourceChart x q) ω
          (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x q) (targetUpperCorner x q)

namespace BoundaryPieceIntegrabilityFamilyData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/-- Source transition-pullback scalar integrand for one boundary piece. -/
def sourceTransitionIntegrand
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) : (Fin n → Real) → Real :=
  boundaryChartTransitionPullbackIntegrand I (D.sourceChart x q)
    (D.boundarySourceChart x q) ω

/-- Jacobian-weighted source scalar integrand for one boundary piece. -/
def jacobianSourceIntegrand
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) : (Fin n → Real) → Real :=
  boundaryChartTransitionJacobianIntegrand I (D.sourceChart x q)
    (D.boundarySourceChart x q) ω

/-- Target in-chart scalar boundary integrand for one boundary piece. -/
def targetInChartIntegrand
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) : (Fin n → Real) → Real :=
  boundaryChartInChartIntegrand I (D.boundarySourceChart x q) ω

/-- Boundary measure partition data carried by the integrability family. -/
def toBoundaryMeasurePartitionData
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (boundaryPartitionTerm : Chart → Piece → Real) :
    BoundaryMeasurePartitionData Chart Piece where
  activeCharts := D.activeCharts
  boundaryPieces := D.boundaryPieces
  boundaryPartitionTerm := boundaryPartitionTerm

/-- Source transition-pullback integrability on an active source face. -/
theorem sourceTransition_integrableOn
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.boundaryPieces x) :
    IntegrableOn (D.sourceTransitionIntegrand x q)
      (lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)) :=
  by
    simpa [sourceTransitionIntegrand] using
      (D.integrability x hx q hq).source_boundary_integrableOn

/-- Jacobian-weighted source integrability on an active source face. -/
theorem jacobianSource_integrableOn
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.boundaryPieces x) :
    IntegrableOn (D.jacobianSourceIntegrand x q)
      (lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)) :=
  by
    simpa [jacobianSourceIntegrand] using
      (D.integrability x hx q hq).jacobian_integrableOn

/-- Target in-chart integrability on an active target face. -/
theorem targetInChart_integrableOn
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    {x : Chart} (hx : x ∈ D.activeCharts)
    {q : Piece} (hq : q ∈ D.boundaryPieces x) :
    IntegrableOn (D.targetInChartIntegrand x q)
      (lowerZeroFaceDomain (D.targetLowerCorner x q) (D.targetUpperCorner x q)) :=
  by
    simpa [targetInChartIntegrand] using
      (D.integrability x hx q hq).target_boundary_integrableOn

/--
Boundary compact-measure fields using the Jacobian-weighted source integrand
on each source lower-zero face.
-/
def jacobianSourceCompactMeasureFields
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (D.sourceLowerCorner x q)
                (D.sourceUpperCorner x q),
              D.jacobianSourceIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          (fun x q =>
            lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q))
          D.jacobianSourceIntegrand) :
    BoundaryCompactMeasureFields (α := Fin n → Real)
      (μ := volume) D.activeCharts D.boundaryPieces boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofLowerZeroFaceIntegrable
    (activeCharts := D.activeCharts) (boundaryPieces := D.boundaryPieces)
    (boundaryPartitionTerm := boundaryPartitionTerm)
    boundaryIntegrand D.sourceLowerCorner D.sourceUpperCorner
    D.jacobianSourceIntegrand boundaryMeasureIntegral hmeasure
    (fun x hx q hq => D.jacobianSource_integrableOn (x := x) hx (q := q) hq)
    hterm hboundary

/--
Boundary measure localization data using the Jacobian-weighted source
integrand on each source lower-zero face.
-/
def jacobianSourceLocalizationData
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (D.sourceLowerCorner x q)
                (D.sourceUpperCorner x q),
              D.jacobianSourceIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          (fun x q =>
            lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q))
          D.jacobianSourceIntegrand) :
    BoundaryMeasureLocalizationData (volume : Measure (Fin n → Real))
      D.activeCharts D.boundaryPieces boundaryPartitionTerm :=
  (D.jacobianSourceCompactMeasureFields boundaryIntegrand boundaryPartitionTerm
    boundaryMeasureIntegral hmeasure hterm hboundary)
    |>.toBoundaryMeasureLocalizationData

/--
The same Jacobian-source localization, routed through
`BoundaryMeasurePartitionData` so downstream code can use the partition-facing
API from `BoundaryMeasureFromPartition`.
-/
def jacobianSourceLocalizationDataFromPartition
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (D.sourceLowerCorner x q)
                (D.sourceUpperCorner x q),
              D.jacobianSourceIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          (fun x q =>
            lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q))
          D.jacobianSourceIntegrand) :
    BoundaryMeasureLocalizationData (volume : Measure (Fin n → Real))
      D.activeCharts D.boundaryPieces boundaryPartitionTerm :=
  (D.toBoundaryMeasurePartitionData boundaryPartitionTerm).localizationDataOfIntegrableOn
    (μ := (volume : Measure (Fin n → Real)))
    boundaryIntegrand
    (fun x q =>
      lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q))
    D.jacobianSourceIntegrand boundaryMeasureIntegral hmeasure
    (fun x _ q _ =>
      measurableSet_lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q))
    (fun x hx q hq => D.jacobianSource_integrableOn (x := x) hx (q := q) hq)
    hterm hboundary

/--
Boundary compact-measure fields using the transition-pullback source integrand
on each source lower-zero face.
-/
def sourceTransitionCompactMeasureFields
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (D.sourceLowerCorner x q)
                (D.sourceUpperCorner x q),
              D.sourceTransitionIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          (fun x q =>
            lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q))
          D.sourceTransitionIntegrand) :
    BoundaryCompactMeasureFields (α := Fin n → Real)
      (μ := volume) D.activeCharts D.boundaryPieces boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofLowerZeroFaceIntegrable
    (activeCharts := D.activeCharts) (boundaryPieces := D.boundaryPieces)
    (boundaryPartitionTerm := boundaryPartitionTerm)
    boundaryIntegrand D.sourceLowerCorner D.sourceUpperCorner
    D.sourceTransitionIntegrand boundaryMeasureIntegral hmeasure
    (fun x hx q hq => D.sourceTransition_integrableOn (x := x) hx (q := q) hq)
    hterm hboundary

/-- Boundary measure localization using source transition-pullback integrands. -/
def sourceTransitionLocalizationData
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (D.sourceLowerCorner x q)
                (D.sourceUpperCorner x q),
              D.sourceTransitionIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          (fun x q =>
            lowerZeroFaceDomain (D.sourceLowerCorner x q) (D.sourceUpperCorner x q))
          D.sourceTransitionIntegrand) :
    BoundaryMeasureLocalizationData (volume : Measure (Fin n → Real))
      D.activeCharts D.boundaryPieces boundaryPartitionTerm :=
  (D.sourceTransitionCompactMeasureFields boundaryIntegrand boundaryPartitionTerm
    boundaryMeasureIntegral hmeasure hterm hboundary)
    |>.toBoundaryMeasureLocalizationData

/--
Boundary compact-measure fields using the target in-chart integrand on each
target lower-zero face.
-/
def targetInChartCompactMeasureFields
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (D.targetLowerCorner x q)
                (D.targetUpperCorner x q),
              D.targetInChartIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          (fun x q =>
            lowerZeroFaceDomain (D.targetLowerCorner x q) (D.targetUpperCorner x q))
          D.targetInChartIntegrand) :
    BoundaryCompactMeasureFields (α := Fin n → Real)
      (μ := volume) D.activeCharts D.boundaryPieces boundaryPartitionTerm :=
  BoundaryCompactMeasureFields.ofLowerZeroFaceIntegrable
    (activeCharts := D.activeCharts) (boundaryPieces := D.boundaryPieces)
    (boundaryPartitionTerm := boundaryPartitionTerm)
    boundaryIntegrand D.targetLowerCorner D.targetUpperCorner
    D.targetInChartIntegrand boundaryMeasureIntegral hmeasure
    (fun x hx q hq => D.targetInChart_integrableOn (x := x) hx (q := q) hq)
    hterm hboundary

/-- Boundary measure localization using target in-chart integrands. -/
def targetInChartLocalizationData
    (D : BoundaryPieceIntegrabilityFamilyData I ω Chart Piece)
    (boundaryIntegrand : (Fin n → Real) → Real)
    (boundaryPartitionTerm : Chart → Piece → Real)
    (boundaryMeasureIntegral : Real)
    (hmeasure :
      boundaryMeasureIntegral = ∫ y, boundaryIntegrand y ∂volume)
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.boundaryPieces x →
          boundaryPartitionTerm x q =
            ∫ y in lowerZeroFaceDomain (D.targetLowerCorner x q)
                (D.targetUpperCorner x q),
              D.targetInChartIntegrand x q y ∂volume)
    (hboundary :
      boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
        boundaryMeasureIndicatorSum D.activeCharts D.boundaryPieces
          (fun x q =>
            lowerZeroFaceDomain (D.targetLowerCorner x q) (D.targetUpperCorner x q))
          D.targetInChartIntegrand) :
    BoundaryMeasureLocalizationData (volume : Measure (Fin n → Real))
      D.activeCharts D.boundaryPieces boundaryPartitionTerm :=
  (D.targetInChartCompactMeasureFields boundaryIntegrand boundaryPartitionTerm
    boundaryMeasureIntegral hmeasure hterm hboundary)
    |>.toBoundaryMeasureLocalizationData

end BoundaryPieceIntegrabilityFamilyData

end BoundaryPieceIntegrabilityToMeasure

end Stokes

end
