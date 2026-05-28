import Stokes.Global.ProjectLocalBoundaryMeasureAuto

/-!
# Canonical lower-face support containment

The raw project-local lower-face scalar representative is integrated over the
selected lower-zero-face domain, but it is not definitionally zero away from
that domain.  The unconditional support-containment fact is therefore for the
indicator-localized representative used by the canonical finite reconstruction
route.

For the older `ProjectLocalBoundarySupportFiniteMeasureFacts` record, whose
field still asks for support containment of the raw representative, this module
provides a small truthful constructor from an explicit zero-off hypothesis.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryCanonicalSupportContainmentAuto

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

namespace ProjectLocalGlobalStokesData

variable (D : ProjectLocalGlobalStokesData I ω Chart Piece)

/-- The indicator-localized canonical lower-face representative is supported
in its selected lower-zero-face domain. -/
theorem projectLocalBoundaryPieceIndicator_support_subset
    (x : Chart) (q : Piece) :
    Function.support
        (boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
          D.projectLocalBoundaryPieceIntegrand x q) ⊆
      D.projectLocalBoundaryPieceSet x q :=
  boundaryMeasurePieceIndicator_support_subset
    D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand x q

/-- Active-field shape of
`ProjectLocalGlobalStokesData.projectLocalBoundaryPieceIndicator_support_subset`. -/
theorem boundaryPieceIndicator_support_subset
    (x : Chart) (_hx : x ∈ D.activeCharts)
    (q : Piece) (_hq : q ∈ D.localPieces x) :
    Function.support
        (boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
          D.projectLocalBoundaryPieceIntegrand x q) ⊆
      D.projectLocalBoundaryPieceSet x q :=
  D.projectLocalBoundaryPieceIndicator_support_subset x q

/-- A genuine zero-off statement for the raw canonical scalar representative
implies the raw support-containment field requested by
`ProjectLocalBoundarySupportFiniteMeasureFacts`. -/
theorem boundaryPiece_support_subset_of_eq_zero_off
    (hzero :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          ∀ y : Fin n → Real,
            y ∉ D.projectLocalBoundaryPieceSet x q →
              D.projectLocalBoundaryPieceIntegrand x q y = 0) :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        Function.support (D.projectLocalBoundaryPieceIntegrand x q) ⊆
          D.projectLocalBoundaryPieceSet x q := by
  intro x hx q hq y hy
  by_contra hmem
  exact hy (hzero x hx q hq y hmem)

/-- Constructor for the raw support-finite measure facts from an explicit
zero-off hypothesis for the raw canonical scalar representatives.  The
zero-off hypothesis is intentionally explicit: without indicator localization,
it is not a definitional consequence of the lower-face set integral. -/
def toProjectLocalBoundarySupportFiniteMeasureFactsOfEqZeroOff
    (boundaryMeasureIntegral : Real)
    (hglobal :
      D.globalBoundaryIntegral = boundaryMeasureIntegral)
    (hintegral :
      boundaryMeasureIntegral =
        ∫ y,
          boundaryMeasurePieceSum D.activeCharts D.localPieces
            D.projectLocalBoundaryPieceIntegrand y ∂volume)
    (hzero :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          ∀ y : Fin n → Real,
            y ∉ D.projectLocalBoundaryPieceSet x q →
              D.projectLocalBoundaryPieceIntegrand x q y = 0) :
    ProjectLocalBoundarySupportFiniteMeasureFacts D where
  boundaryMeasureIntegral := boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral := hglobal
  boundaryMeasureIntegral_eq_integral := hintegral
  boundaryPiece_support_subset :=
    D.boundaryPiece_support_subset_of_eq_zero_off hzero

end ProjectLocalGlobalStokesData

namespace ProjectLocalBoundaryMeasureConstructorInput

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (C : ProjectLocalBoundaryMeasureConstructorInput D)

/-- The support-finite pieces produced from the project-local constructor use
indicator-localized canonical lower-face representatives, hence their support
containment is automatic. -/
theorem toBoundaryPieceSupportFiniteSumInput_boundaryPiece_support_subset
    (x : Chart) (hx : x ∈ D.activeCharts)
    (q : Piece) (hq : q ∈ D.localPieces x) :
    Function.support
        (C.toBoundaryPieceSupportFiniteSumInput.boundaryPieceIntegrand x q) ⊆
      C.toBoundaryPieceSupportFiniteSumInput.boundaryPieceSet x q :=
  C.toBoundaryPieceSupportFiniteSumInput.boundaryPiece_support_subset x hx q hq

end ProjectLocalBoundaryMeasureConstructorInput

end BoundaryCanonicalSupportContainmentAuto

end Stokes

end
