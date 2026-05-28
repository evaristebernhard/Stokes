import Stokes.Global.ProjectLocalBoundaryMeasureAuto

/-!
# Automatic global boundary-measure facts from canonical indicator pieces

This module reduces the caller surface for
`ProjectLocalBoundaryGlobalMeasureFacts`.

The canonical choice of global boundary integrand is the finite sum of the
indicator-localized project-local lower-zero-face pieces.  With that choice,
the a.e. reconstruction and the integral representation are tautological; the
only remaining global fact is that the represented boundary integral is the
integral of this canonical indicator sum.

A second reconstruction record derives that remaining global fact from active
indicator-piece integrability and the equality between each indicator integral
and the recorded boundary partition term.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BoundaryGlobalMeasureFactsAuto

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {Chart : Type c} {Piece : Type p}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}

namespace ProjectLocalGlobalStokesData

variable (D : ProjectLocalGlobalStokesData I ω Chart Piece)

/-- The canonical global boundary integrand: the finite sum of the
indicator-localized project-local lower-zero-face pieces. -/
def projectLocalBoundaryCanonicalIndicatorSum :
    (Fin n → Real) → Real :=
  boundaryMeasureIndicatorSum D.activeCharts D.localPieces
    D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand

/-- The canonical boundary measure integral represented by the canonical
indicator sum. -/
def projectLocalBoundaryCanonicalIndicatorIntegral : Real :=
  ∫ y, D.projectLocalBoundaryCanonicalIndicatorSum y ∂volume

@[simp]
theorem projectLocalBoundaryCanonicalIndicatorSum_eq :
    D.projectLocalBoundaryCanonicalIndicatorSum =
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand := by
  rfl

@[simp]
theorem projectLocalBoundaryCanonicalIndicatorIntegral_eq :
    D.projectLocalBoundaryCanonicalIndicatorIntegral =
      ∫ y, D.projectLocalBoundaryCanonicalIndicatorSum y ∂volume := by
  rfl

end ProjectLocalGlobalStokesData

/-- Canonical-indicator global measure facts.

The two core fields of `ProjectLocalBoundaryGlobalMeasureFacts` are filled by
choosing the global boundary integrand to be the canonical indicator sum.  The
remaining field records the genuine global reconstruction theorem. -/
structure ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) where
  /-- The represented global boundary integral is the integral of the canonical
  indicator sum. -/
  globalBoundaryIntegral_eq_canonicalIndicatorIntegral :
    D.globalBoundaryIntegral =
      D.projectLocalBoundaryCanonicalIndicatorIntegral

namespace ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (G : ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts D)

/-- Boundary-side integrand selected by the canonical-indicator route. -/
def boundaryIntegrand
    (_G : ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts D) :
    (Fin n → Real) → Real :=
  D.projectLocalBoundaryCanonicalIndicatorSum

/-- Boundary measure integral selected by the canonical-indicator route. -/
def boundaryMeasureIntegral
    (_G : ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts D) : Real :=
  D.projectLocalBoundaryCanonicalIndicatorIntegral

@[simp]
theorem boundaryIntegrand_eq :
    G.boundaryIntegrand =
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand := by
  rfl

@[simp]
theorem boundaryMeasureIntegral_eq :
    G.boundaryMeasureIntegral =
      ∫ y, G.boundaryIntegrand y ∂volume := by
  rfl

/-- The integral field for the canonical-indicator global facts. -/
theorem boundaryMeasureIntegral_eq_integral :
    G.boundaryMeasureIntegral =
      ∫ y, G.boundaryIntegrand y ∂volume := by
  rfl

/-- The a.e. reconstruction field for the canonical-indicator global facts. -/
theorem boundaryIntegrand_ae_eq_indicatorSum :
    G.boundaryIntegrand =ᵐ[(volume : Measure (Fin n → Real))]
      boundaryMeasureIndicatorSum D.activeCharts D.localPieces
        D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand := by
  rfl

/-- Forget the canonical-indicator wrapper to the general global-measure facts. -/
def toGlobalMeasureFacts :
    ProjectLocalBoundaryGlobalMeasureFacts D where
  boundaryIntegrand := G.boundaryIntegrand
  boundaryMeasureIntegral := G.boundaryMeasureIntegral
  globalBoundaryIntegral_eq_boundaryMeasureIntegral :=
    G.globalBoundaryIntegral_eq_canonicalIndicatorIntegral
  boundaryMeasureIntegral_eq_integral :=
    G.boundaryMeasureIntegral_eq_integral
  boundaryIntegrand_ae_eq_indicatorSum :=
    G.boundaryIntegrand_ae_eq_indicatorSum

@[simp]
theorem toGlobalMeasureFacts_boundaryIntegrand :
    G.toGlobalMeasureFacts.boundaryIntegrand = G.boundaryIntegrand := by
  rfl

@[simp]
theorem toGlobalMeasureFacts_boundaryMeasureIntegral :
    G.toGlobalMeasureFacts.boundaryMeasureIntegral =
      G.boundaryMeasureIntegral := by
  rfl

end ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts

/-- Indicator-piece reconstruction input for the canonical project-local
boundary measure facts.

This package exposes the real analytic obligations needed to prove that the
canonical indicator sum integrates to the already recorded project-local
boundary partition sum. -/
structure ProjectLocalBoundaryIndicatorIntegralReconstructionFacts
    (D : ProjectLocalGlobalStokesData I ω Chart Piece) where
  /-- Active indicator-localized canonical boundary pieces are integrable. -/
  boundaryPieceIndicator_integrable :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        Integrable
          (boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
            D.projectLocalBoundaryPieceIntegrand x q)
          (volume : Measure (Fin n → Real))
  /-- Active boundary partition terms are the corresponding indicator
  integrals. -/
  boundaryPartitionTerm_eq_indicatorIntegral :
    ∀ x, x ∈ D.activeCharts →
      ∀ q, q ∈ D.localPieces x →
        D.boundaryPartitionTerm x q =
          ∫ y,
            boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
              D.projectLocalBoundaryPieceIntegrand x q y
              ∂(volume : Measure (Fin n → Real))

namespace ProjectLocalBoundaryIndicatorIntegralReconstructionFacts

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}

/-- The canonical indicator sum integrates to the selected boundary partition
sum. -/
theorem canonicalIndicatorIntegral_eq_partitionSum
    (R : ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D) :
    D.projectLocalBoundaryCanonicalIndicatorIntegral =
      selectedBoundaryPieceSum D.activeCharts D.localPieces
        D.boundaryPartitionTerm := by
  simpa [ProjectLocalGlobalStokesData.projectLocalBoundaryCanonicalIndicatorIntegral,
    ProjectLocalGlobalStokesData.projectLocalBoundaryCanonicalIndicatorSum]
    using
      (boundaryMeasureIntegral_eq_selectedBoundaryPieceSum_of_ae_indicator_eq
        (μ := (volume : Measure (Fin n → Real)))
        D.activeCharts D.localPieces
        (boundaryMeasureIndicatorSum D.activeCharts D.localPieces
          D.projectLocalBoundaryPieceSet D.projectLocalBoundaryPieceIntegrand)
        D.projectLocalBoundaryPieceSet
        D.projectLocalBoundaryPieceIntegrand
        D.boundaryPartitionTerm
        (by rfl)
        (ProjectLocalBoundaryIndicatorIntegralReconstructionFacts.boundaryPieceIndicator_integrable R)
        (fun x hx q hq =>
          (ProjectLocalBoundaryIndicatorIntegralReconstructionFacts.boundaryPartitionTerm_eq_indicatorIntegral
            R x hx q hq).symm))

/-- The existing project-local finite boundary reconstruction identifies the
represented global boundary integral with the canonical indicator integral. -/
theorem globalBoundaryIntegral_eq_canonicalIndicatorIntegral
    (R : ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D) :
    D.globalBoundaryIntegral =
      D.projectLocalBoundaryCanonicalIndicatorIntegral := by
  have hglobal :
      D.globalBoundaryIntegral =
        selectedBoundaryPieceSum D.activeCharts D.localPieces
          D.boundaryPartitionTerm := by
    simpa [selectedBoundaryPieceSum] using
      D.globalBoundaryIntegral_eq_boundaryPartitionSum
  exact hglobal.trans
    (ProjectLocalBoundaryIndicatorIntegralReconstructionFacts.canonicalIndicatorIntegral_eq_partitionSum
      R).symm

/-- Reconstruct the canonical-indicator global measure facts from active
indicator-piece integrability and indicator-integral partition terms. -/
def toCanonicalIndicatorGlobalMeasureFacts
    (R : ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D) :
    ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts D where
  globalBoundaryIntegral_eq_canonicalIndicatorIntegral :=
    ProjectLocalBoundaryIndicatorIntegralReconstructionFacts.globalBoundaryIntegral_eq_canonicalIndicatorIntegral
      R

/-- Reconstruct the general project-local boundary global measure facts. -/
def toGlobalMeasureFacts
    (R : ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D) :
    ProjectLocalBoundaryGlobalMeasureFacts D :=
  (ProjectLocalBoundaryIndicatorIntegralReconstructionFacts.toCanonicalIndicatorGlobalMeasureFacts
    R).toGlobalMeasureFacts

@[simp]
theorem toGlobalMeasureFacts_boundaryIntegrand
    (R : ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D) :
    R.toGlobalMeasureFacts.boundaryIntegrand =
      D.projectLocalBoundaryCanonicalIndicatorSum := by
  rfl

@[simp]
theorem toGlobalMeasureFacts_boundaryMeasureIntegral
    (R : ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D) :
    R.toGlobalMeasureFacts.boundaryMeasureIntegral =
      D.projectLocalBoundaryCanonicalIndicatorIntegral := by
  rfl

end ProjectLocalBoundaryIndicatorIntegralReconstructionFacts

namespace ProjectLocalBoundaryCanonicalFaceContinuityData

variable {D : ProjectLocalGlobalStokesData I ω Chart Piece}
variable (F : ProjectLocalBoundaryCanonicalFaceContinuityData D)

/-- Canonical face continuity plus explicit boundary-term/project-local
alignment gives the indicator-integral reconstruction facts.

The alignment hypothesis is intentionally explicit: selected boundary partition
terms still have to be identified with the project-local boundary integrals by
chart-change/COV data. -/
def toIndicatorIntegralReconstructionFacts
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) ω (D.lowerCorner x q)
              (D.upperCorner x q)) :
    ProjectLocalBoundaryIndicatorIntegralReconstructionFacts D where
  boundaryPieceIndicator_integrable := by
    intro x hx q hq
    simpa [boundaryMeasurePieceIndicator] using
      (F.boundaryPieceIntegrableOn x hx q hq).integrable_indicator
        (F.boundaryPieceSet_measurable x hx q hq)
  boundaryPartitionTerm_eq_indicatorIntegral := by
    intro x hx q hq
    calc
      D.boundaryPartitionTerm x q =
          projectLocalBoundaryIntegral I (D.sourceChart x q)
            (D.targetChart x q) ω (D.lowerCorner x q)
            (D.upperCorner x q) :=
        hterm x hx q hq
      _ =
          ∫ y in D.projectLocalBoundaryPieceSet x q,
            D.projectLocalBoundaryPieceIntegrand x q y ∂volume :=
        D.projectLocalBoundaryIntegral_eq_projectLocalBoundarySetIntegral x q
      _ =
          ∫ y,
            boundaryMeasurePieceIndicator D.projectLocalBoundaryPieceSet
              D.projectLocalBoundaryPieceIntegrand x q y
              ∂(volume : Measure (Fin n → Real)) := by
        simpa [boundaryMeasurePieceIndicator] using
          (integral_indicator
            (μ := (volume : Measure (Fin n → Real)))
            (f := D.projectLocalBoundaryPieceIntegrand x q)
            (F.boundaryPieceSet_measurable x hx q hq)).symm

/-- Canonical face continuity and boundary-term alignment reconstruct the
canonical-indicator global measure facts. -/
def toCanonicalIndicatorGlobalMeasureFacts
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) ω (D.lowerCorner x q)
              (D.upperCorner x q)) :
    ProjectLocalBoundaryCanonicalIndicatorGlobalMeasureFacts D :=
  (F.toIndicatorIntegralReconstructionFacts hterm)
    |>.toCanonicalIndicatorGlobalMeasureFacts

/-- Canonical face continuity and boundary-term alignment reconstruct the
general project-local boundary global measure facts. -/
def toGlobalMeasureFacts
    (hterm :
      ∀ x, x ∈ D.activeCharts →
        ∀ q, q ∈ D.localPieces x →
          D.boundaryPartitionTerm x q =
            projectLocalBoundaryIntegral I (D.sourceChart x q)
              (D.targetChart x q) ω (D.lowerCorner x q)
              (D.upperCorner x q)) :
    ProjectLocalBoundaryGlobalMeasureFacts D :=
  (F.toIndicatorIntegralReconstructionFacts hterm).toGlobalMeasureFacts

end ProjectLocalBoundaryCanonicalFaceContinuityData

end BoundaryGlobalMeasureFactsAuto

end Stokes

end
