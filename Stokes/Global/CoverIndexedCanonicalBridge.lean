import Stokes.Global.CanonicalIntegralInterface
import Stokes.Global.CoverIndexedFromSupportControlledCover
import Stokes.Global.CoverIndexedPublicTheorem

/-!
# Canonical names for the cover-indexed compact-support route

This file connects the newer cover-indexed compact-support Stokes core to the
future-facing `CanonicalIntegralInterface`.

The bridge is intentionally still at the represented `Real` layer.  It does
not define a mathlib-native manifold integral or boundary integral.  Its
purpose is to let downstream statements use the canonical names

* `manifoldExtDerivIntegral`, for the represented `∫_M dω`;
* `boundaryFormIntegral`, for the represented `∫_∂M ω`;

while making the proof source explicitly the cover-indexed core rather than the
older M8 reconstruction package.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section SupportControlledCoverIndexed

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

/-- The represented global integral interface carried by the cover-indexed input. -/
def representedGlobalIntegralInterface
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    GlobalIntegralInterface I ω where
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral

/--
Canonical Stokes-facing names for the represented integrals in a
support-controlled cover-indexed input.
-/
def canonicalIntegralInterface
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    CanonicalIntegralInterface I ω :=
  CanonicalIntegralInterface.ofGlobalIntegralInterface
    D.representedGlobalIntegralInterface

@[simp]
theorem representedGlobalIntegralInterface_globalBulkIntegral
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.representedGlobalIntegralInterface.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBoundaryIntegral
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.representedGlobalIntegralInterface.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_stokesStatement
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.representedGlobalIntegralInterface.stokesStatement ↔
      D.globalBulkIntegral = D.globalBoundaryIntegral :=
  Iff.rfl

@[simp]
theorem canonicalIntegralInterface_stokesStatement
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.canonicalIntegralInterface.stokesStatement ↔
      D.globalBulkIntegral = D.globalBoundaryIntegral :=
  Iff.rfl

/--
The support-controlled cover-indexed route proves the represented global
interface-level Stokes statement.
-/
theorem representedGlobalIntegralInterface_stokes
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.representedGlobalIntegralInterface.stokesStatement := by
  simpa [GlobalIntegralInterface.stokesStatement] using D.stokes

/--
The support-controlled cover-indexed route proves the canonical represented
Stokes statement.
-/
theorem canonical_stokes
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [CanonicalIntegralInterface.stokesStatement] using D.stokes

/--
Same theorem as `canonical_stokes`, with the proof source left visibly at the
cover-indexed measure-field projection.
-/
theorem canonical_stokes_via_coverIndexedMeasureFields
    (D : SupportControlledCoverIndexedMeasureInput
      (I := I) (K := K) (ω := ω)
      (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    D.toCoverIndexedMeasureFields.stokes

end SupportControlledCoverIndexedMeasureInput

end SupportControlledCoverIndexed

section PublicCoverIndexed

universe e h m u a b

variable {E : Type e} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type h} [TopologicalSpace H]
variable {M : Type m} [TopologicalSpace M] [ChartedSpace H M]
variable {k : Nat}
variable {I : ModelWithCorners Real E H}
variable {ω : ManifoldForm I M k}
variable {ι : Type u}
variable {αBulk : Type a} [TopologicalSpace αBulk]
variable [MeasurableSpace αBulk] [OpensMeasurableSpace αBulk]
variable [T2Space αBulk]
variable {μBulk : Measure αBulk} [IsFiniteMeasureOnCompacts μBulk]
variable {αBoundary : Type b} [TopologicalSpace αBoundary]
variable [MeasurableSpace αBoundary] [OpensMeasurableSpace αBoundary]
variable [T2Space αBoundary]
variable {μBoundary : Measure αBoundary}
variable [IsFiniteMeasureOnCompacts μBoundary]

namespace CoverIndexedCompactSupportStokesInput

/--
Interpret a public cover-indexed input as the represented global integral
interface for any chosen manifold-form endpoint.
-/
def representedGlobalIntegralInterface
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    GlobalIntegralInterface I ω where
  globalBulkIntegral := D.globalBulk
  globalBoundaryIntegral := D.globalBoundary

/--
Canonical represented integral names attached to a public cover-indexed input.

The public input is intentionally cover-indexed and scalar.  The parameters
`I` and `ω` only choose the endpoint type of the canonical interface; the
represented `Real` values still come from the cover-indexed fields.
-/
def canonicalIntegralInterface
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    CanonicalIntegralInterface I ω :=
  CanonicalIntegralInterface.ofGlobalIntegralInterface
    D.representedGlobalIntegralInterface

@[simp]
theorem representedGlobalIntegralInterface_globalBulkIntegral
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.representedGlobalIntegralInterface
      (I := I) (ω := ω) D).globalBulkIntegral =
      D.globalBulk :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBoundaryIntegral
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.representedGlobalIntegralInterface
      (I := I) (ω := ω) D).globalBoundaryIntegral =
      D.globalBoundary :=
  rfl

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.canonicalIntegralInterface
      (I := I) (ω := ω) D).manifoldExtDerivIntegral =
      D.globalBulk :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.canonicalIntegralInterface
      (I := I) (ω := ω) D).boundaryFormIntegral =
      D.globalBoundary :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_stokesStatement
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.representedGlobalIntegralInterface
      (I := I) (ω := ω) D).stokesStatement ↔
      D.globalBulk = D.globalBoundary :=
  Iff.rfl

@[simp]
theorem canonicalIntegralInterface_stokesStatement
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.canonicalIntegralInterface
      (I := I) (ω := ω) D).stokesStatement ↔
      D.globalBulk = D.globalBoundary :=
  Iff.rfl

/--
The public cover-indexed theorem proves the represented global interface-level
Stokes statement.
-/
theorem representedGlobalIntegralInterface_stokes
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.representedGlobalIntegralInterface
      (I := I) (ω := ω) D).stokesStatement := by
  simpa [GlobalIntegralInterface.stokesStatement] using D.stokes

/--
The public cover-indexed theorem proves the canonical represented Stokes
statement.
-/
theorem canonical_stokes
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.canonicalIntegralInterface
      (I := I) (ω := ω) D).stokesStatement := by
  simpa [CanonicalIntegralInterface.stokesStatement] using D.stokes

/--
Same canonical theorem, stated with the top-level public theorem as the proof
source.
-/
theorem canonical_stokes_via_coverIndexedCompactSupportStokes
    (D : CoverIndexedCompactSupportStokesInput
      (ι := ι) (αBulk := αBulk) (μBulk := μBulk)
      (αBoundary := αBoundary) (μBoundary := μBoundary)) :
    (CoverIndexedCompactSupportStokesInput.canonicalIntegralInterface
      (I := I) (ω := ω) D).stokesStatement := by
  simpa [CanonicalIntegralInterface.stokesStatement] using
    coverIndexedCompactSupportStokes D

end CoverIndexedCompactSupportStokesInput

end PublicCoverIndexed

end Stokes

end
