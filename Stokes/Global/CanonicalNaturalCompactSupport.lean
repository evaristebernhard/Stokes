import Stokes.Global.CanonicalIntegralInterface
import Stokes.Global.NaturalCompactSupportStokesStatement

/-!
# Canonical names for natural compact-support Stokes

This file is a zero-semantics bridge: it gives the current
`NaturalCompactSupportStokesInput` theorem the future-facing names
`manifoldExtDerivIntegral` and `boundaryFormIntegral`.

It still does not define the true manifold integral or boundary integral.  It
only projects the represented `Real` fields already carried by the M8/natural
compact-support packages.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CanonicalNaturalCompactSupport

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

namespace NaturalCompactSupportStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/-- Canonical integral names carried by a natural compact-support input. -/
def canonicalIntegralInterface
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    CanonicalIntegralInterface I omega :=
  D.toM8CompactSupportStokesInput.canonicalIntegralInterface

/-- Existing represented-integral interface carried by a natural compact-support input. -/
def representedGlobalIntegralInterface
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    GlobalIntegralInterface I omega :=
  D.toM8CompactSupportStokesInput.representedGlobalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBulkIntegral
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.representedGlobalIntegralInterface.globalBulkIntegral =
      D.measure.toM8MeasureLocalizationData.globalBulkIntegral :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBoundaryIntegral
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.representedGlobalIntegralInterface.globalBoundaryIntegral =
      D.measure.toM8MeasureLocalizationData.globalBoundaryIntegral :=
  rfl

/-- Natural compact-support Stokes with canonical theorem-facing names. -/
theorem canonical_stokes
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface] using
    D.toM8CompactSupportStokesInput.canonical_stokes

/-- Natural compact-support Stokes with the older represented-integral interface. -/
theorem representedGlobalIntegralInterface_stokes
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.representedGlobalIntegralInterface.stokesStatement := by
  simpa [representedGlobalIntegralInterface,
    M8CompactSupportStokesInput.representedGlobalIntegralInterface,
    M8GlobalStokesInput.representedGlobalIntegralInterface,
    M8MeasureLocalizationData.representedGlobalIntegralInterface,
    GlobalIntegralInterface.stokesStatement] using
    D.toM8CompactSupportStokesInput.toM8GlobalStokesInput.representedGlobalIntegralInterface_stokes

end NaturalCompactSupportStokesInput

/-- Top-level natural compact-support Stokes theorem with canonical names. -/
theorem naturalCompactSupportStokes_canonical
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.canonicalIntegralInterface.stokesStatement :=
  D.canonical_stokes

/-- Top-level natural compact-support Stokes theorem with represented integral names. -/
theorem naturalCompactSupportStokes_represented
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.representedGlobalIntegralInterface.stokesStatement :=
  D.representedGlobalIntegralInterface_stokes

end CanonicalNaturalCompactSupport

end Stokes

end
