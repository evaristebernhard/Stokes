import Stokes.Global.CanonicalIntegralInterface
import Stokes.Global.NaturalCompactSupportStokesStatement

/-!
# Canonical natural compact-support Stokes statement

This file gives the natural compact-support wrapper a theorem stated with the
future-facing canonical integral names:

* `manifoldExtDerivIntegral`, for the eventual value `∫_M dω`;
* `boundaryFormIntegral`, for the eventual value `∫_∂M ω`.

No new analytic content is introduced.  The proof projects the natural input to
the compact-support M8 input and invokes the canonical M8 theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section CanonicalNaturalStokes

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

/--
Canonical Stokes-facing interface carried by a natural compact-support input.

The values are still the represented measure-localization values, but the field
names are the eventual theorem-facing ones.
-/
def measureCanonicalIntegralInterface
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    CanonicalIntegralInterface I omega :=
  D.measure.toM8MeasureLocalizationData.canonicalIntegralInterface

@[simp]
theorem measureCanonicalIntegralInterface_manifoldExtDerivIntegral
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measureCanonicalIntegralInterface.manifoldExtDerivIntegral =
      D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral :=
  rfl

@[simp]
theorem measureCanonicalIntegralInterface_boundaryFormIntegral
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measureCanonicalIntegralInterface.boundaryFormIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  rfl

/--
Natural compact-support Stokes in canonical integral-interface form.

This is a direct consequence of the compact-support M8 canonical theorem.
-/
theorem measureCanonical_stokes
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measureCanonicalIntegralInterface.stokesStatement := by
  simpa [measureCanonicalIntegralInterface,
    CanonicalIntegralInterface.stokesStatement] using
    M8CompactSupportStokesInput.canonical_stokes
      (D.toM8CompactSupportStokesInput)

/--
Natural compact-support Stokes with the two canonical integral names visible in
the statement.
-/
theorem measureCanonical_manifoldExtDerivIntegral_eq_boundaryFormIntegral
    [IsManifold I 1 M]
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measureCanonicalIntegralInterface.manifoldExtDerivIntegral =
      D.measureCanonicalIntegralInterface.boundaryFormIntegral := by
  simpa [CanonicalIntegralInterface.stokesStatement] using D.measureCanonical_stokes

end NaturalCompactSupportStokesInput

/--
Top-level natural compact-support Stokes theorem in canonical names:
`manifoldExtDerivIntegral = boundaryFormIntegral`.
-/
theorem canonicalNaturalCompactSupportStokes_manifoldExtDerivIntegral_eq_boundaryFormIntegral
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : NaturalCompactSupportStokesInput
      (α := α) I omega BoundaryPiece μ) :
    D.measureCanonicalIntegralInterface.manifoldExtDerivIntegral =
      D.measureCanonicalIntegralInterface.boundaryFormIntegral :=
  D.measureCanonical_manifoldExtDerivIntegral_eq_boundaryFormIntegral

end CanonicalNaturalStokes

end Stokes

end
