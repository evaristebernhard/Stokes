import Stokes.Global.NaturalCompactSupportBuilder

/-!
# Higher-level natural Stokes statement wrappers

This file only exposes theorem-level adapters for the natural compact-support
builder.  The mathematical content remains in
`NaturalCompactSupportStokesStatement` and `NaturalCompactSupportBuilder`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section NaturalStokesStatement2

universe u w b a

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {α : Type a} [TopologicalSpace α] [MeasurableSpace α]
variable [OpensMeasurableSpace α] [T2Space α]
variable {μ : Measure α} [IsFiniteMeasureOnCompacts μ]

/--
Top-level compact-support Stokes theorem from builder data.

This is a pure adapter: `NaturalCompactSupportBuilderData` is first forgotten to
the natural compact-support input, then the existing natural statement supplies
the equality.
-/
theorem naturalCompactSupportStokes_builder
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.measure.toM8MeasureLocalizationData.bulkMeasureIntegral =
      D.measure.toM8MeasureLocalizationData.boundaryMeasureIntegral :=
  D.stokes

/--
Top-level compact-support Stokes theorem from builder data, stated using the
compact-support measure package's field names.
-/
theorem naturalCompactSupportStokes_builder_compactSupportFields
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
    [IsManifold I 1 M]
    {omega : ManifoldForm I M n}
    {BoundaryPiece : Type b}
    (D : NaturalCompactSupportBuilderData
      (α := α) I omega BoundaryPiece μ) :
    D.measure.globalBulkIntegral =
      D.measure.boundary.boundaryMeasureIntegral :=
  D.stokes_compactSupportFields

end NaturalStokesStatement2

end Stokes

end
