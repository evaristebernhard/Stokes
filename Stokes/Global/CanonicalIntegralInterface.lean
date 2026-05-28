import Stokes.Global.GlobalIntegralDefinitions
import Stokes.Global.M8CompactSupportStatement

/-!
# Canonical integral interface skeleton

This file separates the future canonical names

* `∫_M dω`, represented here by `manifoldExtDerivIntegral`;
* `∫_∂M ω`, represented here by `boundaryFormIntegral`;

from the current bookkeeping names `globalBulkIntegral` and
`globalBoundaryIntegral`.

The record is still only a `Real`-valued skeleton.  It does not define the
manifold integral or the boundary integral.  Its purpose is to make later files
depend on canonical Stokes-facing names while retaining projection theorems to
the existing represented-integral API.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section CanonicalInterface

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Future-facing names for the two global integrals in Stokes' theorem.

At this stage both fields are represented `Real` values.  The names are chosen
so that downstream theorem statements can talk about the mathematical sides of
Stokes' theorem without depending on the current reconstruction-field names.
-/
structure CanonicalIntegralInterface {k : Nat}
    (I : ModelWithCorners Real E H) (omega : ManifoldForm I M k) where
  /-- Placeholder for the future canonical value `∫_M dω`. -/
  manifoldExtDerivIntegral : Real
  /-- Placeholder for the future canonical value `∫_∂M ω`. -/
  boundaryFormIntegral : Real

namespace CanonicalIntegralInterface

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {omega : ManifoldForm I M k}

/-- Build the canonical skeleton from explicitly named values. -/
def ofValues (manifoldExtDerivIntegral boundaryFormIntegral : Real) :
    CanonicalIntegralInterface I omega where
  manifoldExtDerivIntegral := manifoldExtDerivIntegral
  boundaryFormIntegral := boundaryFormIntegral

/-- The canonical Stokes statement, currently at the represented-`Real` level. -/
def stokesStatement (J : CanonicalIntegralInterface I omega) : Prop :=
  J.manifoldExtDerivIntegral = J.boundaryFormIntegral

/--
Forget the canonical names and expose the existing represented-integral
interface.
-/
def toGlobalIntegralInterface
    (J : CanonicalIntegralInterface I omega) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := J.manifoldExtDerivIntegral
  globalBoundaryIntegral := J.boundaryFormIntegral

/-- Interpret an existing represented-integral interface with canonical names. -/
def ofGlobalIntegralInterface
    (J : GlobalIntegralInterface I omega) :
    CanonicalIntegralInterface I omega where
  manifoldExtDerivIntegral := J.globalBulkIntegral
  boundaryFormIntegral := J.globalBoundaryIntegral

@[simp]
theorem ofValues_manifoldExtDerivIntegral
    (manifoldExtDerivIntegral boundaryFormIntegral : Real) :
    (ofValues (I := I) (omega := omega)
      manifoldExtDerivIntegral boundaryFormIntegral
    ).manifoldExtDerivIntegral = manifoldExtDerivIntegral :=
  rfl

@[simp]
theorem ofValues_boundaryFormIntegral
    (manifoldExtDerivIntegral boundaryFormIntegral : Real) :
    (ofValues (I := I) (omega := omega)
      manifoldExtDerivIntegral boundaryFormIntegral
    ).boundaryFormIntegral = boundaryFormIntegral :=
  rfl

@[simp]
theorem toGlobalIntegralInterface_globalBulkIntegral
    (J : CanonicalIntegralInterface I omega) :
    J.toGlobalIntegralInterface.globalBulkIntegral =
      J.manifoldExtDerivIntegral :=
  rfl

@[simp]
theorem toGlobalIntegralInterface_globalBoundaryIntegral
    (J : CanonicalIntegralInterface I omega) :
    J.toGlobalIntegralInterface.globalBoundaryIntegral =
      J.boundaryFormIntegral :=
  rfl

@[simp]
theorem ofGlobalIntegralInterface_manifoldExtDerivIntegral
    (J : GlobalIntegralInterface I omega) :
    (ofGlobalIntegralInterface J).manifoldExtDerivIntegral =
      J.globalBulkIntegral :=
  rfl

@[simp]
theorem ofGlobalIntegralInterface_boundaryFormIntegral
    (J : GlobalIntegralInterface I omega) :
    (ofGlobalIntegralInterface J).boundaryFormIntegral =
      J.globalBoundaryIntegral :=
  rfl

@[simp]
theorem toGlobalIntegralInterface_stokesStatement
    (J : CanonicalIntegralInterface I omega) :
    J.toGlobalIntegralInterface.stokesStatement ↔ J.stokesStatement :=
  Iff.rfl

@[simp]
theorem ofGlobalIntegralInterface_stokesStatement
    (J : GlobalIntegralInterface I omega) :
    (ofGlobalIntegralInterface J).stokesStatement ↔ J.stokesStatement :=
  Iff.rfl

@[simp]
theorem toGlobalIntegralInterface_ofGlobalIntegralInterface
    (J : GlobalIntegralInterface I omega) :
    (ofGlobalIntegralInterface J).toGlobalIntegralInterface = J := by
  cases J
  rfl

@[simp]
theorem ofGlobalIntegralInterface_toGlobalIntegralInterface
    (J : CanonicalIntegralInterface I omega) :
    ofGlobalIntegralInterface J.toGlobalIntegralInterface = J := by
  cases J
  rfl

end CanonicalIntegralInterface

end CanonicalInterface

section M8Projections

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}

namespace M8MeasureLocalizationData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}

/--
Canonical Stokes-facing interface for the measure-level M8 integrals.

These are the values in the theorem `m8GlobalStokes`.
-/
def canonicalIntegralInterface
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    CanonicalIntegralInterface I omega where
  manifoldExtDerivIntegral := D.bulkMeasureIntegral
  boundaryFormIntegral := D.boundaryMeasureIntegral

/--
Existing represented-integral interface carried by the M8 localization record.

This keeps the old `globalBulkIntegral`/`globalBoundaryIntegral` names
available without making them the canonical theorem-facing names.
-/
def representedGlobalIntegralInterface
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral

/-- Canonical names applied to the existing represented-integral fields. -/
def representedCanonicalIntegralInterface
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    CanonicalIntegralInterface I omega :=
  CanonicalIntegralInterface.ofGlobalIntegralInterface
    D.representedGlobalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBulkIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.representedGlobalIntegralInterface.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBoundaryIntegral
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.representedGlobalIntegralInterface.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem representedCanonicalIntegralInterface_toGlobalIntegralInterface
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.representedCanonicalIntegralInterface.toGlobalIntegralInterface =
      D.representedGlobalIntegralInterface :=
  rfl

@[simp]
theorem canonicalIntegralInterface_stokesStatement
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.canonicalIntegralInterface.stokesStatement ↔
      D.bulkMeasureIntegral = D.boundaryMeasureIntegral :=
  Iff.rfl

@[simp]
theorem representedGlobalIntegralInterface_stokesStatement
    (D : M8MeasureLocalizationData I omega selectedPartition targetImages) :
    D.representedGlobalIntegralInterface.stokesStatement ↔
      D.globalBulkIntegral = D.globalBoundaryIntegral :=
  Iff.rfl

end M8MeasureLocalizationData

namespace M8GlobalStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}

/-- Canonical measure-level integral interface carried by an M8 input. -/
def canonicalIntegralInterface
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    CanonicalIntegralInterface I omega :=
  D.measureLocalization.canonicalIntegralInterface

/-- Existing represented-integral interface carried by an M8 input. -/
def representedGlobalIntegralInterface
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    GlobalIntegralInterface I omega :=
  D.measureLocalization.representedGlobalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.measureLocalization.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.measureLocalization.boundaryMeasureIntegral :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBulkIntegral
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.representedGlobalIntegralInterface.globalBulkIntegral =
      D.measureLocalization.globalBulkIntegral :=
  rfl

@[simp]
theorem representedGlobalIntegralInterface_globalBoundaryIntegral
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.representedGlobalIntegralInterface.globalBoundaryIntegral =
      D.measureLocalization.globalBoundaryIntegral :=
  rfl

/-- M8 proves the canonical measure-level Stokes statement. -/
theorem canonical_stokes
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface,
    M8MeasureLocalizationData.canonicalIntegralInterface,
    CanonicalIntegralInterface.stokesStatement] using D.stokes

/-- M8 also proves the older represented-integral Stokes statement. -/
theorem representedGlobalIntegralInterface_stokes
    [IsManifold I 1 M]
    (D : M8GlobalStokesInput I omega BoundaryPiece) :
    D.representedGlobalIntegralInterface.stokesStatement := by
  simpa [representedGlobalIntegralInterface,
    M8MeasureLocalizationData.representedGlobalIntegralInterface,
    GlobalIntegralInterface.stokesStatement] using D.represented_stokes

end M8GlobalStokesInput

namespace M8CompactSupportStokesInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {BoundaryPiece : Type b}

/-- Canonical measure-level integral interface carried by compact M8 input. -/
def canonicalIntegralInterface
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    CanonicalIntegralInterface I omega :=
  D.toM8GlobalStokesInput.canonicalIntegralInterface

/-- Existing represented-integral interface carried by compact M8 input. -/
def representedGlobalIntegralInterface
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    GlobalIntegralInterface I omega :=
  D.toM8GlobalStokesInput.representedGlobalIntegralInterface

@[simp]
theorem canonicalIntegralInterface_manifoldExtDerivIntegral
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.canonicalIntegralInterface.manifoldExtDerivIntegral =
      D.measureResolved.measureLocalization.bulkMeasureIntegral :=
  rfl

@[simp]
theorem canonicalIntegralInterface_boundaryFormIntegral
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.canonicalIntegralInterface.boundaryFormIntegral =
      D.measureResolved.measureLocalization.boundaryMeasureIntegral :=
  rfl

/-- Compact-support-facing M8 proves the canonical measure-level statement. -/
theorem canonical_stokes
    [IsManifold I 1 M]
    (D : M8CompactSupportStokesInput I omega BoundaryPiece) :
    D.canonicalIntegralInterface.stokesStatement := by
  simpa [canonicalIntegralInterface,
    M8GlobalStokesInput.canonicalIntegralInterface,
    M8MeasureLocalizationData.canonicalIntegralInterface,
    CanonicalIntegralInterface.stokesStatement] using D.stokes

end M8CompactSupportStokesInput

end M8Projections

end Stokes

end
