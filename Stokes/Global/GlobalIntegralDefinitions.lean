import Stokes.Global.NaturalInputData

/-!
# Global integral interface

This file adds a small naming layer for the two global real numbers carried by
the current global Stokes packages.

The record below is intentionally only an interface: it does not define a
manifold integral, a boundary measure, or an integration theory.  It lets later
files pass around the represented bulk and boundary values as one replaceable
object while the existing reconstruction records continue to expose the exact
finite-sum fields they already use.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section Interface

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Lightweight interface for the represented global bulk and boundary values.

This is deliberately a replaceable label for the current `Real` values, not a
definition of the eventual analytic manifold integrals.
-/
structure GlobalIntegralInterface {k : Nat}
    (I : ModelWithCorners Real E H) (omega : ManifoldForm I M k) where
  /-- The represented global bulk-side value. -/
  globalBulkIntegral : Real
  /-- The represented global boundary-side value. -/
  globalBoundaryIntegral : Real

namespace GlobalIntegralInterface

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {omega : ManifoldForm I M k}

/-- Build the interface from explicitly named represented values. -/
def ofValues (globalBulkIntegral globalBoundaryIntegral : Real) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := globalBulkIntegral
  globalBoundaryIntegral := globalBoundaryIntegral

/-- The interface-level Stokes equality claim. -/
def stokesStatement (J : GlobalIntegralInterface I omega) : Prop :=
  J.globalBulkIntegral = J.globalBoundaryIntegral

@[simp]
theorem ofValues_globalBulkIntegral
    (globalBulkIntegral globalBoundaryIntegral : Real) :
    (ofValues (I := I) (omega := omega)
      globalBulkIntegral globalBoundaryIntegral).globalBulkIntegral =
        globalBulkIntegral :=
  rfl

@[simp]
theorem ofValues_globalBoundaryIntegral
    (globalBulkIntegral globalBoundaryIntegral : Real) :
    (ofValues (I := I) (omega := omega)
      globalBulkIntegral globalBoundaryIntegral).globalBoundaryIntegral =
        globalBoundaryIntegral :=
  rfl

end GlobalIntegralInterface

end Interface

section ReconstructionProjections

universe u v w c i b p

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BulkIntegralReconstructionData

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {omega : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/--
Build bulk reconstruction data while sourcing the bulk value from the global
integral interface.
-/
def ofGlobalIntegralInterface
    (integrals : GlobalIntegralInterface I omega)
    (activeCharts : Finset Chart)
    (interiorPieces : Chart -> Finset InteriorPiece)
    (boundaryPieces : Chart -> Finset BoundaryPiece)
    (interiorBulkTerm : Chart -> InteriorPiece -> Real)
    (boundaryBulkTerm : Chart -> BoundaryPiece -> Real)
    (globalBulkIntegral_eq_localBulkSum :
      integrals.globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q) :
    BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  boundaryPieces := boundaryPieces
  interiorBulkTerm := interiorBulkTerm
  boundaryBulkTerm := boundaryBulkTerm
  globalBulkIntegral := integrals.globalBulkIntegral
  globalBulkIntegral_eq_localBulkSum := globalBulkIntegral_eq_localBulkSum

/--
Extract the global integral interface from separated bulk reconstruction and
the boundary fields that complete it.
-/
def globalIntegralInterface
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := B.globalBoundaryIntegral

namespace BoundaryPartitionFields

/--
Build the boundary fields that complete bulk reconstruction while sourcing the
represented boundary value from the global integral interface.
-/
def ofGlobalIntegralInterface
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (integrals : GlobalIntegralInterface I omega)
    (boundaryPartitionTerm : Chart -> BoundaryPiece -> Real)
    (globalBoundaryIntegral_eq_boundaryPartitionSum :
      integrals.globalBoundaryIntegral =
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q => boundaryPartitionTerm x q) :
    BoundaryPartitionFields D where
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBoundaryIntegral := integrals.globalBoundaryIntegral
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    globalBoundaryIntegral_eq_boundaryPartitionSum

@[simp]
theorem ofGlobalIntegralInterface_globalBoundaryIntegral
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (integrals : GlobalIntegralInterface I omega)
    (boundaryPartitionTerm : Chart -> BoundaryPiece -> Real)
    (globalBoundaryIntegral_eq_boundaryPartitionSum :
      integrals.globalBoundaryIntegral =
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q => boundaryPartitionTerm x q) :
    (ofGlobalIntegralInterface D integrals boundaryPartitionTerm
      globalBoundaryIntegral_eq_boundaryPartitionSum).globalBoundaryIntegral =
        integrals.globalBoundaryIntegral :=
  rfl

@[simp]
theorem ofGlobalIntegralInterface_boundaryPartitionTerm
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (integrals : GlobalIntegralInterface I omega)
    (boundaryPartitionTerm : Chart -> BoundaryPiece -> Real)
    (globalBoundaryIntegral_eq_boundaryPartitionSum :
      integrals.globalBoundaryIntegral =
        Finset.sum D.activeCharts fun x =>
          Finset.sum (D.boundaryPieces x) fun q => boundaryPartitionTerm x q) :
    (ofGlobalIntegralInterface D integrals boundaryPartitionTerm
      globalBoundaryIntegral_eq_boundaryPartitionSum).boundaryPartitionTerm =
        boundaryPartitionTerm :=
  rfl

end BoundaryPartitionFields

@[simp]
theorem ofGlobalIntegralInterface_globalBulkIntegral
    (integrals : GlobalIntegralInterface I omega)
    (activeCharts : Finset Chart)
    (interiorPieces : Chart -> Finset InteriorPiece)
    (boundaryPieces : Chart -> Finset BoundaryPiece)
    (interiorBulkTerm : Chart -> InteriorPiece -> Real)
    (boundaryBulkTerm : Chart -> BoundaryPiece -> Real)
    (globalBulkIntegral_eq_localBulkSum :
      integrals.globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q) :
    (ofGlobalIntegralInterface (I := I) (omega := omega) integrals
      activeCharts interiorPieces boundaryPieces interiorBulkTerm
      boundaryBulkTerm globalBulkIntegral_eq_localBulkSum).globalBulkIntegral =
        integrals.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    (D.globalIntegralInterface B).globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (D : BulkIntegralReconstructionData I omega Chart InteriorPiece BoundaryPiece)
    (B : BoundaryPartitionFields D) :
    (D.globalIntegralInterface B).globalBoundaryIntegral =
      B.globalBoundaryIntegral :=
  rfl

end BulkIntegralReconstructionData

namespace BoundaryIntegralReconstructionData

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {omega : ManifoldForm I M k}
variable {Chart : Type c} {Piece : Type p}

/--
Build boundary reconstruction data while sourcing the boundary value from the
global integral interface.
-/
def ofGlobalIntegralInterface
    (integrals : GlobalIntegralInterface I omega)
    (activeCharts : Finset Chart)
    (selectedBoundaryPieces : Chart -> Finset Piece)
    (selectedBoundaryTerm : Chart -> Piece -> Real)
    (manifoldBoundaryIntegral_eq_selectedBoundarySum :
      integrals.globalBoundaryIntegral =
        selectedBoundaryPieceSum activeCharts selectedBoundaryPieces
          selectedBoundaryTerm) :
    BoundaryIntegralReconstructionData activeCharts selectedBoundaryPieces
      selectedBoundaryTerm integrals.globalBoundaryIntegral where
  manifoldBoundaryIntegral_eq_selectedBoundarySum :=
    manifoldBoundaryIntegral_eq_selectedBoundarySum

@[simp]
theorem ofGlobalIntegralInterface_manifoldBoundaryIntegral
    (integrals : GlobalIntegralInterface I omega)
    (activeCharts : Finset Chart)
    (selectedBoundaryPieces : Chart -> Finset Piece)
    (selectedBoundaryTerm : Chart -> Piece -> Real)
    (manifoldBoundaryIntegral_eq_selectedBoundarySum :
      integrals.globalBoundaryIntegral =
        selectedBoundaryPieceSum activeCharts selectedBoundaryPieces
          selectedBoundaryTerm) :
    (ofGlobalIntegralInterface (I := I) (omega := omega) integrals
        activeCharts selectedBoundaryPieces selectedBoundaryTerm
        manifoldBoundaryIntegral_eq_selectedBoundarySum
      ).manifoldBoundaryIntegral_eq_selectedBoundarySum =
      manifoldBoundaryIntegral_eq_selectedBoundarySum :=
  rfl

end BoundaryIntegralReconstructionData

namespace PartitionReconstructionData

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {omega : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/--
Build partition reconstruction data while sourcing both represented global
values from the global integral interface.
-/
def ofGlobalIntegralInterface
    (integrals : GlobalIntegralInterface I omega)
    (activeCharts : Finset Chart)
    (interiorPieces : Chart -> Finset InteriorPiece)
    (boundaryPieces : Chart -> Finset BoundaryPiece)
    (interiorBulkTerm : Chart -> InteriorPiece -> Real)
    (boundaryBulkTerm boundaryPartitionTerm : Chart -> BoundaryPiece -> Real)
    (globalBulkIntegral_eq_localBulkSum :
      integrals.globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q)
    (globalBoundaryIntegral_eq_boundaryPartitionSum :
      integrals.globalBoundaryIntegral =
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q) :
    PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  boundaryPieces := boundaryPieces
  interiorBulkTerm := interiorBulkTerm
  boundaryBulkTerm := boundaryBulkTerm
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBulkIntegral := integrals.globalBulkIntegral
  globalBoundaryIntegral := integrals.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Extract the represented global integral interface from reconstruction data. -/
def globalIntegralInterface
    (R : PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := R.globalBulkIntegral
  globalBoundaryIntegral := R.globalBoundaryIntegral

@[simp]
theorem ofGlobalIntegralInterface_globalBulkIntegral
    (integrals : GlobalIntegralInterface I omega)
    (activeCharts : Finset Chart)
    (interiorPieces : Chart -> Finset InteriorPiece)
    (boundaryPieces : Chart -> Finset BoundaryPiece)
    (interiorBulkTerm : Chart -> InteriorPiece -> Real)
    (boundaryBulkTerm boundaryPartitionTerm : Chart -> BoundaryPiece -> Real)
    (globalBulkIntegral_eq_localBulkSum :
      integrals.globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q)
    (globalBoundaryIntegral_eq_boundaryPartitionSum :
      integrals.globalBoundaryIntegral =
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q) :
    (ofGlobalIntegralInterface (I := I) (omega := omega) integrals
      activeCharts interiorPieces boundaryPieces interiorBulkTerm
      boundaryBulkTerm boundaryPartitionTerm globalBulkIntegral_eq_localBulkSum
      globalBoundaryIntegral_eq_boundaryPartitionSum).globalBulkIntegral =
        integrals.globalBulkIntegral :=
  rfl

@[simp]
theorem ofGlobalIntegralInterface_globalBoundaryIntegral
    (integrals : GlobalIntegralInterface I omega)
    (activeCharts : Finset Chart)
    (interiorPieces : Chart -> Finset InteriorPiece)
    (boundaryPieces : Chart -> Finset BoundaryPiece)
    (interiorBulkTerm : Chart -> InteriorPiece -> Real)
    (boundaryBulkTerm boundaryPartitionTerm : Chart -> BoundaryPiece -> Real)
    (globalBulkIntegral_eq_localBulkSum :
      integrals.globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q)
    (globalBoundaryIntegral_eq_boundaryPartitionSum :
      integrals.globalBoundaryIntegral =
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q) :
    (ofGlobalIntegralInterface (I := I) (omega := omega) integrals
      activeCharts interiorPieces boundaryPieces interiorBulkTerm
      boundaryBulkTerm boundaryPartitionTerm globalBulkIntegral_eq_localBulkSum
      globalBoundaryIntegral_eq_boundaryPartitionSum).globalBoundaryIntegral =
        integrals.globalBoundaryIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (R : PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    R.globalIntegralInterface.globalBulkIntegral = R.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (R : PartitionReconstructionData I omega Chart InteriorPiece BoundaryPiece) :
    R.globalIntegralInterface.globalBoundaryIntegral =
      R.globalBoundaryIntegral :=
  rfl

end PartitionReconstructionData

end ReconstructionProjections

section FinalPackageProjections

universe u w c i b p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

namespace GlobalStokesReconstructionFields

/--
Build final-shape reconstruction fields while sourcing both represented global
values from the global integral interface.
-/
def ofGlobalIntegralInterface
    (integrals : GlobalIntegralInterface I omega)
    (activeCharts : Finset Chart)
    (interiorPieces : Chart -> Finset InteriorPiece)
    (boundaryPieces : Chart -> Finset BoundaryPiece)
    (interiorBulkTerm : Chart -> InteriorPiece -> Real)
    (boundaryBulkTerm boundaryPartitionTerm : Chart -> BoundaryPiece -> Real)
    (globalBulkIntegral_eq_localBulkSum :
      integrals.globalBulkIntegral =
        (Finset.sum activeCharts fun x =>
            Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
          Finset.sum activeCharts fun x =>
            Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q)
    (globalBoundaryIntegral_eq_boundaryPartitionSum :
      integrals.globalBoundaryIntegral =
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q) :
    GlobalStokesReconstructionFields I omega Chart InteriorPiece BoundaryPiece where
  activeCharts := activeCharts
  interiorPieces := interiorPieces
  boundaryPieces := boundaryPieces
  interiorBulkTerm := interiorBulkTerm
  boundaryBulkTerm := boundaryBulkTerm
  boundaryPartitionTerm := boundaryPartitionTerm
  globalBulkIntegral := integrals.globalBulkIntegral
  globalBoundaryIntegral := integrals.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Extract the represented global integral interface from reconstruction fields. -/
def globalIntegralInterface
    (D : GlobalStokesReconstructionFields I omega Chart InteriorPiece BoundaryPiece) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (D : GlobalStokesReconstructionFields I omega Chart InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (D : GlobalStokesReconstructionFields I omega Chart InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

end GlobalStokesReconstructionFields

namespace GlobalStokesData

/-- Extract the represented global integral interface from final global data. -/
def globalIntegralInterface
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

/-- The final global package proves the interface-level Stokes statement. -/
theorem globalIntegralInterface_stokesStatement
    (D : GlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.stokesStatement := by
  exact D.stokes

end GlobalStokesData

namespace MixedGlobalStokesData

/-- Extract the represented global integral interface from mixed constructor data. -/
def globalIntegralInterface
    (D : MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    GlobalIntegralInterface I omega :=
  D.reconstruction.globalIntegralInterface

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (D : MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBulkIntegral =
      D.reconstruction.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (D : MixedGlobalStokesData I omega Chart InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBoundaryIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  rfl

end MixedGlobalStokesData

namespace SelectedMixedGlobalInput

/-- Extract the represented global integral interface from selected mixed input. -/
def globalIntegralInterface
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    GlobalIntegralInterface I omega :=
  D.reconstruction.globalIntegralInterface

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBulkIntegral =
      D.reconstruction.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (D : SelectedMixedGlobalInput I omega InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBoundaryIntegral =
      D.reconstruction.globalBoundaryIntegral :=
  rfl

end SelectedMixedGlobalInput

namespace NaturalGlobalStokesInput

/--
Stable top-level name for the represented global bulk integral carried by a
natural input.

The field currently lives inside `bulkReconstruction`; this projection gives
later M8-facing statements the same surface shape as the existing
`globalBoundaryIntegral` field.
-/
abbrev globalBulkIntegral
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) : Real :=
  D.bulkReconstruction.globalBulkIntegral

/-- Interface-level represented-integral Stokes statement for natural input. -/
def representedStokesStatement
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) : Prop :=
  D.globalBulkIntegral = D.globalBoundaryIntegral

/-- Extract the represented global integral interface from natural global input. -/
def globalIntegralInterface
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) :
    GlobalIntegralInterface I omega :=
  GlobalIntegralInterface.ofValues D.globalBulkIntegral D.globalBoundaryIntegral

@[simp]
theorem globalBulkIntegral_eq
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral = D.bulkReconstruction.globalBulkIntegral :=
  rfl

@[simp]
theorem representedStokesStatement_iff
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) :
    D.representedStokesStatement ↔
      D.globalBulkIntegral = D.globalBoundaryIntegral :=
  Iff.rfl

@[simp]
theorem globalIntegralInterface_eq
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface =
      GlobalIntegralInterface.ofValues
        D.globalBulkIntegral D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBulkIntegral =
      D.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_stokesStatement
    (D : NaturalGlobalStokesInput I omega InteriorPiece BoundaryPiece) :
    D.globalIntegralInterface.stokesStatement ↔
      D.representedStokesStatement :=
  Iff.rfl

end NaturalGlobalStokesInput

namespace ProjectLocalGlobalStokesData

variable {Piece : Type p}

/-- Extract the represented global integral interface from project-local data. -/
def globalIntegralInterface
    (D : ProjectLocalGlobalStokesData I omega Chart Piece) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (D : ProjectLocalGlobalStokesData I omega Chart Piece) :
    D.globalIntegralInterface.globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (D : ProjectLocalGlobalStokesData I omega Chart Piece) :
    D.globalIntegralInterface.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

end ProjectLocalGlobalStokesData

namespace ProjectLocalConstructorData

variable {Piece : Type p}

/-- Extract the represented global integral interface from project-local input. -/
def globalIntegralInterface
    (D : ProjectLocalConstructorData I omega Chart Piece) :
    GlobalIntegralInterface I omega where
  globalBulkIntegral := D.globalBulkIntegral
  globalBoundaryIntegral := D.globalBoundaryIntegral

@[simp]
theorem globalIntegralInterface_globalBulkIntegral
    (D : ProjectLocalConstructorData I omega Chart Piece) :
    D.globalIntegralInterface.globalBulkIntegral = D.globalBulkIntegral :=
  rfl

@[simp]
theorem globalIntegralInterface_globalBoundaryIntegral
    (D : ProjectLocalConstructorData I omega Chart Piece) :
    D.globalIntegralInterface.globalBoundaryIntegral =
      D.globalBoundaryIntegral :=
  rfl

end ProjectLocalConstructorData

end FinalPackageProjections

end Stokes

end
