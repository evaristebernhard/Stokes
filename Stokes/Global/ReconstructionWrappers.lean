import Stokes.Global.Reconstruction

/-!
# Reconstruction-field wrappers

This file contains small adapters for the global reconstruction layer.

The core wrappers are intentionally phrased over abstract fields from
`PartitionReconstructionData`, so downstream files can fill the final
`GlobalStokesData` reconstruction fields without depending on a particular
partition-of-unity construction.  When a concrete sum-one theorem is available
from the finite-active partition layer, it can be passed to
`LocalizedFormReconstructionFields.ofCoeffSumEqOneOn`.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedFormWrappers

universe u v w c

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

/--
Abstract localized-form reconstruction data.

The field `localizedFormSum_eq_self_on` is the only fact needed by later
integration wrappers.  Concrete partition-of-unity files may construct this
package from their own sum-one theorem, while this file stays independent of
those less stable APIs.
-/
structure LocalizedFormReconstructionFields
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k)
    (Chart : Type c) where
  /-- Finite partition/chart labels used in the localized sum. -/
  activeCharts : Finset Chart
  /-- Scalar coefficients for the localized forms. -/
  coefficient : Chart → M → Real
  /-- Set on which the finite localized sum reconstructs the original form. -/
  supportSet : Set M
  /-- Pointwise reconstruction of the localized finite sum on `supportSet`. -/
  localizedFormSum_eq_self_on :
    ∀ x ∈ supportSet, localizedFormSum I activeCharts coefficient ω x = ω x

namespace LocalizedFormReconstructionFields

variable {Chart : Type c} {ω : ManifoldForm I M k}

/-- The reconstruction field exposed as a theorem. -/
theorem localizedFormSum_eq_self_on'
    (D : LocalizedFormReconstructionFields I ω Chart) :
    ∀ x ∈ D.supportSet,
      localizedFormSum I D.activeCharts D.coefficient ω x = ω x :=
  D.localizedFormSum_eq_self_on

/--
Build localized-form reconstruction from an abstract pointwise coefficient
sum-one theorem.

If `Stokes.Global.PartitionSumOne` is available, its `coeff_sum_eq_one_on`
theorems have exactly the intended role for `hsum`.
-/
def ofCoeffSumEqOneOn
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (K : Set M)
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1) :
    LocalizedFormReconstructionFields I ω Chart where
  activeCharts := active
  coefficient := coefficient
  supportSet := K
  localizedFormSum_eq_self_on :=
    localizedFormSum_eqOn_of_coeff_sum_eq_one_on active coefficient ω hsum

/-- Build localized-form reconstruction from an already proved pointwise equality. -/
def ofEqOn
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (K : Set M)
    (hlocalized :
      ∀ x ∈ K, localizedFormSum I active coefficient ω x = ω x) :
    LocalizedFormReconstructionFields I ω Chart where
  activeCharts := active
  coefficient := coefficient
  supportSet := K
  localizedFormSum_eq_self_on := hlocalized

@[simp]
theorem ofCoeffSumEqOneOn_activeCharts
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (K : Set M)
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1) :
    (ofCoeffSumEqOneOn (I := I) (ω := ω) active coefficient K hsum).activeCharts =
      active :=
  rfl

@[simp]
theorem ofCoeffSumEqOneOn_coefficient
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (K : Set M)
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1) :
    (ofCoeffSumEqOneOn (I := I) (ω := ω) active coefficient K hsum).coefficient =
      coefficient :=
  rfl

@[simp]
theorem ofCoeffSumEqOneOn_supportSet
    (active : Finset Chart) (coefficient : Chart → M → Real)
    (K : Set M)
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => coefficient i x) = 1) :
    (ofCoeffSumEqOneOn (I := I) (ω := ω) active coefficient K hsum).supportSet =
      K :=
  rfl

end LocalizedFormReconstructionFields

end LocalizedFormWrappers

section GlobalReconstructionWrappers

universe u w c i b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/--
The reconstruction-only fields of `GlobalStokesData`.

This is a thin record with the same bulk and boundary reconstruction equalities
as the final theorem package, but without local Stokes, cancellation, or
chart-change data.
-/
structure GlobalStokesReconstructionFields
    (I : ModelWithCorners Real (Fin (n + 1) → Real) H)
    (ω : ManifoldForm I M n)
    (Chart : Type c) (InteriorPiece : Type i) (BoundaryPiece : Type b) where
  /-- Finite chart labels active in the chosen partition/cover. -/
  activeCharts : Finset Chart
  /-- Localized interior pieces assigned to an active chart. -/
  interiorPieces : Chart → Finset InteriorPiece
  /-- Localized boundary-chart pieces assigned to an active chart. -/
  boundaryPieces : Chart → Finset BoundaryPiece
  /-- Bulk contribution of an interior local piece. -/
  interiorBulkTerm : Chart → InteriorPiece → Real
  /-- Bulk contribution of a boundary-chart local piece. -/
  boundaryBulkTerm : Chart → BoundaryPiece → Real
  /-- Boundary contribution after chart changes and partition reconstruction. -/
  boundaryPartitionTerm : Chart → BoundaryPiece → Real
  /-- The global bulk integral represented by this reconstruction package. -/
  globalBulkIntegral : Real
  /-- The global boundary integral represented by this reconstruction package. -/
  globalBoundaryIntegral : Real
  /-- Reconstruction of the global bulk integral from finitely many local pieces. -/
  globalBulkIntegral_eq_localBulkSum :
    globalBulkIntegral =
      (Finset.sum activeCharts fun x =>
          Finset.sum (interiorPieces x) fun q => interiorBulkTerm x q) +
        Finset.sum activeCharts fun x =>
          Finset.sum (boundaryPieces x) fun q => boundaryBulkTerm x q
  /-- Reconstruction of the global boundary integral from the boundary partition. -/
  globalBoundaryIntegral_eq_boundaryPartitionSum :
    globalBoundaryIntegral =
      Finset.sum activeCharts fun x =>
        Finset.sum (boundaryPieces x) fun q => boundaryPartitionTerm x q

namespace GlobalStokesReconstructionFields

/-- Sum of all interior bulk terms in a reconstruction-field package. -/
def interiorBulkSum
    (D : GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece) :
    Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.interiorPieces x) fun q => D.interiorBulkTerm x q

/-- Sum of all boundary-chart bulk terms in a reconstruction-field package. -/
def boundaryBulkSum
    (D : GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece) :
    Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.boundaryBulkTerm x q

/-- Total local bulk side recorded in a reconstruction-field package. -/
def localBulkSum
    (D : GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece) :
    Real :=
  interiorBulkSum D + boundaryBulkSum D

/-- Sum of boundary partition terms in a reconstruction-field package. -/
def boundaryPartitionSum
    (D : GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece) :
    Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => D.boundaryPartitionTerm x q

/-- Wrapper form of the bulk reconstruction field using package-local sum names. -/
theorem globalBulkIntegral_eq_localBulkSum'
    (D : GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece) :
    D.globalBulkIntegral = localBulkSum D := by
  rw [localBulkSum, interiorBulkSum, boundaryBulkSum]
  exact D.globalBulkIntegral_eq_localBulkSum

/-- Wrapper form of the boundary reconstruction field using package-local sum names. -/
theorem globalBoundaryIntegral_eq_boundaryPartitionSum'
    (D : GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece) :
    D.globalBoundaryIntegral = boundaryPartitionSum D := by
  rw [boundaryPartitionSum]
  exact D.globalBoundaryIntegral_eq_boundaryPartitionSum

/-- Convert the existing partition reconstruction package to reconstruction fields. -/
def ofPartitionReconstructionData
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece where
  activeCharts := R.activeCharts
  interiorPieces := R.interiorPieces
  boundaryPieces := R.boundaryPieces
  interiorBulkTerm := R.interiorBulkTerm
  boundaryBulkTerm := R.boundaryBulkTerm
  boundaryPartitionTerm := R.boundaryPartitionTerm
  globalBulkIntegral := R.globalBulkIntegral
  globalBoundaryIntegral := R.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum := R.globalBulkIntegral_eq_localBulkSum
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    R.globalBoundaryIntegral_eq_boundaryPartitionSum

end GlobalStokesReconstructionFields

namespace PartitionReconstructionData

/--
Package only the reconstruction fields of a `PartitionReconstructionData` in
the shape used by `GlobalStokesData`.
-/
def toGlobalStokesReconstructionFields
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    GlobalStokesReconstructionFields I ω Chart InteriorPiece BoundaryPiece :=
  GlobalStokesReconstructionFields.ofPartitionReconstructionData R

@[simp]
theorem toGlobalStokesReconstructionFields_activeCharts
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    R.toGlobalStokesReconstructionFields.activeCharts = R.activeCharts :=
  rfl

@[simp]
theorem toGlobalStokesReconstructionFields_globalBulkIntegral
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    R.toGlobalStokesReconstructionFields.globalBulkIntegral =
      R.globalBulkIntegral :=
  rfl

@[simp]
theorem toGlobalStokesReconstructionFields_globalBoundaryIntegral
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    R.toGlobalStokesReconstructionFields.globalBoundaryIntegral =
      R.globalBoundaryIntegral :=
  rfl

/--
Bulk reconstruction theorem in exactly the shape of the corresponding
`GlobalStokesData` field.
-/
theorem globalBulkIntegral_eq_globalStokes_localBulkSum
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    R.globalBulkIntegral =
      (Finset.sum R.activeCharts fun x =>
          Finset.sum (R.interiorPieces x) fun q => R.interiorBulkTerm x q) +
        Finset.sum R.activeCharts fun x =>
          Finset.sum (R.boundaryPieces x) fun q => R.boundaryBulkTerm x q :=
  R.globalBulkIntegral_eq_localBulkSum

/--
Boundary reconstruction theorem in exactly the shape of the corresponding
`GlobalStokesData` field.
-/
theorem globalBoundaryIntegral_eq_globalStokes_boundaryPartitionSum
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    R.globalBoundaryIntegral =
      Finset.sum R.activeCharts fun x =>
        Finset.sum (R.boundaryPieces x) fun q => R.boundaryPartitionTerm x q :=
  R.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
The non-reconstruction inputs still needed after `PartitionReconstructionData`
has supplied the global bulk and boundary reconstruction fields.
-/
structure GlobalStokesRemainingFields
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) where
  /-- Artificial boundary-side contribution of an interior local piece. -/
  interiorBoundaryTerm : Chart → InteriorPiece → Real
  /-- Boundary-chart contribution before global chart-change identification. -/
  boundaryBoundaryTerm : Chart → BoundaryPiece → Real
  /-- Local Stokes on every recorded interior piece. -/
  interiorLocalStokes :
    ∀ x, x ∈ R.activeCharts →
      ∀ q, q ∈ R.interiorPieces x →
        R.interiorBulkTerm x q = interiorBoundaryTerm x q
  /-- Local Stokes on every recorded boundary-chart piece. -/
  boundaryLocalStokes :
    ∀ x, x ∈ R.activeCharts →
      ∀ q, q ∈ R.boundaryPieces x →
        R.boundaryBulkTerm x q = boundaryBoundaryTerm x q
  /-- Cancellation of artificial interior-chart boundary faces. -/
  interiorBoundaryCancellation :
    (Finset.sum R.activeCharts fun x =>
      Finset.sum (R.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0
  /-- Boundary chart-change compatibility with the reconstructed partition term. -/
  chartChangeCancellation :
    (Finset.sum R.activeCharts fun x =>
        Finset.sum (R.boundaryPieces x) fun q => boundaryBoundaryTerm x q) =
      Finset.sum R.activeCharts fun x =>
        Finset.sum (R.boundaryPieces x) fun q => R.boundaryPartitionTerm x q

/--
Convert partition reconstruction data plus the remaining local fields to the
final `GlobalStokesData`, automatically filling both reconstruction fields.
-/
def toGlobalStokesDataWith
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (A : GlobalStokesRemainingFields R) :
    GlobalStokesData I ω Chart InteriorPiece BoundaryPiece :=
  R.toGlobalStokesData
    A.interiorBoundaryTerm
    A.boundaryBoundaryTerm
    A.interiorLocalStokes
    A.boundaryLocalStokes
    A.interiorBoundaryCancellation
    A.chartChangeCancellation

@[simp]
theorem toGlobalStokesDataWith_globalBulkIntegral
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (A : GlobalStokesRemainingFields R) :
    (R.toGlobalStokesDataWith A).globalBulkIntegral = R.globalBulkIntegral :=
  rfl

@[simp]
theorem toGlobalStokesDataWith_globalBoundaryIntegral
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (A : GlobalStokesRemainingFields R) :
    (R.toGlobalStokesDataWith A).globalBoundaryIntegral =
      R.globalBoundaryIntegral :=
  rfl

/--
The automatically constructed `GlobalStokesData` has its bulk reconstruction
field filled by the source `PartitionReconstructionData`.
-/
theorem toGlobalStokesDataWith_globalBulkIntegral_eq_localBulkSum
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (A : GlobalStokesRemainingFields R) :
    (R.toGlobalStokesDataWith A).globalBulkIntegral =
      GlobalStokesData.localBulkSum (R.toGlobalStokesDataWith A) := by
  rw [GlobalStokesData.localBulkSum, GlobalStokesData.interiorBulkSum,
    GlobalStokesData.boundaryBulkSum]
  exact R.globalBulkIntegral_eq_localBulkSum

/--
The automatically constructed `GlobalStokesData` has its boundary reconstruction
field filled by the source `PartitionReconstructionData`.
-/
theorem toGlobalStokesDataWith_globalBoundaryIntegral_eq_boundaryPartitionSum
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece)
    (A : GlobalStokesRemainingFields R) :
    (R.toGlobalStokesDataWith A).globalBoundaryIntegral =
      GlobalStokesData.boundaryPartitionSum (R.toGlobalStokesDataWith A) := by
  rw [GlobalStokesData.boundaryPartitionSum]
  exact R.globalBoundaryIntegral_eq_boundaryPartitionSum

end PartitionReconstructionData

end GlobalReconstructionWrappers

end Stokes

end
