import Stokes.Global.Localization
import Stokes.Global.Partition
import Stokes.Global.Theorem

/-!
# Partition reconstruction packages

This file is the package layer between partition-of-unity localization and the
final `GlobalStokesData` bookkeeping theorem.  It contains only algebraic and
function-extensional reconstruction statements; analytic support, local Stokes,
boundary cancellation, and chart-change facts remain explicit inputs.
-/

noncomputable section

open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedPointwise

universe u v w c

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

/-- Finite sum of the partition-localized forms indexed by `active`. -/
def localizedFormSum {Chart : Type c} (I : ModelWithCorners Real E H)
    (active : Finset Chart) (ρ : Chart → M → Real)
    (ω : ManifoldForm I M k) : ManifoldForm I M k :=
  Finset.sum active fun i => ManifoldForm.localizedForm I (ρ i) ω

@[simp]
theorem localizedFormSum_apply {Chart : Type c}
    (active : Finset Chart) (ρ : Chart → M → Real)
    (ω : ManifoldForm I M k) (x : M) :
    localizedFormSum I active ρ ω x =
      Finset.sum active fun i => ManifoldForm.localizedForm I (ρ i) ω x := by
  simp [localizedFormSum]

/--
At one point, summing the localized forms is scalar multiplication by the sum of
the coefficients at that point.
-/
theorem localizedFormSum_apply_eq_coeff_sum_smul {Chart : Type c}
    (active : Finset Chart) (ρ : Chart → M → Real)
    (ω : ManifoldForm I M k) (x : M) :
    localizedFormSum I active ρ ω x =
      (Finset.sum active fun i => ρ i x) • ω x := by
  calc
    localizedFormSum I active ρ ω x =
        Finset.sum active fun i => (ρ i x) • ω x := by
      simp [localizedFormSum, ManifoldForm.localizedForm]
    _ = (Finset.sum active fun i => ρ i x) • ω x := by
      rw [← Finset.sum_smul]

/--
Pointwise partition reconstruction for localized manifold forms.

This is the raw algebraic statement used when a finite active subfamily has
coefficient sum `1` at the chosen point.
-/
theorem localizedFormSum_apply_eq_self_of_coeff_sum_eq_one {Chart : Type c}
    (active : Finset Chart) (ρ : Chart → M → Real)
    (ω : ManifoldForm I M k) {x : M}
    (hsum : (Finset.sum active fun i => ρ i x) = 1) :
    localizedFormSum I active ρ ω x = ω x := by
  rw [localizedFormSum_apply_eq_coeff_sum_smul]
  simp [hsum]

/--
Pointwise reconstruction on a controlled set `K`, assuming the active
coefficients sum to `1` on `K`.
-/
theorem localizedFormSum_apply_eq_self_on {Chart : Type c}
    (active : Finset Chart) (ρ : Chart → M → Real)
    (ω : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => ρ i x) = 1)
    {x : M} (hx : x ∈ K) :
    localizedFormSum I active ρ ω x = ω x :=
  localizedFormSum_apply_eq_self_of_coeff_sum_eq_one active ρ ω (hsum x hx)

/--
Set-wise reconstruction of the localized finite sum on `K`.

This is written with an explicit dependent pointwise predicate rather than
`Set.EqOn`, since the target fiber of a `ManifoldForm` depends on the point.
-/
theorem localizedFormSum_eqOn_of_coeff_sum_eq_one_on {Chart : Type c}
    (active : Finset Chart) (ρ : Chart → M → Real)
    (ω : ManifoldForm I M k) {K : Set M}
    (hsum : ∀ x ∈ K, (Finset.sum active fun i => ρ i x) = 1) :
    ∀ x ∈ K, localizedFormSum I active ρ ω x = ω x := by
  intro x hx
  exact localizedFormSum_apply_eq_self_on active ρ ω hsum hx

/--
Function-extensional reconstruction when the active coefficients sum to `1`
everywhere.
-/
theorem localizedFormSum_eq_self_of_coeff_sum_eq_one {Chart : Type c}
    (active : Finset Chart) (ρ : Chart → M → Real)
    (ω : ManifoldForm I M k)
    (hsum : ∀ x : M, (Finset.sum active fun i => ρ i x) = 1) :
    localizedFormSum I active ρ ω = ω := by
  funext x
  exact localizedFormSum_apply_eq_self_of_coeff_sum_eq_one active ρ ω (hsum x)

end LocalizedPointwise

section ReconstructionPackage

universe u v w c i b

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Partition reconstruction data for the final global package.

This structure deliberately records only the two reconstruction equalities:
global bulk as the sum of localized bulk pieces, and global boundary as the
boundary partition sum.  Local Stokes, artificial-face cancellation, and
chart-change compatibility are supplied separately when converting to
`GlobalStokesData`.
-/
structure PartitionReconstructionData {k : Nat}
    (I : ModelWithCorners Real E H) (ω : ManifoldForm I M k)
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

namespace PartitionReconstructionData

variable {k : Nat} {I : ModelWithCorners Real E H}
variable {ω : ManifoldForm I M k}
variable {Chart : Type c} {InteriorPiece : Type i} {BoundaryPiece : Type b}

/-- Sum of all interior bulk terms in a reconstruction package. -/
def interiorBulkSum
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum R.activeCharts fun x =>
    Finset.sum (R.interiorPieces x) fun q => R.interiorBulkTerm x q

/-- Sum of all boundary-chart bulk terms in a reconstruction package. -/
def boundaryBulkSum
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum R.activeCharts fun x =>
    Finset.sum (R.boundaryPieces x) fun q => R.boundaryBulkTerm x q

/-- Total local bulk side recorded in a reconstruction package. -/
def localBulkSum
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  interiorBulkSum R + boundaryBulkSum R

/-- Sum of boundary partition terms in a reconstruction package. -/
def boundaryPartitionSum
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) : Real :=
  Finset.sum R.activeCharts fun x =>
    Finset.sum (R.boundaryPieces x) fun q => R.boundaryPartitionTerm x q

/-- Wrapper form of the bulk reconstruction field, using the package-local sum name. -/
theorem globalBulkIntegral_eq_localBulkSum'
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    R.globalBulkIntegral = localBulkSum R := by
  rw [localBulkSum, interiorBulkSum, boundaryBulkSum]
  exact R.globalBulkIntegral_eq_localBulkSum

/-- Wrapper form of the boundary reconstruction field, using the package-local sum name. -/
theorem globalBoundaryIntegral_eq_boundaryPartitionSum'
    (R : PartitionReconstructionData I ω Chart InteriorPiece BoundaryPiece) :
    R.globalBoundaryIntegral = boundaryPartitionSum R := by
  rw [boundaryPartitionSum]
  exact R.globalBoundaryIntegral_eq_boundaryPartitionSum

section GlobalStokesWrapper

variable {n : Nat}
variable {I' : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω' : ManifoldForm I' M n}

/--
Bulk reconstruction theorem in exactly the shape needed for
`GlobalStokesData.globalBulkIntegral_eq_localBulkSum`.
-/
theorem toGlobalStokesData_globalBulkIntegral_eq_localBulkSum
    (R : PartitionReconstructionData I' ω' Chart InteriorPiece BoundaryPiece) :
    R.globalBulkIntegral =
      (Finset.sum R.activeCharts fun x =>
          Finset.sum (R.interiorPieces x) fun q => R.interiorBulkTerm x q) +
        Finset.sum R.activeCharts fun x =>
          Finset.sum (R.boundaryPieces x) fun q => R.boundaryBulkTerm x q :=
  R.globalBulkIntegral_eq_localBulkSum

/--
Boundary reconstruction theorem in exactly the shape needed for
`GlobalStokesData.globalBoundaryIntegral_eq_boundaryPartitionSum`.
-/
theorem toGlobalStokesData_globalBoundaryIntegral_eq_boundaryPartitionSum
    (R : PartitionReconstructionData I' ω' Chart InteriorPiece BoundaryPiece) :
    R.globalBoundaryIntegral =
      Finset.sum R.activeCharts fun x =>
        Finset.sum (R.boundaryPieces x) fun q => R.boundaryPartitionTerm x q :=
  R.globalBoundaryIntegral_eq_boundaryPartitionSum

/--
Convert reconstruction data plus the remaining local/cancellation/chart-change
inputs into the final `GlobalStokesData` package.
-/
def toGlobalStokesData
    (R : PartitionReconstructionData I' ω' Chart InteriorPiece BoundaryPiece)
    (interiorBoundaryTerm : Chart → InteriorPiece → Real)
    (boundaryBoundaryTerm : Chart → BoundaryPiece → Real)
    (interiorLocalStokes :
      ∀ x, x ∈ R.activeCharts →
        ∀ q, q ∈ R.interiorPieces x →
          R.interiorBulkTerm x q = interiorBoundaryTerm x q)
    (boundaryLocalStokes :
      ∀ x, x ∈ R.activeCharts →
        ∀ q, q ∈ R.boundaryPieces x →
          R.boundaryBulkTerm x q = boundaryBoundaryTerm x q)
    (interiorBoundaryCancellation :
      (Finset.sum R.activeCharts fun x =>
        Finset.sum (R.interiorPieces x) fun q => interiorBoundaryTerm x q) = 0)
    (chartChangeCancellation :
      (Finset.sum R.activeCharts fun x =>
          Finset.sum (R.boundaryPieces x) fun q => boundaryBoundaryTerm x q) =
        Finset.sum R.activeCharts fun x =>
          Finset.sum (R.boundaryPieces x) fun q => R.boundaryPartitionTerm x q) :
    GlobalStokesData I' ω' Chart InteriorPiece BoundaryPiece where
  activeCharts := R.activeCharts
  interiorPieces := R.interiorPieces
  boundaryPieces := R.boundaryPieces
  interiorBulkTerm := R.interiorBulkTerm
  interiorBoundaryTerm := interiorBoundaryTerm
  boundaryBulkTerm := R.boundaryBulkTerm
  boundaryBoundaryTerm := boundaryBoundaryTerm
  boundaryPartitionTerm := R.boundaryPartitionTerm
  globalBulkIntegral := R.globalBulkIntegral
  globalBoundaryIntegral := R.globalBoundaryIntegral
  globalBulkIntegral_eq_localBulkSum :=
    toGlobalStokesData_globalBulkIntegral_eq_localBulkSum R
  interiorLocalStokes := interiorLocalStokes
  boundaryLocalStokes := boundaryLocalStokes
  interiorBoundaryCancellation := interiorBoundaryCancellation
  chartChangeCancellation := chartChangeCancellation
  globalBoundaryIntegral_eq_boundaryPartitionSum :=
    toGlobalStokesData_globalBoundaryIntegral_eq_boundaryPartitionSum R

end GlobalStokesWrapper

end PartitionReconstructionData

end ReconstructionPackage

end Stokes

end
