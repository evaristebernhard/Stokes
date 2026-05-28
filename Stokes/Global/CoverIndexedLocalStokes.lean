import Stokes.Global.CompactSupportLocalStokesPackage
import Stokes.Global.InteriorSupportControlledAssignedBox
import Stokes.Global.BoundarySupportControlledAssignedBox

/-!
# Cover-indexed local Stokes finite sums

This file is a small algebraic assembly layer for local Stokes data indexed by
a finite cover.  The main package is intentionally independent of
`SelectedBoxPartitionOfUnity`: it only needs a finite index set, local bulk
terms, true boundary terms, and the interior artificial-boundary zero facts.

The last section gives the minimal bridges back to the selected-cover APIs.
Those bridges do not solve the remaining analytic adapter work; callers still
have to provide coordinate carriers, chart-domain containment, smoothness
neighborhoods, and later chart-change/boundary-measure reconstruction data.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section Algebra

universe c b p

variable {ι : Type c} {BoundaryPiece : Type b} {Piece : Type p}

/-- Pointwise-zero cover-indexed artificial terms vanish after finite summation. -/
theorem coverIndexed_interiorArtificialBoundarySum_eq_zero
    (active : Finset ι) (artificialBoundaryTerm : ι -> Real)
    (hzero : forall i, i ∈ active -> artificialBoundaryTerm i = 0) :
    (Finset.sum active fun i => artificialBoundaryTerm i) = 0 := by
  classical
  exact Finset.sum_eq_zero hzero

/--
Nested finite-sum version of pointwise artificial-term vanishing.  This is the
shape used when a cover index carries a finite local-piece fiber.
-/
theorem coverIndexed_nestedArtificialBoundarySum_eq_zero
    (active : Finset ι) (pieces : ι -> Finset Piece)
    (artificialBoundaryTerm : ι -> Piece -> Real)
    (hzero :
      forall i, i ∈ active ->
        forall q, q ∈ pieces i -> artificialBoundaryTerm i q = 0) :
    (Finset.sum active fun i =>
      Finset.sum (pieces i) fun q => artificialBoundaryTerm i q) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact Finset.sum_eq_zero (hzero i hi)

/--
Cover-indexed local Stokes data.

Interior pieces are already collapsed to one cover-level real term: this is the
right shape for the selected compact-support route, where assigned-box support
kills the full interior artificial side.  Boundary pieces may still have a
finite fiber over each cover index.
-/
structure CoverIndexedLocalStokesPackage
    (ι : Type c) (BoundaryPiece : Type b) where
  /-- Finite cover labels used in this assembly layer. -/
  active : Finset ι
  /-- Finite true-boundary local pieces attached to each cover label. -/
  boundaryPieces : ι -> Finset BoundaryPiece
  /-- Cover-level interior bulk contribution. -/
  interiorBulkTerm : ι -> Real
  /-- Cover-level interior artificial-boundary contribution. -/
  interiorArtificialBoundaryTerm : ι -> Real
  /-- Boundary half-space/local bulk contribution. -/
  boundaryBulkTerm : ι -> BoundaryPiece -> Real
  /-- True outward-first local boundary contribution. -/
  trueBoundaryTerm : ι -> BoundaryPiece -> Real
  /-- Interior local Stokes on every active cover index. -/
  interiorLocalStokes :
    forall i, i ∈ active ->
      interiorBulkTerm i = interiorArtificialBoundaryTerm i
  /-- Boundary local Stokes on every active boundary local piece. -/
  boundaryLocalStokes :
    forall i, i ∈ active ->
      forall q, q ∈ boundaryPieces i ->
        boundaryBulkTerm i q = trueBoundaryTerm i q
  /-- Assigned-box support kills the interior artificial side. -/
  interiorArtificialBoundaryZero :
    forall i, i ∈ active -> interiorArtificialBoundaryTerm i = 0

namespace CoverIndexedLocalStokesPackage

/-- Sum of cover-indexed interior bulk terms. -/
def interiorBulkSum (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) : Real :=
  Finset.sum D.active fun i => D.interiorBulkTerm i

/-- Sum of cover-indexed interior artificial-boundary terms. -/
def interiorArtificialBoundarySum
    (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) : Real :=
  Finset.sum D.active fun i => D.interiorArtificialBoundaryTerm i

/-- Sum of cover-indexed boundary bulk terms. -/
def boundaryBulkSum (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) : Real :=
  Finset.sum D.active fun i =>
    Finset.sum (D.boundaryPieces i) fun q => D.boundaryBulkTerm i q

/-- Sum of cover-indexed true outward-first boundary terms. -/
def trueBoundarySum (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) : Real :=
  Finset.sum D.active fun i =>
    Finset.sum (D.boundaryPieces i) fun q => D.trueBoundaryTerm i q

/-- The full local bulk side: interior bulk plus boundary half-space bulk. -/
def localBulkSum (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) : Real :=
  D.interiorBulkSum + D.boundaryBulkSum

/-- Interior local Stokes identities summed over all active cover labels. -/
theorem interiorBulkSum_eq_interiorArtificialBoundarySum
    (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) :
    D.interiorBulkSum = D.interiorArtificialBoundarySum := by
  exact Finset.sum_congr rfl D.interiorLocalStokes

/-- Boundary local Stokes identities summed over all active cover labels. -/
theorem boundaryBulkSum_eq_trueBoundarySum
    (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) :
    D.boundaryBulkSum = D.trueBoundarySum := by
  exact GlobalStokesData.sum_localPieces D.active D.boundaryPieces
    D.boundaryBulkTerm D.trueBoundaryTerm D.boundaryLocalStokes

/-- The assigned-box interior artificial side vanishes in the cover-indexed sum. -/
theorem interiorArtificialBoundarySum_eq_zero
    (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) :
    D.interiorArtificialBoundarySum = 0 :=
  coverIndexed_interiorArtificialBoundarySum_eq_zero
    D.active D.interiorArtificialBoundaryTerm D.interiorArtificialBoundaryZero

/-- Interior local bulk also vanishes after local Stokes and artificial-side support control. -/
theorem interiorBulkSum_eq_zero
    (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) :
    D.interiorBulkSum = 0 := by
  calc
    D.interiorBulkSum = D.interiorArtificialBoundarySum :=
      D.interiorBulkSum_eq_interiorArtificialBoundarySum
    _ = 0 := D.interiorArtificialBoundarySum_eq_zero

/--
Main cover-indexed finite-sum package theorem: local bulk terms reduce to the
finite sum of true boundary local terms.
-/
theorem localBulkSum_eq_trueBoundarySum
    (D : CoverIndexedLocalStokesPackage ι BoundaryPiece) :
    D.localBulkSum = D.trueBoundarySum := by
  rw [localBulkSum, D.interiorBulkSum_eq_zero, zero_add]
  exact D.boundaryBulkSum_eq_trueBoundarySum

end CoverIndexedLocalStokesPackage

/--
Priority theorem shape: from pointwise local Stokes and interior artificial
zero facts on a finite cover, the sum of local bulk terms equals the sum of true
boundary local terms.
-/
theorem coverIndexed_localBulkSum_eq_trueBoundarySum
    (active : Finset ι)
    (boundaryPieces : ι -> Finset BoundaryPiece)
    (interiorBulkTerm interiorArtificialBoundaryTerm : ι -> Real)
    (boundaryBulkTerm trueBoundaryTerm : ι -> BoundaryPiece -> Real)
    (hinteriorLocal :
      forall i, i ∈ active ->
        interiorBulkTerm i = interiorArtificialBoundaryTerm i)
    (hinteriorArtificialZero :
      forall i, i ∈ active -> interiorArtificialBoundaryTerm i = 0)
    (hboundaryLocal :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          boundaryBulkTerm i q = trueBoundaryTerm i q) :
    (Finset.sum active fun i => interiorBulkTerm i) +
        (Finset.sum active fun i =>
          Finset.sum (boundaryPieces i) fun q => boundaryBulkTerm i q) =
      Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q => trueBoundaryTerm i q := by
  let D : CoverIndexedLocalStokesPackage ι BoundaryPiece :=
    { active := active
      boundaryPieces := boundaryPieces
      interiorBulkTerm := interiorBulkTerm
      interiorArtificialBoundaryTerm := interiorArtificialBoundaryTerm
      boundaryBulkTerm := boundaryBulkTerm
      trueBoundaryTerm := trueBoundaryTerm
      interiorLocalStokes := hinteriorLocal
      boundaryLocalStokes := hboundaryLocal
      interiorArtificialBoundaryZero := hinteriorArtificialZero }
  exact D.localBulkSum_eq_trueBoundarySum

/-- Boundary local Stokes identities summed over a cover-indexed finite family. -/
theorem coverIndexed_boundaryBulkSum_eq_trueBoundarySum
    (active : Finset ι)
    (boundaryPieces : ι -> Finset BoundaryPiece)
    (boundaryBulkTerm trueBoundaryTerm : ι -> BoundaryPiece -> Real)
    (hboundaryLocal :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          boundaryBulkTerm i q = trueBoundaryTerm i q) :
    (Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q => boundaryBulkTerm i q) =
      Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q => trueBoundaryTerm i q :=
  GlobalStokesData.sum_localPieces active boundaryPieces
    boundaryBulkTerm trueBoundaryTerm hboundaryLocal

end Algebra

section BoundaryHalfSpace

universe u w c b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type c} {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Cover-indexed boundary half-space local Stokes, using already-localized
smoothness on each selected box neighborhood.
-/
theorem coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_coordSupport
    (active : Finset ι)
    (boundaryPieces : ι -> Finset BoundaryPiece)
    (sourceChart targetChart : ι -> BoundaryPiece -> M)
    (rho : ι -> BoundaryPiece -> M -> Real)
    (K : ι -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (lower upper : ι -> BoundaryPiece -> Fin (n + 1) -> Real)
    (U : ι -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (hK :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> IsCompact (K i q))
    (hhalf :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> K i q ⊆ upperHalfSpace n)
    (hbase :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (sourceChart i q) (targetChart i q) omega) ⊆
            K i q)
    (ha0 :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> lower i q 0 = 0)
    (hle :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> lower i q ≤ upper i q)
    (hcoeff :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (sourceChart i q) (targetChart i q) (rho i q)) ∩ K i q ⊆
            halfSpaceSupportBox (lower i q) (upper i q))
    (hdomain :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          Set.Icc (lower i q) (upper i q) ⊆
            boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (hU :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> IsOpen (U i q))
    (hUbox :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          Set.Icc (lower i q) (upper i q) ⊆ U i q)
    (hlocalizedU :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q)
              (ManifoldForm.localizedForm I (rho i q) omega)) (U i q)) :
    (Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q =>
          projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (rho i q) omega)
            (lower i q) (upper i q)) =
      Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q =>
          projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (rho i q) omega)
            (lower i q) (upper i q) := by
  exact
    coverIndexed_boundaryBulkSum_eq_trueBoundarySum active boundaryPieces
      (fun i q =>
        projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
          (ManifoldForm.localizedForm I (rho i q) omega)
          (lower i q) (upper i q))
      (fun i q =>
        projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
          (ManifoldForm.localizedForm I (rho i q) omega)
          (lower i q) (upper i q))
      (by
        intro i hi q hq
        exact
          boundaryAssignedBox_projectLocalStokes_of_coordSupport
            (I := I) (omega := omega)
            (x0 := sourceChart i q) (x1 := targetChart i q)
            (rho := rho i q)
            (hK i hi q hq) (hhalf i hi q hq) (hbase i hi q hq)
            (ha0 i hi q hq) (hle i hi q hq) (hcoeff i hi q hq)
            (hdomain i hi q hq) (hU i hi q hq) (hUbox i hi q hq)
            (hlocalizedU i hi q hq))

/--
Cover-indexed boundary half-space local Stokes, deriving localized smoothness
from coefficient and base representative smoothness on each box neighborhood.
-/
theorem coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn
    (active : Finset ι)
    (boundaryPieces : ι -> Finset BoundaryPiece)
    (sourceChart targetChart : ι -> BoundaryPiece -> M)
    (rho : ι -> BoundaryPiece -> M -> Real)
    (K : ι -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (lower upper : ι -> BoundaryPiece -> Fin (n + 1) -> Real)
    (U : ι -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (hK :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> IsCompact (K i q))
    (hhalf :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> K i q ⊆ upperHalfSpace n)
    (hbase :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (sourceChart i q) (targetChart i q) omega) ⊆
            K i q)
    (ha0 :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> lower i q 0 = 0)
    (hle :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> lower i q ≤ upper i q)
    (hcoeff :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (sourceChart i q) (targetChart i q) (rho i q)) ∩ K i q ⊆
            halfSpaceSupportBox (lower i q) (upper i q))
    (hdomain :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          Set.Icc (lower i q) (upper i q) ⊆
            boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (hU :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> IsOpen (U i q))
    (hUbox :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          Set.Icc (lower i q) (upper i q) ⊆ U i q)
    (hrhoU :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionCoefficientInChart I
              (sourceChart i q) (targetChart i q) (rho i q)) (U i q))
    (homegaU :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q) omega) (U i q)) :
    (Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q =>
          projectLocalBulkIntegral I (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (rho i q) omega)
            (lower i q) (upper i q)) =
      Finset.sum active fun i =>
        Finset.sum (boundaryPieces i) fun q =>
          projectLocalBoundaryIntegral I (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (rho i q) omega)
            (lower i q) (upper i q) := by
  exact
    coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_coordSupport
      (I := I) (omega := omega)
      active boundaryPieces sourceChart targetChart rho K lower upper U
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox
      (by
        intro i hi q hq
        exact
          ManifoldForm.contDiffOn_transitionPullbackInChart_localizedForm_of_contDiffOn
            (I := I) (hrhoU i hi q hq) (homegaU i hi q hq))

end BoundaryHalfSpace

section CoverIndexBridge

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}

namespace CompactSupportChartCoverSelection

/-- The canonical finite active set for the mixed selected cover index type. -/
def coverIndexFinset (C : CompactSupportChartCoverSelection I K) :
    Finset C.CoverIndex :=
  Finset.univ

@[simp]
theorem mem_coverIndexFinset
    (C : CompactSupportChartCoverSelection I K) (j : C.CoverIndex) :
    j ∈ C.coverIndexFinset := by
  classical
  simp [coverIndexFinset]

/-- The canonical finite active set for selected boundary cover indices. -/
def boundaryCoverIndexFinset (C : CompactSupportChartCoverSelection I K) :
    Finset {x : M // x ∈ C.boundaryCenters} :=
  Finset.univ

@[simp]
theorem mem_boundaryCoverIndexFinset
    (C : CompactSupportChartCoverSelection I K)
    (j : {x : M // x ∈ C.boundaryCenters}) :
    j ∈ C.boundaryCoverIndexFinset := by
  classical
  simp [boundaryCoverIndexFinset]

end CompactSupportChartCoverSelection

/--
Cover-index specialization of the generic local Stokes package.

This is only the finite-sum adapter.  Coordinate support, local smoothness,
chart-change, and boundary reconstruction remain separate adapter fields.
-/
abbrev CoverIndexLocalStokesPackage
    (C : CompactSupportChartCoverSelection I K) (BoundaryPiece : Type b) :=
  CoverIndexedLocalStokesPackage C.CoverIndex BoundaryPiece

/-- The generic cover-indexed theorem specialized to `C.CoverIndex`. -/
theorem coverIndex_localBulkSum_eq_trueBoundarySum
    {C : CompactSupportChartCoverSelection I K}
    (D : CoverIndexLocalStokesPackage (I := I) C BoundaryPiece) :
    D.localBulkSum = D.trueBoundarySum :=
  D.localBulkSum_eq_trueBoundarySum

namespace CompactSupportLocalStokesPackage

variable {P : SelectedBoxPartitionOfUnity I omega}
variable {boundaryPieces : M -> Finset BoundaryPiece}
variable {sourceChart targetChart : M -> BoundaryPiece -> M}
variable {rho : M -> BoundaryPiece -> M -> Real}
variable {lower upper : M -> BoundaryPiece -> Fin (n + 1) -> Real}

/--
Compatibility bridge from the older selected-chart package to the generic
cover-indexed algebra package.

This bridge deliberately keeps the old chart label type `M`; it is provided so
existing selected-partition code can consume the new finite-sum theorem while a
separate adapter aligns selected charts with `CompactSupportChartCoverSelection`
cover indices.
-/
def toCoverIndexedLocalStokesPackage
    (D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) :
    CoverIndexedLocalStokesPackage M BoundaryPiece where
  active := P.active
  boundaryPieces := boundaryPieces
  interiorBulkTerm := fun x =>
    Finset.sum (selectedInteriorLocalPieces P x) fun q =>
      selectedInteriorLocalBulkTerm P x q
  interiorArtificialBoundaryTerm := fun x =>
    Finset.sum (selectedInteriorLocalPieces P x) fun q =>
      selectedInteriorArtificialBoundaryTerm P x q
  boundaryBulkTerm :=
    assignedBoundaryLocalBulkTerm (I := I) (omega := omega)
      sourceChart targetChart rho lower upper
  trueBoundaryTerm :=
    assignedBoundaryTrueLocalTerm (I := I) (omega := omega)
      sourceChart targetChart rho lower upper
  interiorLocalStokes := by
    intro x hx
    exact Finset.sum_congr rfl fun q hq =>
      D.interiorFields.localStokes x hx q hq
  boundaryLocalStokes := D.boundaryFields.localStokes
  interiorArtificialBoundaryZero := by
    intro x hx
    refine Finset.sum_eq_zero ?_
    intro q hq
    exact D.interiorArtificialBoundaryZero x hx q hq

/-- The selected compact-support package satisfies the cover-indexed finite-sum theorem. -/
theorem toCoverIndexedLocalStokesPackage_localBulkSum_eq_trueBoundarySum
    (D :
      CompactSupportLocalStokesPackage (I := I) (omega := omega)
        P boundaryPieces sourceChart targetChart rho lower upper) :
    D.toCoverIndexedLocalStokesPackage.localBulkSum =
      D.toCoverIndexedLocalStokesPackage.trueBoundarySum :=
  D.toCoverIndexedLocalStokesPackage.localBulkSum_eq_trueBoundarySum

end CompactSupportLocalStokesPackage

namespace SupportControlledSelectedPartition

variable {C : CompactSupportChartCoverSelection I K}

/--
Boundary-cover-indexed half-space local Stokes from the support-controlled
selected partition fields.

This is the minimal cover-index bridge for the boundary half-space local
Stokes API.  It uses the selected cover's boundary subindices directly; a mixed
`C.CoverIndex` adapter only has to embed these as `Sum.inr`.
-/
theorem boundaryCoverIndex_halfSpaceBulkSum_eq_trueBoundarySum_of_fields
    (P : SupportControlledSelectedPartition C)
    (coordSupport U :
      {x : M // x ∈ C.boundaryCenters} -> Set (Fin (n + 1) -> Real))
    (hfields :
      forall i, i ∈ C.boundaryCoverIndexFinset ->
        BoundaryAssignedBoxCoordSupportFields P i omega
          (coordSupport i) (U i))
    (hrhoU :
      forall i, i ∈ C.boundaryCoverIndexFinset ->
        ContDiffOn Real ⊤
          (ManifoldForm.transitionCoefficientInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1)
            (P.partition (Sum.inr i))) (U i))
    (homegaU :
      forall i, i ∈ C.boundaryCoverIndexFinset ->
        ContDiffOn Real ⊤
          (ManifoldForm.transitionPullbackInChart I
            (C.boundaryChart i.1) (C.boundaryChart i.1) omega) (U i)) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBulkIntegral I (C.boundaryChart i.1) (C.boundaryChart i.1)
          (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) omega)
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I (C.boundaryChart i.1) (C.boundaryChart i.1)
          (ManifoldForm.localizedForm I (P.partition (Sum.inr i)) omega)
          (C.boundaryLower i.1) (C.boundaryUpper i.1) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro i hi
  rcases hfields i hi with
    ⟨hKcoord, hhalf, hbase, ha0, hle, hcoeff, hdomain, hU, hUbox⟩
  exact
    boundaryAssignedBox_projectLocalStokes_of_contDiffOn
      (I := I) (omega := omega)
      (x0 := C.boundaryChart i.1) (x1 := C.boundaryChart i.1)
      (rho := P.partition (Sum.inr i))
      hKcoord hhalf hbase ha0 hle hcoeff hdomain hU hUbox
      (hrhoU i hi) (homegaU i hi)

end SupportControlledSelectedPartition

end CoverIndexBridge

end Stokes

end
