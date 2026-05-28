import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Stokes.Global.CoverIndexedLocalizedRefinedEndpoint
import Stokes.Global.CoverIndexedLocalizedSupportRefinement
import Stokes.Global.CoverIndexedZeroCompactRefinedPartitionConstructor
import Stokes.Global.CoverIndexedZeroCompactSmoothBoxRefinement

/-!
# Geometry-rich localized refined boundary partitions

Worker endpoint modules reserve
`CoverIndexedBoundaryLocalizedRefinedPartition` for the final algebra layer:
finite refined pieces plus local bulk and boundary scalar terms.

This file supplies the geometry-rich input package that feeds that endpoint.
It records source/target charts, coefficients, half-space box geometry,
reconstruction on `K`, and the direct zero/localized support field.  It
deliberately avoids the older `base_tsupport_subset_coordSupport` and
coefficient-support carrier fields.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section LocalizedRefinedGeometry

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
Geometry-rich refinement of the boundary part of a selected partition, with
direct localized support.

This is a constructor-facing package.  The endpoint algebra projection is
`toEndpointPartition`.
-/
structure CoverIndexedBoundaryLocalizedRefinedGeometry
    (C : CompactSupportChartCoverSelection I K)
    (P : SupportControlledSelectedPartition C)
    (omega : ManifoldForm I M n) (BoundaryPiece : Type b) where
  /-- Finite local half-space boxes attached to each selected boundary chart. -/
  boundaryPieces : CoverIndexedBoundaryIndex (I := I) C -> Finset BoundaryPiece
  /-- Source chart used for a refined box. -/
  sourceChart : CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> M
  /-- Target chart used for the transition-pullback representative. -/
  targetChart : CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> M
  /-- Refined scalar coefficient, intended as a subpartition of the boundary coefficient. -/
  coefficient :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> M -> Real
  /-- Lower corner of the refined half-space support box. -/
  lower :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> Fin (n + 1) -> Real
  /-- Upper corner of the refined half-space support box. -/
  upper :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> Fin (n + 1) -> Real
  /-- The refined coefficients reconstruct the original boundary coefficient on `K`. -/
  reconstruct_on_K :
    forall i x, x ∈ K ->
      (Finset.sum (boundaryPieces i) fun q => coefficient i q x) =
        P.partition (Sum.inr i) x
  /-- The lower normal coordinate is normalized to the boundary face. -/
  lower_zero :
    forall i q, q ∈ boundaryPieces i -> lower i q 0 = 0
  /-- Ordered box corners. -/
  lower_le_upper :
    forall i q, q ∈ boundaryPieces i -> lower i q ≤ upper i q
  /-- Closed refined boxes lie in the boundary chart-transition domain. -/
  Icc_subset_boundaryChartDomain :
    forall i q, q ∈ boundaryPieces i ->
      Icc (lower i q) (upper i q) ⊆
        boundaryChartDomain I (sourceChart i q) (targetChart i q)
  /--
  Direct zero/localized support field: each refined localized representative is
  supported in its assigned half-space support box.
  -/
  localized_tsupport_subset_halfSpaceSupportBox :
    forall i q, q ∈ boundaryPieces i ->
      tsupport
          (ManifoldForm.transitionPullbackInChart I
            (sourceChart i q) (targetChart i q)
            (ManifoldForm.localizedForm I (coefficient i q) omega)) ⊆
        halfSpaceSupportBox (lower i q) (upper i q)

namespace CoverIndexedBoundaryLocalizedRefinedGeometry

variable
  (D : CoverIndexedBoundaryLocalizedRefinedGeometry
    (I := I) (K := K) C P omega BoundaryPiece)

/-- The localized manifold form attached to a refined boundary box. -/
def localizedForm
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) :
    ManifoldForm I M n :=
  ManifoldForm.localizedForm I (D.coefficient i q) omega

/-- The local bulk integral attached to a refined boundary box. -/
def localBulkTerm
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) : Real :=
  projectLocalBulkIntegral I (D.sourceChart i q) (D.targetChart i q)
    (D.localizedForm i q) (D.lower i q) (D.upper i q)

/-- The outward-first boundary integral attached to a refined boundary box. -/
def localBoundaryTerm
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) : Real :=
  projectLocalBoundaryIntegral I (D.sourceChart i q) (D.targetChart i q)
    (D.localizedForm i q) (D.lower i q) (D.upper i q)

/--
Projection to Worker 5's minimal endpoint-algebra structure.
-/
def toEndpointPartition :
    CoverIndexedBoundaryLocalizedRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece where
  boundaryPieces := D.boundaryPieces
  localBulkTerm := D.localBulkTerm
  localBoundaryTerm := D.localBoundaryTerm

@[simp]
theorem toEndpointPartition_boundaryPieces
    (i : CoverIndexedBoundaryIndex (I := I) C) :
    (D.toEndpointPartition (I := I) (K := K)).boundaryPieces i =
      D.boundaryPieces i :=
  rfl

@[simp]
theorem toEndpointPartition_localBulkTerm
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) :
    (D.toEndpointPartition (I := I) (K := K)).localBulkTerm i q =
      D.localBulkTerm i q :=
  rfl

@[simp]
theorem toEndpointPartition_localBoundaryTerm
    (i : CoverIndexedBoundaryIndex (I := I) C) (q : BoundaryPiece) :
    (D.toEndpointPartition (I := I) (K := K)).localBoundaryTerm i q =
      D.localBoundaryTerm i q :=
  rfl

/-- Alias emphasizing that the stored support datum is the zero/localized one. -/
theorem zeroLocalized_tsupport_subset_halfSpaceSupportBox
    (i : CoverIndexedBoundaryIndex (I := I) C) {q : BoundaryPiece}
    (hq : q ∈ D.boundaryPieces i) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I
          (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q)) ⊆
      halfSpaceSupportBox (D.lower i q) (D.upper i q) := by
  simpa [localizedForm] using
    D.localized_tsupport_subset_halfSpaceSupportBox i q hq

/--
Pointwise reconstruction of the original boundary localized form from the
localized refined pieces, on the compact support set.
-/
theorem sum_localizedForm_apply_eq_coverIndexLocalizedForm_apply
    (i : CoverIndexedBoundaryIndex (I := I) C) {x : M} (hxK : x ∈ K) :
    (Finset.sum (D.boundaryPieces i) fun q => D.localizedForm i q x) =
      P.coverIndexLocalizedForm omega (Sum.inr i) x := by
  classical
  calc
    (Finset.sum (D.boundaryPieces i) fun q => D.localizedForm i q x)
        = Finset.sum (D.boundaryPieces i) fun q =>
            D.coefficient i q x • omega x := by
          simp [localizedForm]
    _ = (Finset.sum (D.boundaryPieces i) fun q =>
            D.coefficient i q x) • omega x := by
          rw [Finset.sum_smul]
    _ = P.partition (Sum.inr i) x • omega x := by
          rw [D.reconstruct_on_K i x hxK]
    _ = P.coverIndexLocalizedForm omega (Sum.inr i) x := by
          rfl

/--
Refined local Stokes summed over selected boundary charts and localized
refined boxes, using the stored direct localized support field.
-/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
    (hfields :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
            (D.lower i q) (D.upper i q)) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
      (I := I) (ω := omega)
      (active := (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)))
      (boundaryPieces := D.boundaryPieces)
      (sourceChart := D.sourceChart) (targetChart := D.targetChart)
      (rho := D.coefficient)
      (lower := D.lower) (upper := D.upper)
      (by
        intro i _hi q hq
        exact D.localized_tsupport_subset_halfSpaceSupportBox i q hq)
      hfields

/--
Endpoint represented equality generated from the localized-support local Stokes
sum.
-/
theorem endpoint_representedStokes_of_localizedSupport_interiorFields
    (hfields :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (D.sourceChart i q) (D.targetChart i q) (D.localizedForm i q))
            (D.lower i q) (D.upper i q)) :
    (D.toEndpointPartition (I := I) (K := K)).generatedRepresentedBulkIntegral
        (I := I) (K := K) =
      (D.toEndpointPartition (I := I) (K := K)).generatedRepresentedBoundaryIntegral
        (I := I) (K := K) := by
  exact
    (D.toEndpointPartition (I := I) (K := K)).representedStokes_of_localStokes
      (I := I) (K := K)
      (by
        simpa [toEndpointPartition] using
          D.boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_localizedSupport_interiorFields
            (I := I) (K := K) hfields)

/-- Build the localized refined geometry package from explicit fields. -/
def ofDirectLocalizedSupport
    (boundaryPieces :
      CoverIndexedBoundaryIndex (I := I) C -> Finset BoundaryPiece)
    (sourceChart targetChart :
      CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> M)
    (coefficient :
      CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> M -> Real)
    (lower upper :
      CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece ->
        Fin (n + 1) -> Real)
    (reconstruct_on_K :
      forall i x, x ∈ K ->
        (Finset.sum (boundaryPieces i) fun q => coefficient i q x) =
          P.partition (Sum.inr i) x)
    (lower_zero :
      forall i q, q ∈ boundaryPieces i -> lower i q 0 = 0)
    (lower_le_upper :
      forall i q, q ∈ boundaryPieces i -> lower i q ≤ upper i q)
    (Icc_subset_boundaryChartDomain :
      forall i q, q ∈ boundaryPieces i ->
        Icc (lower i q) (upper i q) ⊆
          boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (localized_tsupport_subset_halfSpaceSupportBox :
      forall i q, q ∈ boundaryPieces i ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q)
              (ManifoldForm.localizedForm I (coefficient i q) omega)) ⊆
          halfSpaceSupportBox (lower i q) (upper i q)) :
    CoverIndexedBoundaryLocalizedRefinedGeometry
      (I := I) (K := K) C P omega BoundaryPiece where
  boundaryPieces := boundaryPieces
  sourceChart := sourceChart
  targetChart := targetChart
  coefficient := coefficient
  lower := lower
  upper := upper
  reconstruct_on_K := reconstruct_on_K
  lower_zero := lower_zero
  lower_le_upper := lower_le_upper
  Icc_subset_boundaryChartDomain := Icc_subset_boundaryChartDomain
  localized_tsupport_subset_halfSpaceSupportBox :=
    localized_tsupport_subset_halfSpaceSupportBox

/--
Forget the older coordinate-support-heavy refined partition to the localized
geometry package.  Only its final localized support field is used.
-/
def ofBoxRefinedPartition
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P omega BoundaryPiece) :
    CoverIndexedBoundaryLocalizedRefinedGeometry
      (I := I) (K := K) C P omega BoundaryPiece :=
  ofDirectLocalizedSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (BoundaryPiece := BoundaryPiece)
    D.boundaryPieces D.sourceChart D.targetChart D.coefficient
    D.lower D.upper D.reconstruct_on_K
    D.lower_zero D.lower_le_upper D.Icc_subset_boundaryChartDomain
    D.localized_tsupport_subset_halfSpaceSupportBox

end CoverIndexedBoundaryLocalizedRefinedGeometry

end LocalizedRefinedGeometry

section SmoothRefinementConstructors

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b} [DecidableEq BoundaryPiece]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace BoundarySmoothBoxRefinement

variable
  (S : BoundarySmoothBoxRefinement
    (I := I) (K := K) C P BoundaryPiece)

/--
Constructor from a smooth refinement.  Geometry and localized support remain
explicit because the smooth refinement records the subpartition and manifold
open cover, while the zero/localized support route may obtain support by a
separate argument.
-/
def toLocalizedRefinedGeometry
    (targetChart :
      CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece -> M)
    (lower_zero :
      forall i q, q ∈ S.boundaryPieces i -> S.lower i q 0 = 0)
    (lower_le_upper :
      forall i q, q ∈ S.boundaryPieces i -> S.lower i q ≤ S.upper i q)
    (Icc_subset_boundaryChartDomain :
      forall i q, q ∈ S.boundaryPieces i ->
        Icc (S.lower i q) (S.upper i q) ⊆
          boundaryChartDomain I (S.sourceChart i q) (targetChart i q))
    (localized_tsupport_subset_halfSpaceSupportBox :
      forall i q, q ∈ S.boundaryPieces i ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (S.sourceChart i q) (targetChart i q)
              (ManifoldForm.localizedForm I (S.coefficient i q) omega)) ⊆
          halfSpaceSupportBox (S.lower i q) (S.upper i q)) :
    CoverIndexedBoundaryLocalizedRefinedGeometry
      (I := I) (K := K) C P omega BoundaryPiece :=
  CoverIndexedBoundaryLocalizedRefinedGeometry.ofDirectLocalizedSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (BoundaryPiece := BoundaryPiece)
    S.boundaryPieces S.sourceChart targetChart S.coefficient
    S.lower S.upper
    (by
      intro i x hxK
      exact S.reconstruct_on_K i (x := x) hxK)
    lower_zero lower_le_upper Icc_subset_boundaryChartDomain
    localized_tsupport_subset_halfSpaceSupportBox

end BoundarySmoothBoxRefinement

end SmoothRefinementConstructors

section FiniteHalfSpaceCoverConstructors

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable
  {coordCarrier ambient :
    CoverIndexedBoundaryIndex (I := I) C -> Set (Fin (n + 1) -> Real)}
variable {Piece : CoverIndexedBoundaryIndex (I := I) C -> Type p}

namespace CoverIndexedBoundaryLocalizedRefinedGeometry

/--
Constructor from a selected finite half-space cover with dependent per-chart
pieces.  The cover supplies the finite pieces and box geometry; the direct
localized support field is the only support hypothesis.
-/
def ofFiniteHalfSpaceCover
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (sourceChart targetChart :
      forall i : CoverIndexedBoundaryIndex (I := I) C, Piece i -> M)
    (coefficient :
      forall i : CoverIndexedBoundaryIndex (I := I) C, Piece i -> M -> Real)
    (reconstruct_on_K :
      forall i x, x ∈ K ->
        (Finset.sum (D.activePieces i) fun q => coefficient i q x) =
          P.partition (Sum.inr i) x)
    (Icc_subset_boundaryChartDomain :
      forall i q, q ∈ D.activePieces i ->
        Icc (D.lowerCorner i q) (D.upperCorner i q) ⊆
          boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (localized_tsupport_subset_halfSpaceSupportBox :
      forall i q, q ∈ D.activePieces i ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q)
              (ManifoldForm.localizedForm I (coefficient i q) omega)) ⊆
          halfSpaceSupportBox (D.lowerCorner i q) (D.upperCorner i q)) :
    CoverIndexedBoundaryLocalizedRefinedGeometry
      (I := I) (K := K) C P omega
      (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  ofDirectLocalizedSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (BoundaryPiece := SigmaBoundaryPiece (I := I) (K := K) C Piece)
    (boundaryPieces := D.sigmaBoundaryPieces)
    (sourceChart := fun _ q => sourceChart q.1 q.2)
    (targetChart := fun _ q => targetChart q.1 q.2)
    (coefficient := fun _ q => coefficient q.1 q.2)
    (lower := fun _ q => D.lowerCorner q.1 q.2)
    (upper := fun _ q => D.upperCorner q.1 q.2)
    (reconstruct_on_K := by
      intro i x hxK
      calc
        Finset.sum (D.sigmaBoundaryPieces i)
            (fun q => coefficient q.1 q.2 x)
            =
            Finset.sum
              ({i} : Finset (CoverIndexedBoundaryIndex (I := I) C))
              (fun j =>
                Finset.sum (D.activePieces j)
                  (fun q => coefficient j q x)) := by
              simpa [CoverIndexedFiniteHalfSpaceBoxCover.sigmaBoundaryPieces]
                using
                  (Finset.sum_sigma'
                    ({i} : Finset (CoverIndexedBoundaryIndex (I := I) C))
                    (fun j => D.activePieces j)
                    (fun j q => coefficient j q x)).symm
        _ = Finset.sum (D.activePieces i) (fun q => coefficient i q x) := by
              simp
        _ = P.partition (Sum.inr i) x :=
              reconstruct_on_K i x hxK)
    (lower_zero := by
      intro i q hq
      exact
        (D.cover q.1).lowerCorner_zero q.2
          (by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces] using
              D.sigmaBoundaryPieces_active hq))
    (lower_le_upper := by
      intro i q hq
      exact
        (D.cover q.1).lower_le_upper q.2
          (by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces] using
              D.sigmaBoundaryPieces_active hq))
    (Icc_subset_boundaryChartDomain := by
      intro i q hq
      exact
        Icc_subset_boundaryChartDomain q.1 q.2
          (D.sigmaBoundaryPieces_active hq))
    (localized_tsupport_subset_halfSpaceSupportBox := by
      intro i q hq
      exact
        localized_tsupport_subset_halfSpaceSupportBox q.1 q.2
          (D.sigmaBoundaryPieces_active hq))

/--
Finite-cover constructor deriving the boundary-domain containment from the
ambient field of the selected finite cover.
-/
def ofFiniteHalfSpaceCoverOfAmbientDomain
    (D :
      CoverIndexedFiniteHalfSpaceBoxCover
        (I := I) (K := K) C coordCarrier ambient Piece)
    (sourceChart targetChart :
      forall i : CoverIndexedBoundaryIndex (I := I) C, Piece i -> M)
    (coefficient :
      forall i : CoverIndexedBoundaryIndex (I := I) C, Piece i -> M -> Real)
    (reconstruct_on_K :
      forall i x, x ∈ K ->
        (Finset.sum (D.activePieces i) fun q => coefficient i q x) =
          P.partition (Sum.inr i) x)
    (ambient_subset_boundaryChartDomain :
      forall i q, q ∈ D.activePieces i ->
        ambient i ⊆ boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (localized_tsupport_subset_halfSpaceSupportBox :
      forall i q, q ∈ D.activePieces i ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q)
              (ManifoldForm.localizedForm I (coefficient i q) omega)) ⊆
          halfSpaceSupportBox (D.lowerCorner i q) (D.upperCorner i q)) :
    CoverIndexedBoundaryLocalizedRefinedGeometry
      (I := I) (K := K) C P omega
      (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  ofFiniteHalfSpaceCover
    (I := I) (K := K) (omega := omega) (C := C) (P := P) D
    sourceChart targetChart coefficient reconstruct_on_K
    (fun i q hq =>
      (D.Icc_subset_ambient i hq).trans
        (ambient_subset_boundaryChartDomain i q hq))
    localized_tsupport_subset_halfSpaceSupportBox

end CoverIndexedBoundaryLocalizedRefinedGeometry

end FiniteHalfSpaceCoverConstructors

section SmoothFiniteCoverConstructor

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}
variable
  {coordCarrier ambient :
    CoverIndexedBoundaryIndex (I := I) C -> Set (Fin (n + 1) -> Real)}
variable {Piece : CoverIndexedBoundaryIndex (I := I) C -> Type p}

namespace BoundarySmoothBoxRefinement

variable [DecidableEq (SigmaBoundaryPiece (I := I) (K := K) C Piece)]
variable
  (S :
    BoundarySmoothBoxRefinement
      (I := I) (K := K) C P
      (SigmaBoundaryPiece (I := I) (K := K) C Piece))
  (F :
    CoverIndexedFiniteHalfSpaceBoxCover
      (I := I) (K := K) C coordCarrier ambient Piece)

/--
Constructor from a smooth refinement paired with a selected finite half-space
cover.  The localized support statement is an explicit constructor argument,
so this route does not ask for the old base-coordinate support theorem.
-/
def toLocalizedRefinedGeometryOfFiniteHalfSpaceCover
    (targetChart :
      forall i : CoverIndexedBoundaryIndex (I := I) C, Piece i -> M)
    (boundaryPieces_eq :
      forall i : CoverIndexedBoundaryIndex (I := I) C,
        S.boundaryPieces i = F.sigmaBoundaryPieces i)
    (ambient_subset_boundaryChartDomain :
      forall i (q : Piece i), q ∈ F.activePieces i ->
        ambient i ⊆
          boundaryChartDomain I (S.sourceChart i ⟨i, q⟩) (targetChart i q))
    (localized_tsupport_subset_halfSpaceSupportBox :
      forall i (q : Piece i), q ∈ F.activePieces i ->
        tsupport
            (ManifoldForm.transitionPullbackInChart I
              (S.sourceChart i ⟨i, q⟩) (targetChart i q)
              (ManifoldForm.localizedForm I (S.coefficient i ⟨i, q⟩) omega)) ⊆
          halfSpaceSupportBox (F.lowerCorner i q) (F.upperCorner i q)) :
    CoverIndexedBoundaryLocalizedRefinedGeometry
      (I := I) (K := K) C P omega
      (SigmaBoundaryPiece (I := I) (K := K) C Piece) :=
  CoverIndexedBoundaryLocalizedRefinedGeometry.ofDirectLocalizedSupport
    (I := I) (K := K) (C := C) (P := P) (omega := omega)
    (BoundaryPiece := SigmaBoundaryPiece (I := I) (K := K) C Piece)
    (boundaryPieces := F.sigmaBoundaryPieces)
    (sourceChart := fun _ q => S.sourceChart q.1 q)
    (targetChart := fun _ q => targetChart q.1 q.2)
    (coefficient := fun _ q => S.coefficient q.1 q)
    (lower := fun _ q => F.lowerCorner q.1 q.2)
    (upper := fun _ q => F.upperCorner q.1 q.2)
    (reconstruct_on_K := by
      intro i x hxK
      calc
        Finset.sum (F.sigmaBoundaryPieces i)
            (fun q => S.coefficient q.1 q x)
            =
            Finset.sum (F.sigmaBoundaryPieces i)
              (fun q => S.coefficient i q x) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              have howner : q.1 = i := (F.mem_sigmaBoundaryPieces.mp hq).1
              cases howner
              rfl
        _ = P.partition (Sum.inr i) x := by
              simpa [boundaryPieces_eq i] using
                S.reconstruct_on_K i (x := x) hxK)
    (lower_zero := by
      intro i q hq
      exact
        (F.cover q.1).lowerCorner_zero q.2
          (by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces] using
              F.sigmaBoundaryPieces_active hq))
    (lower_le_upper := by
      intro i q hq
      exact
        (F.cover q.1).lower_le_upper q.2
          (by
            simpa [CoverIndexedFiniteHalfSpaceBoxCover.activePieces] using
              F.sigmaBoundaryPieces_active hq))
    (Icc_subset_boundaryChartDomain := by
      intro i q hq
      have hactive : q.2 ∈ F.activePieces q.1 :=
        F.sigmaBoundaryPieces_active hq
      exact
        (F.Icc_subset_ambient q.1 hactive).trans
          (ambient_subset_boundaryChartDomain q.1 q.2 hactive))
    (localized_tsupport_subset_halfSpaceSupportBox := by
      intro i q hq
      exact
        localized_tsupport_subset_halfSpaceSupportBox q.1 q.2
          (F.sigmaBoundaryPieces_active hq))

end BoundarySmoothBoxRefinement

end SmoothFiniteCoverConstructor

end Stokes

end
