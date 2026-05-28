import Stokes.Global.BoundaryPieceFamilyConstructor
import Stokes.Global.CoverIndexedZeroBoundaryLocalStokesConstructor
import Stokes.Global.CoverIndexedBoundaryTargetBoxDataConstructor

/-!
# Zero-source boundary piece families

The legacy `BoundaryPieceFamilyInput` stores a `sourceExtendedBox` field.  That
field proves local boundary Stokes from the old, globally supported transition
representative.  The zero-extension route proves the same source-side local
Stokes equality from a different pair of inputs:

* smoothness of the old representative on the transition source;
* support of the zero-extended representative in the selected half-space box.

This file packages that output without pretending to construct a legacy
`sourceExtendedBox`.  The adapter below feeds the existing mixed assembly layer
at its actual point of use, namely the `MixedBoundaryPackage.localStokes` field.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section ZeroBoundaryPieceFamily

universe uH uM c p

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/--
Boundary-piece family whose source local Stokes theorem is supplied directly.

Unlike `BoundaryPieceFamilyInput`, this record does not require a
`sourceExtendedBox`.  It also allows the form to vary with the piece, which is
the natural shape for cover-indexed partition pieces such as
`P.coverIndexLocalizedForm omega (Sum.inr i)`.
-/
structure ZeroBoundaryPieceFamilyInput {n : Nat}
    (I : ModelWithCorners Real (Fin (n + 1) -> Real) H)
    (Chart : Type c) (Piece : Type p) where
  /-- Finite chart labels active in the boundary decomposition. -/
  activeCharts : Finset Chart
  /-- Boundary pieces assigned to an active chart. -/
  boundaryPieces : Chart -> Finset Piece
  /-- The localized form attached to each boundary piece. -/
  form : Chart -> Piece -> ManifoldForm I M n
  /-- Source chart for the source-side half-space local Stokes theorem. -/
  sourceChart : Chart -> Piece -> M
  /-- Target chart of the source-side local Stokes theorem. -/
  boundarySourceChart : Chart -> Piece -> M
  /-- Target chart after boundary change of variables. -/
  boundaryTargetChart : Chart -> Piece -> M
  /-- Lower corner of the source half-space box. -/
  sourceLowerCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Upper corner of the source half-space box. -/
  sourceUpperCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Lower corner of the transported target boundary box. -/
  targetLowerCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Upper corner of the transported target boundary box. -/
  targetUpperCorner : Chart -> Piece -> Fin (n + 1) -> Real
  /-- Selected target boxes used by the boundary chart-change theorem. -/
  targetSelectedBox :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryChartSelectedBox I (boundarySourceChart x q) (boundaryTargetChart x q)
          (form x q) (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Oriented boundary chart-change data from the source face to the target box. -/
  orientedCOV :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        boundaryChartOrientedChangeOfVariables I
          (sourceChart x q) (boundarySourceChart x q) (form x q)
          (sourceLowerCorner x q) (sourceUpperCorner x q)
          (targetLowerCorner x q) (targetUpperCorner x q)
  /-- Source-side local Stokes, proved externally by the zero-extension route. -/
  sourceLocalStokes :
    forall x, x ∈ activeCharts ->
      forall q, q ∈ boundaryPieces x ->
        projectLocalBulkIntegral I (sourceChart x q) (boundarySourceChart x q)
            (form x q) (sourceLowerCorner x q) (sourceUpperCorner x q) =
          projectLocalBoundaryIntegral I (sourceChart x q) (boundarySourceChart x q)
            (form x q) (sourceLowerCorner x q) (sourceUpperCorner x q)

namespace ZeroBoundaryPieceFamilyInput

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {Chart : Type c} {Piece : Type p}

/-- Bulk term of one zero-source boundary piece. -/
def boundaryBulkTerm
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBulkIntegral I (D.sourceChart x q) (D.boundarySourceChart x q)
    (D.form x q) (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)

/-- Source boundary term before target chart change. -/
def sourceBoundaryTerm
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBoundaryIntegral I (D.sourceChart x q) (D.boundarySourceChart x q)
    (D.form x q) (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)

/-- Transported boundary term used by the global boundary assembly. -/
def boundaryBoundaryTerm
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece)
    (x : Chart) (q : Piece) : Real :=
  projectLocalBoundaryIntegral I (D.boundarySourceChart x q)
    (D.boundaryTargetChart x q) (D.form x q)
    (D.targetLowerCorner x q) (D.targetUpperCorner x q)

/-- Finite sum of zero-source boundary bulk terms. -/
def boundaryBulkSum
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => boundaryBulkTerm D x q

/-- Finite sum of transported boundary terms. -/
def boundaryBoundarySum
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece) : Real :=
  Finset.sum D.activeCharts fun x =>
    Finset.sum (D.boundaryPieces x) fun q => boundaryBoundaryTerm D x q

/--
Pointwise local Stokes in the shape consumed by boundary assembly:
zero-source local Stokes followed by the selected boundary chart-change
theorem.
-/
theorem localStokes
    [IsManifold I 1 M]
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece) :
    forall x, x ∈ D.activeCharts ->
      forall q, q ∈ D.boundaryPieces x ->
        boundaryBulkTerm D x q = boundaryBoundaryTerm D x q := by
  intro x hx q hq
  calc
    boundaryBulkTerm D x q = sourceBoundaryTerm D x q := by
      simpa [boundaryBulkTerm, sourceBoundaryTerm] using
        D.sourceLocalStokes x hx q hq
    _ = boundaryBoundaryTerm D x q := by
      simpa [sourceBoundaryTerm, boundaryBoundaryTerm] using
        projectLocalBoundaryIntegral_chartChange_selected
          (D.sourceChart x q) (D.boundarySourceChart x q)
          (D.boundaryTargetChart x q) (D.form x q)
          (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)
          (D.targetLowerCorner x q) (D.targetUpperCorner x q)
          (D.orientedCOV x hx q hq) (D.targetSelectedBox x hx q hq)

/-- The zero-source local Stokes identities summed over all active pieces. -/
theorem boundaryBulkSum_eq_boundaryBoundarySum
    [IsManifold I 1 M]
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece) :
    boundaryBulkSum D = boundaryBoundarySum D := by
  exact GlobalStokesData.sum_localPieces D.activeCharts D.boundaryPieces
    (boundaryBulkTerm D) (boundaryBoundaryTerm D) D.localStokes

/--
Direct adapter to the existing mixed boundary package.

This is the useful bridge for assembly: the mixed constructor only needs the
local equality field, so it does not require reconstructing the legacy
`BoundaryPieceFamilyInput.sourceExtendedBox`.
-/
def toMixedBoundaryPackage
    [IsManifold I 1 M]
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece)
    (omega : ManifoldForm I M n) :
    MixedBoundaryPackage I omega Chart Piece
      D.activeCharts D.boundaryPieces
      (boundaryBulkTerm D) (boundaryBoundaryTerm D) where
  localStokes := D.localStokes

/--
If a caller still wants to use `BoundaryPieceFamilyInput`, this is the exact
extra field they must supply.  The zero-source route deliberately does not
construct it.
-/
abbrev LegacySourceExtendedBoxField
    (D : ZeroBoundaryPieceFamilyInput (M := M) I Chart Piece) : Prop :=
  forall x, x ∈ D.activeCharts ->
    forall q, q ∈ D.boundaryPieces x ->
      boundaryChartExtendedBox I (D.sourceChart x q) (D.boundarySourceChart x q)
        (D.form x q) (D.sourceLowerCorner x q) (D.sourceUpperCorner x q)

end ZeroBoundaryPieceFamilyInput

end ZeroBoundaryPieceFamily

section CoverIndexedZeroBoundaryPieceFamily

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega omegaGlobal : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

namespace CoverIndexedCompactSupportNeighborhoodDataInfty

/--
Cover-indexed zero-source boundary pieces.

The source-side local Stokes field is exactly
`boundary_projectLocalStokes_of_zero_tsupport_subset_source`; the target side is
left as explicit selected COV data so this adapter can be used before the
orientation inputs are collapsed.
-/
def zeroBoundaryPieceFamilyInput
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    [IsManifold I ⊤ M]
    (hsourceOpen :
      forall i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      forall i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (boundaryTargetChart :
      {x : M // x ∈ C.boundaryCenters} -> M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} -> Fin (n + 1) -> Real)
    (targetSelectedBox :
      forall i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I (transitionSupportData.targetChart i)
          (boundaryTargetChart i) (P.coverIndexLocalizedForm omega (Sum.inr i))
          (targetLower i) (targetUpper i))
    (orientedCOV :
      forall i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    ZeroBoundaryPieceFamilyInput (M := M) I
      {x : M // x ∈ C.boundaryCenters} Unit where
  activeCharts := C.boundaryCoverIndexFinset
  boundaryPieces := fun _ => {()}
  form := fun i _ => P.coverIndexLocalizedForm omega (Sum.inr i)
  sourceChart := fun i _ => C.boundaryChart i.1
  boundarySourceChart := fun i _ => transitionSupportData.targetChart i
  boundaryTargetChart := fun i _ => boundaryTargetChart i
  sourceLowerCorner := fun i _ => C.boundaryLower i.1
  sourceUpperCorner := fun i _ => C.boundaryUpper i.1
  targetLowerCorner := fun i _ => targetLower i
  targetUpperCorner := fun i _ => targetUpper i
  targetSelectedBox := by
    intro i _hi q _hq
    cases q
    exact targetSelectedBox i
  orientedCOV := by
    intro i _hi q _hq
    cases q
    exact orientedCOV i
  sourceLocalStokes := by
    intro i _hi q _hq
    cases q
    exact
      neighborhoodData.boundary_projectLocalStokes_of_zero_tsupport_subset_source
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        transitionSupportData i (hsourceOpen i) (hzero i)

/--
Cover-indexed zero-source package as the existing mixed-boundary local Stokes
field.  The `omegaGlobal` parameter is only the ambient form parameter carried
by `MixedBoundaryPackage`; the actual local terms are those stored in the
zero-source package and may use localized forms.
-/
def zeroBoundaryMixedPackage
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (hsourceOpen :
      forall i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      forall i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (boundaryTargetChart :
      {x : M // x ∈ C.boundaryCenters} -> M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} -> Fin (n + 1) -> Real)
    (targetSelectedBox :
      forall i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I (transitionSupportData.targetChart i)
          (boundaryTargetChart i) (P.coverIndexLocalizedForm omega (Sum.inr i))
          (targetLower i) (targetUpper i))
    (orientedCOV :
      forall i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    let D :=
      zeroBoundaryPieceFamilyInput
        (I := I) (K := K) (C := C) (P := P) (omega := omega)
        neighborhoodData transitionSupportData hsourceOpen hzero
        boundaryTargetChart targetLower targetUpper targetSelectedBox orientedCOV
    MixedBoundaryPackage I omegaGlobal
      {x : M // x ∈ C.boundaryCenters} Unit
      D.activeCharts D.boundaryPieces
      (ZeroBoundaryPieceFamilyInput.boundaryBulkTerm D)
      (ZeroBoundaryPieceFamilyInput.boundaryBoundaryTerm D) :=
  let D :=
    zeroBoundaryPieceFamilyInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData hsourceOpen hzero
      boundaryTargetChart targetLower targetUpper targetSelectedBox orientedCOV
  D.toMixedBoundaryPackage omegaGlobal

/--
Replacement finite-sum theorem for the legacy boundary-piece local Stokes sum.
It is the same assembly ingredient as `BoundaryPieceFamilyInput` used to
provide, but its source local Stokes proof comes from zero-extension support.
-/
theorem zeroBoundaryBulkSum_eq_targetBoundarySum
    [IsManifold I ⊤ M] [IsManifold I 1 M]
    (neighborhoodData :
      CoverIndexedCompactSupportNeighborhoodDataInfty
        (I := I) (K := K) C P omega)
    (transitionSupportData :
      CoverIndexedCompactSupportTransitionSupportData
        (I := I) (K := K) C P omega)
    (hsourceOpen :
      forall i : {x : M // x ∈ C.boundaryCenters},
        IsOpen
          (ManifoldForm.chartTransitionSource I
            (C.boundaryChart i.1) (transitionSupportData.targetChart i)))
    (hzero :
      forall i : {x : M // x ∈ C.boundaryCenters},
        tsupport
            (ManifoldForm.transitionPullbackInChartZero I
              (C.boundaryChart i.1) (transitionSupportData.targetChart i)
              (P.coverIndexLocalizedForm omega (Sum.inr i))) ⊆
          halfSpaceSupportBox
            (C.boundaryLower i.1) (C.boundaryUpper i.1))
    (boundaryTargetChart :
      {x : M // x ∈ C.boundaryCenters} -> M)
    (targetLower targetUpper :
      {x : M // x ∈ C.boundaryCenters} -> Fin (n + 1) -> Real)
    (targetSelectedBox :
      forall i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartSelectedBox I (transitionSupportData.targetChart i)
          (boundaryTargetChart i) (P.coverIndexLocalizedForm omega (Sum.inr i))
          (targetLower i) (targetUpper i))
    (orientedCOV :
      forall i : {x : M // x ∈ C.boundaryCenters},
        boundaryChartOrientedChangeOfVariables I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)
          (targetLower i) (targetUpper i)) :
    (Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBulkIntegral I
          (C.boundaryChart i.1) (transitionSupportData.targetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (C.boundaryLower i.1) (C.boundaryUpper i.1)) =
      Finset.sum C.boundaryCoverIndexFinset fun i =>
        projectLocalBoundaryIntegral I
          (transitionSupportData.targetChart i) (boundaryTargetChart i)
          (P.coverIndexLocalizedForm omega (Sum.inr i))
          (targetLower i) (targetUpper i) := by
  classical
  let D :=
    zeroBoundaryPieceFamilyInput
      (I := I) (K := K) (C := C) (P := P) (omega := omega)
      neighborhoodData transitionSupportData hsourceOpen hzero
      boundaryTargetChart targetLower targetUpper targetSelectedBox orientedCOV
  simpa [D, zeroBoundaryPieceFamilyInput,
    ZeroBoundaryPieceFamilyInput.boundaryBulkSum,
    ZeroBoundaryPieceFamilyInput.boundaryBoundarySum,
    ZeroBoundaryPieceFamilyInput.boundaryBulkTerm,
    ZeroBoundaryPieceFamilyInput.boundaryBoundaryTerm] using
    D.boundaryBulkSum_eq_boundaryBoundarySum

end CoverIndexedCompactSupportNeighborhoodDataInfty

end CoverIndexedZeroBoundaryPieceFamily

end Stokes

end
