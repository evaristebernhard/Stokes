import Stokes.Global.CoverIndexedLocalStokes
import Stokes.Global.CoverIndexedZeroCompactRefinedLocalStokes
import Stokes.Global.CoverIndexedZeroRelativeSource
import Stokes.BoundaryChart.RelativeFiniteBoxLocalStokes

/-!
# Relative chartwise-smooth adapters for cover-indexed local Stokes

This file is a thin compatibility layer for the boundary-compatible route.
The available lower layer already proves the refined local Stokes sum from
ordinary open smoothness neighborhoods.  Here we expose the requested
`relativeChartwiseSmooth` names by deriving the base-form smoothness from
chartwise smoothness together with the local target/overlap containments of
each chosen neighborhood.

No raw represented-Stokes files are touched here.
-/

noncomputable section

set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section CoverIndexedRelativeLocalStokes

universe u w c b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type c} {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Cover-indexed boundary half-space local Stokes from chartwise smoothness of the
base form and relative target/overlap control of every smoothness neighborhood.

This is the cover-index adapter for the boundary route: callers provide
coefficient smoothness in transition coordinates, while the base-form
transition smoothness is generated from `ManifoldForm.ChartwiseSmooth`.
-/
theorem coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_relativeChartwiseSmooth
    [IsManifold I ⊤ M]
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
          Icc (lower i q) (upper i q) ⊆
            boundaryChartDomain I (sourceChart i q) (targetChart i q))
    (hU :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i -> IsOpen (U i q))
    (hUbox :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          Icc (lower i q) (upper i q) ⊆ U i q)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUtarget :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          U i q ⊆ (extChartAt I (sourceChart i q)).target)
    (hUoverlap :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          U i q ⊆
            ManifoldForm.chartOverlap I (sourceChart i q) (targetChart i q))
    (hrhoU :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionCoefficientInChart I
              (sourceChart i q) (targetChart i q) (rho i q)) (U i q)) :
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
    coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_contDiffOn
      (I := I) (omega := omega)
      active boundaryPieces sourceChart targetChart rho K lower upper U
      hK hhalf hbase ha0 hle hcoeff hdomain hU hUbox hrhoU
      (by
        intro i hi q hq
        exact
          ManifoldForm.contDiffOn_transitionPullbackInChart_of_chartwiseSmooth_refined
            (I := I) (x0 := sourceChart i q) (x1 := targetChart i q)
            (omega := omega) (U := U i q) homega
            (hUtarget i hi q hq) (hUoverlap i hi q hq))

end CoverIndexedRelativeLocalStokes

section CoverIndexedInteriorFieldsLocalStokes

universe u w c b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {ι : Type c} {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}

/--
Cover-indexed boundary half-space local Stokes from the exact interior-box
fields needed by the Euclidean box theorem.

This is the first finite-sum entry point in this layer that does not mention an
ambient-open smoothness neighborhood `U`.
-/
theorem coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_interiorFields
    (active : Finset ι)
    (boundaryPieces : ι -> Finset BoundaryPiece)
    (sourceChart targetChart : ι -> BoundaryPiece -> M)
    (rho : ι -> BoundaryPiece -> M -> Real)
    (K : ι -> BoundaryPiece -> Set (Fin (n + 1) -> Real))
    (lower upper : ι -> BoundaryPiece -> Fin (n + 1) -> Real)
    (hbase :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          tsupport
              (ManifoldForm.transitionPullbackInChart I
                (sourceChart i q) (targetChart i q) omega) ⊆
            K i q)
    (hcoeff :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (sourceChart i q) (targetChart i q) (rho i q)) ∩ K i q ⊆
            halfSpaceSupportBox (lower i q) (upper i q))
    (hfields :
      forall i, i ∈ active ->
        forall q, q ∈ boundaryPieces i ->
          HalfSpaceBoxInteriorStokesFields
            (ManifoldForm.transitionPullbackInChart I
              (sourceChart i q) (targetChart i q)
              (ManifoldForm.localizedForm I (rho i q) omega))
            (lower i q) (upper i q)) :
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
          boundaryAssignedBox_projectLocalStokes_of_interiorFields
            (I := I) (x0 := sourceChart i q) (x1 := targetChart i q)
            (ρ := rho i q) (ω := omega)
            (K := K i q) (a := lower i q) (b := upper i q)
            (hbase i hi q hq) (hcoeff i hi q hq) (hfields i hi q hq))

end CoverIndexedInteriorFieldsLocalStokes

section RefinedRelativeLocalStokes

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

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
  (D :
    CoverIndexedBoundaryBoxRefinedPartition
      (I := I) (K := K) C P omega BoundaryPiece)
  {U :
    CoverIndexedBoundaryIndex (I := I) C -> BoundaryPiece ->
      Set (Fin (n + 1) -> Real)}

/--
Refined partition version of
`coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_relativeChartwiseSmooth`.

The source/target neighborhood containments are the relative chart data; the
coefficient smoothness remains an explicit input because refined coefficients
are supplied by the partition-refinement layer.
-/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_relativeChartwiseSmooth
    [IsManifold I ⊤ M]
    (hU :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i -> IsOpen (U i q))
    (hUbox :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          Icc (D.lower i q) (D.upper i q) ⊆ U i q)
    (homega : ManifoldForm.ChartwiseSmooth I omega)
    (hUtarget :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆ (extChartAt I (D.sourceChart i q)).target)
    (hUoverlap :
      forall i q, q ∈ D.boundaryPieces i ->
        U i q ⊆
          ManifoldForm.chartOverlap I (D.sourceChart i q) (D.targetChart i q))
    (hrhoU :
      forall i, i ∈ (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) ->
        forall q, q ∈ D.boundaryPieces i ->
          ContDiffOn Real ⊤
            (ManifoldForm.transitionCoefficientInChart I
              (D.sourceChart i q) (D.targetChart i q) (D.coefficient i q))
            (U i q)) :
    (Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBulkTerm i q) =
      Finset.sum (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)) fun i =>
        Finset.sum (D.boundaryPieces i) fun q =>
          D.localBoundaryTerm i q := by
  classical
  exact
    coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_relativeChartwiseSmooth
      (I := I) (omega := omega)
      (active := (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)))
      (boundaryPieces := D.boundaryPieces)
      (sourceChart := D.sourceChart) (targetChart := D.targetChart)
      (rho := D.coefficient) (K := D.coordSupport)
      (lower := D.lower) (upper := D.upper) (U := U)
      (fun i _hi q hq => D.isCompact_coordSupport i q hq)
      (fun i _hi q hq => D.coordSupport_subset_upperHalfSpace i q hq)
      (fun i _hi q hq => D.base_tsupport_subset_coordSupport i q hq)
      (fun i _hi q hq => D.lower_zero i q hq)
      (fun i _hi q hq => D.lower_le_upper i q hq)
      (fun i _hi q hq =>
        D.coefficient_tsupport_inter_coordSupport_subset_halfSpaceSupportBox i q hq)
      (fun i _hi q hq => D.Icc_subset_boundaryChartDomain i q hq)
      hU hUbox homega
      (fun i _hi q hq => hUtarget i q hq)
      (fun i _hi q hq => hUoverlap i q hq)
      hrhoU

/--
Refined partition version of the interior-fields local Stokes route.  This is
the theorem intended for the raw represented-Stokes relative entry point: it no
longer takes an ambient-open chart-target neighborhood.
-/
theorem boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_interiorFields
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
    coverIndexed_boundaryHalfSpaceBulkSum_eq_trueBoundarySum_of_interiorFields
      (I := I) (omega := omega)
      (active := (Finset.univ : Finset (CoverIndexedBoundaryIndex (I := I) C)))
      (boundaryPieces := D.boundaryPieces)
      (sourceChart := D.sourceChart) (targetChart := D.targetChart)
      (rho := D.coefficient) (K := D.coordSupport)
      (lower := D.lower) (upper := D.upper)
      (fun i _hi q hq => D.base_tsupport_subset_coordSupport i q hq)
      (fun i _hi q hq =>
        D.coefficient_tsupport_inter_coordSupport_subset_halfSpaceSupportBox i q hq)
      hfields

end CoverIndexedBoundaryBoxRefinedPartition

end RefinedRelativeLocalStokes

end Stokes

end
