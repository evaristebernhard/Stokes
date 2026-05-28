import Stokes.Global.SupportControlledSelectedPartition
import Stokes.Global.CompactSupportAssignedBoxFields

/-!
# Interior support-controlled selected partitions to assigned boxes

This file is the interior bridge from a support-controlled selected chart-box
partition to the coordinate support hypotheses consumed by
`InteriorAssignedBoxSupport`.

The support-controlled selected partition is indexed by the finite mixed cover
indices.  Downstream assigned-box APIs are indexed by the selected chart label
itself.  The theorems below keep that reindexing honest: callers provide the
chart-coordinate carrier hypotheses and the alignment between active selected
chart labels and interior cover indices.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section InteriorSupportControlledAssignedBox

set_option linter.unusedSectionVars false

universe u w b

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {K : Set M}
variable {omega : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}

/--
Interior coordinate coefficient support obtained from a support-controlled
selected partition.

This is a named wrapper around
`SupportControlledSelectedPartition.interior_tsupport_inter_subset_assigned`:
the extra hypotheses are exactly the chart-coordinate carrier facts needed to
move from manifold-side support control to coordinate support control.
-/
theorem interior_coefficient_tsupport_subset_assignedBox_of_supportControlledPartition
    (supportPartition : SupportControlledSelectedPartition C)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : Set (Fin (n + 1) -> Real)}
    (hcoordK :
      forall y, y ∈ coordSupport ->
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport ⊆ (extChartAt I (C.interiorChart i.1)).target)
    (htransitionCoeffSupport :
      forall y,
        y ∈ tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.interiorChart i.1) (C.interiorChart i.1)
              (supportPartition.partition (Sum.inl i))) ->
          (extChartAt I (C.interiorChart i.1)).symm y ∈
            tsupport (supportPartition.partition (Sum.inl i))) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (supportPartition.partition (Sum.inl i))) ∩ coordSupport ⊆
      boxInteriorSupportBox (C.interiorLower i.1) (C.interiorUpper i.1) :=
  supportPartition
    |>.interior_transitionCoefficient_inter_coordSupport_subset_box
      (i := i) hcoordK hcoordTarget htransitionCoeffSupport

/--
Selected-partition form of the preceding coefficient support bridge, for the
case where an active selected chart label is definitionally aligned with an
interior selected cover index.
-/
theorem interior_selected_coefficient_tsupport_subset_assignedBox_of_supportControlledPartition
    (supportPartition : SupportControlledSelectedPartition C)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    (i : {x : M // x ∈ C.interiorCenters})
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hpartition :
      selectedPartition.partition (C.interiorChart i.1) =
        supportPartition.partition (Sum.inl i))
    (hlower :
      selectedPartition.lower (C.interiorChart i.1) = C.interiorLower i.1)
    (hupper :
      selectedPartition.upper (C.interiorChart i.1) = C.interiorUpper i.1)
    (hcoordK :
      forall y, y ∈ coordSupport (C.interiorChart i.1) ->
        (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      coordSupport (C.interiorChart i.1) ⊆
        (extChartAt I (C.interiorChart i.1)).target)
    (htransitionCoeffSupport :
      forall y,
        y ∈ tsupport
            (ManifoldForm.transitionCoefficientInChart I
              (C.interiorChart i.1) (C.interiorChart i.1)
              (supportPartition.partition (Sum.inl i))) ->
          (extChartAt I (C.interiorChart i.1)).symm y ∈
            tsupport (supportPartition.partition (Sum.inl i))) :
    tsupport
          (ManifoldForm.transitionCoefficientInChart I
            (C.interiorChart i.1) (C.interiorChart i.1)
            (selectedPartition.partition (C.interiorChart i.1))) ∩
        coordSupport (C.interiorChart i.1) ⊆
      boxInteriorSupportBox
        (selectedPartition.lower (C.interiorChart i.1))
        (selectedPartition.upper (C.interiorChart i.1)) := by
  simpa [hpartition, hlower, hupper] using
    interior_coefficient_tsupport_subset_assignedBox_of_supportControlledPartition
      (I := I) (C := C) supportPartition i
      (coordSupport := coordSupport (C.interiorChart i.1))
      hcoordK hcoordTarget htransitionCoeffSupport

/--
Build the exact audit fields consumed by `interiorAssignedBox_from_fields` from
a support-controlled selected partition, assuming every active selected chart
label comes from an interior selected cover index and the selected partition is
aligned with that cover index.
-/
theorem interior_assignedBox_fields_of_supportControlledPartition
    (supportPartition : SupportControlledSelectedPartition C)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hactiveInterior :
      forall x, x ∈ selectedPartition.active ->
        exists i : {x : M // x ∈ C.interiorCenters},
          x = C.interiorChart i.1)
    (hpartition :
      forall i : {x : M // x ∈ C.interiorCenters},
        selectedPartition.partition (C.interiorChart i.1) =
          supportPartition.partition (Sum.inl i))
    (hlower :
      forall i : {x : M // x ∈ C.interiorCenters},
        selectedPartition.lower (C.interiorChart i.1) = C.interiorLower i.1)
    (hupper :
      forall i : {x : M // x ∈ C.interiorCenters},
        selectedPartition.upper (C.interiorChart i.1) = C.interiorUpper i.1)
    (hcoordK :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y, y ∈ coordSupport (C.interiorChart i.1) ->
          (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      forall i : {x : M // x ∈ C.interiorCenters},
        coordSupport (C.interiorChart i.1) ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (htransitionCoeffSupport :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y,
          y ∈ tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (C.interiorChart i.1) (C.interiorChart i.1)
                (supportPartition.partition (Sum.inl i))) ->
            (extChartAt I (C.interiorChart i.1)).symm y ∈
              tsupport (supportPartition.partition (Sum.inl i))) :
    InteriorAssignedBoxFields
      selectedPartition coordSupport := by
  refine ⟨hbase, ?_⟩
  intro x hx
  rcases hactiveInterior x hx with ⟨i, rfl⟩
  exact
    interior_selected_coefficient_tsupport_subset_assignedBox_of_supportControlledPartition
      (I := I) (C := C) supportPartition selectedPartition i
      (coordSupport := coordSupport)
      (hpartition i) (hlower i) (hupper i)
      (hcoordK i) (hcoordTarget i) (htransitionCoeffSupport i)

/--
Direct assigned-box support conclusion from a support-controlled selected
partition, via the audit fields wrapper.
-/
theorem interiorAssignedBox_from_supportControlledPartition
    (supportPartition : SupportControlledSelectedPartition C)
    (selectedPartition : SelectedBoxPartitionOfUnity I omega)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hactiveInterior :
      forall x, x ∈ selectedPartition.active ->
        exists i : {x : M // x ∈ C.interiorCenters},
          x = C.interiorChart i.1)
    (hpartition :
      forall i : {x : M // x ∈ C.interiorCenters},
        selectedPartition.partition (C.interiorChart i.1) =
          supportPartition.partition (Sum.inl i))
    (hlower :
      forall i : {x : M // x ∈ C.interiorCenters},
        selectedPartition.lower (C.interiorChart i.1) = C.interiorLower i.1)
    (hupper :
      forall i : {x : M // x ∈ C.interiorCenters},
        selectedPartition.upper (C.interiorChart i.1) = C.interiorUpper i.1)
    (hcoordK :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y, y ∈ coordSupport (C.interiorChart i.1) ->
          (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      forall i : {x : M // x ∈ C.interiorCenters},
        coordSupport (C.interiorChart i.1) ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (htransitionCoeffSupport :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y,
          y ∈ tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (C.interiorChart i.1) (C.interiorChart i.1)
                (supportPartition.partition (Sum.inl i))) ->
            (extChartAt I (C.interiorChart i.1)).symm y ∈
              tsupport (supportPartition.partition (Sum.inl i)))
    {x : M} (hx : x ∈ selectedPartition.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x x
          (ManifoldForm.localizedForm I
            (selectedPartition.partition x) omega)) ⊆
      boxInteriorSupportBox
        (selectedPartition.lower x) (selectedPartition.upper x) :=
  interiorAssignedBox_from_fields
    (I := I) (omega := omega) selectedPartition
    (interior_assignedBox_fields_of_supportControlledPartition
      (I := I) (C := C) supportPartition selectedPartition
      hbase hactiveInterior hpartition hlower hupper hcoordK hcoordTarget
      htransitionCoeffSupport)
    hx

/--
M8 localized-piece coefficient support from a support-controlled selected
partition.  This is the same bridge as the audit-field theorem, but its target
box is the localized interior piece stored in the M8 measure-localization data.
-/
theorem interior_m8_coefficient_tsupport_subset_assignedBox_of_supportControlledPartition
    (supportPartition : SupportControlledSelectedPartition C)
    {selectedPartition : SelectedBoxPartitionOfUnity I omega}
    {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages}
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hactiveInterior :
      forall x, x ∈ selectedPartition.active ->
        exists i : {x : M // x ∈ C.interiorCenters},
          x = C.interiorChart i.1)
    (hpartition :
      forall i : {x : M // x ∈ C.interiorCenters},
        selectedPartition.partition (C.interiorChart i.1) =
          supportPartition.partition (Sum.inl i))
    (hpieceLower :
      forall i : {x : M // x ∈ C.interiorCenters},
        (measureLocalization.localizedInterior.piece
          (C.interiorChart i.1)).lowerCorner = C.interiorLower i.1)
    (hpieceUpper :
      forall i : {x : M // x ∈ C.interiorCenters},
        (measureLocalization.localizedInterior.piece
          (C.interiorChart i.1)).upperCorner = C.interiorUpper i.1)
    (hcoordK :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y, y ∈ coordSupport (C.interiorChart i.1) ->
          (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      forall i : {x : M // x ∈ C.interiorCenters},
        coordSupport (C.interiorChart i.1) ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (htransitionCoeffSupport :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y,
          y ∈ tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (C.interiorChart i.1) (C.interiorChart i.1)
                (supportPartition.partition (Sum.inl i))) ->
            (extChartAt I (C.interiorChart i.1)).symm y ∈
              tsupport (supportPartition.partition (Sum.inl i))) :
    forall x, x ∈ selectedPartition.active ->
      tsupport
          (ManifoldForm.transitionCoefficientInChart I x x
            (selectedPartition.partition x)) ∩ coordSupport x ⊆
        boxInteriorSupportBox
          (measureLocalization.localizedInterior.piece x).lowerCorner
          (measureLocalization.localizedInterior.piece x).upperCorner := by
  intro x hx
  rcases hactiveInterior x hx with ⟨i, rfl⟩
  simpa [hpartition i, hpieceLower i, hpieceUpper i] using
    interior_coefficient_tsupport_subset_assignedBox_of_supportControlledPartition
      (I := I) (C := C) supportPartition i
      (coordSupport := coordSupport (C.interiorChart i.1))
      (hcoordK i) (hcoordTarget i) (htransitionCoeffSupport i)

/--
Construct M8 artificial-face fields directly from support-controlled selected
partition data and the interior cover-to-piece alignment.
-/
def m8ArtificialFaceFields_of_supportControlledPartition
    (supportPartition : SupportControlledSelectedPartition C)
    {selectedPartition : SelectedBoxPartitionOfUnity I omega}
    {targetImages : BoundaryPieceFamilyInput I omega M BoundaryPiece}
    {measureLocalization :
      M8MeasureLocalizationData I omega selectedPartition targetImages}
    (localizedPieceAlignment :
      LocalizedInteriorPieceAlignment selectedPartition targetImages
        measureLocalization)
    {coordSupport : M -> Set (Fin (n + 1) -> Real)}
    (hbase :
      forall x, x ∈ selectedPartition.active ->
        tsupport (ManifoldForm.transitionPullbackInChart I x x omega) ⊆
          coordSupport x)
    (hactiveInterior :
      forall x, x ∈ selectedPartition.active ->
        exists i : {x : M // x ∈ C.interiorCenters},
          x = C.interiorChart i.1)
    (hpartition :
      forall i : {x : M // x ∈ C.interiorCenters},
        selectedPartition.partition (C.interiorChart i.1) =
          supportPartition.partition (Sum.inl i))
    (hpieceLower :
      forall i : {x : M // x ∈ C.interiorCenters},
        (measureLocalization.localizedInterior.piece
          (C.interiorChart i.1)).lowerCorner = C.interiorLower i.1)
    (hpieceUpper :
      forall i : {x : M // x ∈ C.interiorCenters},
        (measureLocalization.localizedInterior.piece
          (C.interiorChart i.1)).upperCorner = C.interiorUpper i.1)
    (hcoordK :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y, y ∈ coordSupport (C.interiorChart i.1) ->
          (extChartAt I (C.interiorChart i.1)).symm y ∈ K)
    (hcoordTarget :
      forall i : {x : M // x ∈ C.interiorCenters},
        coordSupport (C.interiorChart i.1) ⊆
          (extChartAt I (C.interiorChart i.1)).target)
    (htransitionCoeffSupport :
      forall i : {x : M // x ∈ C.interiorCenters},
        forall y,
          y ∈ tsupport
              (ManifoldForm.transitionCoefficientInChart I
                (C.interiorChart i.1) (C.interiorChart i.1)
                (supportPartition.partition (Sum.inl i))) ->
            (extChartAt I (C.interiorChart i.1)).symm y ∈
              tsupport (supportPartition.partition (Sum.inl i))) :
    M8ArtificialFaceFields I omega BoundaryPiece selectedPartition
      targetImages measureLocalization :=
  M8ArtificialFaceFields.ofAssignedInteriorBoxSupport
    (BoundaryPiece := BoundaryPiece)
    (selectedPartition := selectedPartition)
    (targetImages := targetImages)
    (measureLocalization := measureLocalization)
    localizedPieceAlignment
    hbase
    (interior_m8_coefficient_tsupport_subset_assignedBox_of_supportControlledPartition
      (I := I) (C := C) supportPartition
      hactiveInterior hpartition hpieceLower hpieceUpper
      hcoordK hcoordTarget htransitionCoeffSupport)

end InteriorSupportControlledAssignedBox

end Stokes

end
