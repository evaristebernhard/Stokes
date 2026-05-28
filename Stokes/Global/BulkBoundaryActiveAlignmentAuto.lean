import Stokes.Global.BulkCanonicalLocalFactsFromExtDerivAuto
import Stokes.Global.BoundaryUnifiedToControlledM8InputAuto

/-!
# Boundary active-set alignment for canonical bulk routes

`BulkCanonicalLocalFactsFromExtDerivAuto` still needs the small but frequent
alignment

```lean
boundary.activeCharts = selectedPartition.active
```

when the boundary family is the M8 target-image family.  That equality is
already stored in `M8TargetImageInput`, and the controlled/unified boundary
routes both project to such an input.  This file exposes that equality in the
exact shapes consumed by the canonical bulk-local-facts routes.
-/

noncomputable section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators Manifold Topology

namespace Stokes

section BulkBoundaryActiveAlignmentAuto

universe u w b ei eb

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type b}
variable {ExtInteriorPiece : Type ei} {ExtBoundaryPiece : Type eb}
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) -> Real) H}
variable {omega : ManifoldForm I M n}
variable {selectedPartition : SelectedBoxPartitionOfUnity I omega}
variable {orientedBoundaryAtlas : BoundaryChartOrientedAtlas I M}

namespace M8TargetImageInput

variable
    (D :
      M8TargetImageInput I omega selectedPartition orientedBoundaryAtlas
        BoundaryPiece)

/-- Boundary-active alignment in the exact shape expected by the bulk-local
canonical facts route. -/
theorem boundaryActiveAlignment :
    D.targetImages.activeCharts = selectedPartition.active :=
  D.targetImages_active

/-- Canonical bulk local facts whose boundary family is the target-image
boundary family stored in an `M8TargetImageInput`. -/
def toBulkCanonicalLocalFacts
    (localized : LocalizedInteriorM8Fields I omega selectedPartition) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := selectedPartition) (boundary := D.targetImages) localized :=
  SelectedPartitionBulkCanonicalLocalFacts.ofBoundaryActive
    localized D.boundaryActiveAlignment

@[simp]
theorem toBulkCanonicalLocalFacts_boundary_active
    (localized : LocalizedInteriorM8Fields I omega selectedPartition) :
    (D.toBulkCanonicalLocalFacts localized).boundary_active =
      D.boundaryActiveAlignment :=
  rfl

/-- Constructor-indexed bulk route with `boundary_active` projected from the
M8 target-image input. -/
def toBulkCanonicalLocalFactsExtDerivConstructorRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (extDerivConstructor :
      PartitionExtDerivConstructorData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (localizedEventually_eq_selected :
      extDerivConstructor.localizedEventually =
        selectedPartition.bulkSelectedLocalizedEventually
          (BoundaryChart := M) D.targetImages
          omegaSupport_subset_selected)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsExtDerivConstructorRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      D.targetImages localized where
  boundary_active := D.boundaryActiveAlignment
  extDerivConstructor := extDerivConstructor
  omegaSupport_subset_selected := omegaSupport_subset_selected
  localizedEventually_eq_selected := localizedEventually_eq_selected
  measure := measure

@[simp]
theorem toBulkCanonicalLocalFactsExtDerivConstructorRoute_boundary_active
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (extDerivConstructor :
      PartitionExtDerivConstructorData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (localizedEventually_eq_selected :
      extDerivConstructor.localizedEventually =
        selectedPartition.bulkSelectedLocalizedEventually
          (BoundaryChart := M) D.targetImages
          omegaSupport_subset_selected)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    (D.toBulkCanonicalLocalFactsExtDerivConstructorRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      localized extDerivConstructor omegaSupport_subset_selected
      localizedEventually_eq_selected measure).boundary_active =
      D.boundaryActiveAlignment :=
  rfl

/-- Reconstruction-indexed bulk route with `boundary_active` projected from the
M8 target-image input. -/
def toBulkCanonicalLocalFactsReconstructionRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (reconstruction_active :
      selectedPartitionBulkActive selectedPartition D.targetImages =
        reconstruction.activeCharts)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsReconstructionRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      D.targetImages localized where
  boundary_active := D.boundaryActiveAlignment
  reconstruction := reconstruction
  reconstruction_active := reconstruction_active
  omegaSupport_subset_selected := omegaSupport_subset_selected
  measure := measure

@[simp]
theorem toBulkCanonicalLocalFactsReconstructionRoute_boundary_active
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (reconstruction_active :
      selectedPartitionBulkActive selectedPartition D.targetImages =
        reconstruction.activeCharts)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    (D.toBulkCanonicalLocalFactsReconstructionRoute
      (ExtInteriorPiece := ExtInteriorPiece)
      (ExtBoundaryPiece := ExtBoundaryPiece)
      localized reconstruction reconstruction_active
      omegaSupport_subset_selected measure).boundary_active =
      D.boundaryActiveAlignment :=
  rfl

end M8TargetImageInput

namespace BoundaryChartControlledTargetImageFamily.M8ResolvedFields

variable
    {F :
      BoundaryChartControlledTargetImageFamily I omega M BoundaryPiece}
    (D :
      M8ResolvedFields F selectedPartition orientedBoundaryAtlas)

/-- Boundary-active alignment supplied by a controlled-target resolved package. -/
theorem boundaryActiveAlignment :
    D.toM8TargetImageInput.targetImages.activeCharts =
      selectedPartition.active :=
  D.toM8TargetImageInput.boundaryActiveAlignment

/-- Canonical bulk local facts for the boundary family induced by a
controlled-target resolved package. -/
def toBulkCanonicalLocalFacts
    (localized : LocalizedInteriorM8Fields I omega selectedPartition) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := selectedPartition)
      (boundary := D.toM8TargetImageInput.targetImages) localized :=
  D.toM8TargetImageInput.toBulkCanonicalLocalFacts localized

/-- Constructor-indexed bulk route for controlled-target resolved packages. -/
def toBulkCanonicalLocalFactsExtDerivConstructorRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (extDerivConstructor :
      PartitionExtDerivConstructorData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (localizedEventually_eq_selected :
      extDerivConstructor.localizedEventually =
        selectedPartition.bulkSelectedLocalizedEventually
          (BoundaryChart := M) D.toM8TargetImageInput.targetImages
          omegaSupport_subset_selected)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsExtDerivConstructorRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      D.toM8TargetImageInput.targetImages localized :=
  D.toM8TargetImageInput.toBulkCanonicalLocalFactsExtDerivConstructorRoute
    localized extDerivConstructor omegaSupport_subset_selected
    localizedEventually_eq_selected measure

/-- Reconstruction-indexed bulk route for controlled-target resolved packages. -/
def toBulkCanonicalLocalFactsReconstructionRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (reconstruction_active :
      selectedPartitionBulkActive selectedPartition
          D.toM8TargetImageInput.targetImages =
        reconstruction.activeCharts)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsReconstructionRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      D.toM8TargetImageInput.targetImages localized :=
  D.toM8TargetImageInput.toBulkCanonicalLocalFactsReconstructionRoute
    localized reconstruction reconstruction_active
    omegaSupport_subset_selected measure

end BoundaryChartControlledTargetImageFamily.M8ResolvedFields

namespace M8BoundaryControlledTargetInput

variable
    (D :
      M8BoundaryControlledTargetInput I omega selectedPartition
        orientedBoundaryAtlas BoundaryPiece)

/-- Boundary-active alignment supplied by a controlled M8 boundary input. -/
theorem boundaryActiveAlignment :
    D.toM8TargetImageInput.targetImages.activeCharts =
      selectedPartition.active :=
  D.toM8TargetImageInput.boundaryActiveAlignment

/-- Canonical bulk local facts for the boundary family induced by a controlled
M8 boundary input. -/
def toBulkCanonicalLocalFacts
    (localized : LocalizedInteriorM8Fields I omega selectedPartition) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := selectedPartition)
      (boundary := D.toM8TargetImageInput.targetImages) localized :=
  D.toM8TargetImageInput.toBulkCanonicalLocalFacts localized

/-- Constructor-indexed bulk route for controlled M8 boundary inputs. -/
def toBulkCanonicalLocalFactsExtDerivConstructorRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (extDerivConstructor :
      PartitionExtDerivConstructorData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (localizedEventually_eq_selected :
      extDerivConstructor.localizedEventually =
        selectedPartition.bulkSelectedLocalizedEventually
          (BoundaryChart := M) D.toM8TargetImageInput.targetImages
          omegaSupport_subset_selected)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsExtDerivConstructorRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      D.toM8TargetImageInput.targetImages localized :=
  D.toM8TargetImageInput.toBulkCanonicalLocalFactsExtDerivConstructorRoute
    localized extDerivConstructor omegaSupport_subset_selected
    localizedEventually_eq_selected measure

/-- Reconstruction-indexed bulk route for controlled M8 boundary inputs. -/
def toBulkCanonicalLocalFactsReconstructionRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (reconstruction_active :
      selectedPartitionBulkActive selectedPartition
          D.toM8TargetImageInput.targetImages =
        reconstruction.activeCharts)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsReconstructionRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      D.toM8TargetImageInput.targetImages localized :=
  D.toM8TargetImageInput.toBulkCanonicalLocalFactsReconstructionRoute
    localized reconstruction reconstruction_active
    omegaSupport_subset_selected measure

end M8BoundaryControlledTargetInput

namespace BoundarySourceAlignmentUnifiedData

variable
    (U :
      BoundarySourceAlignmentUnifiedData
        (I := I) (omega := omega)
        (selectedPartition := selectedPartition)
        (orientedBoundaryAtlas := orientedBoundaryAtlas)
        (BoundaryPiece := BoundaryPiece))

/-- Boundary-active alignment projected from unified source-alignment data. -/
theorem boundaryActiveAlignment :
    U.toM8TargetImageInput.targetImages.activeCharts =
      selectedPartition.active :=
  U.toM8TargetImageInput.boundaryActiveAlignment

/-- The same alignment through the controlled-target view of unified source
data.  This is useful for callers already routed through
`toM8BoundaryControlledTargetInput`. -/
theorem controlledBoundaryActiveAlignment :
    U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages.activeCharts =
      selectedPartition.active :=
  U.toM8BoundaryControlledTargetInput.boundaryActiveAlignment

/-- Canonical bulk local facts for the unified boundary source package. -/
def toBulkCanonicalLocalFacts
    (localized : LocalizedInteriorM8Fields I omega selectedPartition) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := selectedPartition)
      (boundary := U.toM8TargetImageInput.targetImages) localized :=
  U.toM8TargetImageInput.toBulkCanonicalLocalFacts localized

/-- Controlled-target spelling of the same canonical bulk local facts. -/
def toControlledBulkCanonicalLocalFacts
    (localized : LocalizedInteriorM8Fields I omega selectedPartition) :
    SelectedPartitionBulkCanonicalLocalFacts
      (P := selectedPartition)
      (boundary :=
        U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages)
      localized :=
  U.toM8BoundaryControlledTargetInput.toBulkCanonicalLocalFacts localized

/-- Constructor-indexed bulk route for unified boundary source data. -/
def toBulkCanonicalLocalFactsExtDerivConstructorRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (extDerivConstructor :
      PartitionExtDerivConstructorData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (localizedEventually_eq_selected :
      extDerivConstructor.localizedEventually =
        selectedPartition.bulkSelectedLocalizedEventually
          (BoundaryChart := M) U.toM8TargetImageInput.targetImages
          omegaSupport_subset_selected)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsExtDerivConstructorRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      U.toM8TargetImageInput.targetImages localized :=
  U.toM8TargetImageInput.toBulkCanonicalLocalFactsExtDerivConstructorRoute
    localized extDerivConstructor omegaSupport_subset_selected
    localizedEventually_eq_selected measure

/-- Reconstruction-indexed bulk route for unified boundary source data. -/
def toBulkCanonicalLocalFactsReconstructionRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (reconstruction_active :
      selectedPartitionBulkActive selectedPartition
          U.toM8TargetImageInput.targetImages =
        reconstruction.activeCharts)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsReconstructionRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      U.toM8TargetImageInput.targetImages localized :=
  U.toM8TargetImageInput.toBulkCanonicalLocalFactsReconstructionRoute
    localized reconstruction reconstruction_active
    omegaSupport_subset_selected measure

/-- Controlled-target constructor-indexed bulk route for unified boundary
source data. -/
def toControlledBulkCanonicalLocalFactsExtDerivConstructorRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (extDerivConstructor :
      PartitionExtDerivConstructorData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (localizedEventually_eq_selected :
      extDerivConstructor.localizedEventually =
        selectedPartition.bulkSelectedLocalizedEventually
          (BoundaryChart := M)
          U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages
          omegaSupport_subset_selected)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsExtDerivConstructorRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages
      localized :=
  U.toM8BoundaryControlledTargetInput
    |>.toBulkCanonicalLocalFactsExtDerivConstructorRoute
      localized extDerivConstructor omegaSupport_subset_selected
      localizedEventually_eq_selected measure

/-- Controlled-target reconstruction-indexed bulk route for unified boundary
source data. -/
def toControlledBulkCanonicalLocalFactsReconstructionRoute
    (localized : LocalizedInteriorM8Fields I omega selectedPartition)
    (reconstruction :
      PartitionReconstructionData I omega (M ⊕ M)
        ExtInteriorPiece ExtBoundaryPiece)
    (reconstruction_active :
      selectedPartitionBulkActive selectedPartition
          U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages =
        reconstruction.activeCharts)
    (omegaSupport_subset_selected :
      ManifoldForm.support I omega ⊆ selectedPartition.K)
    (measure : M -> M -> Measure (Fin (n + 1) -> Real)) :
    BulkCanonicalLocalFactsReconstructionRoute
      ExtInteriorPiece ExtBoundaryPiece selectedPartition
      U.toM8BoundaryControlledTargetInput.toM8TargetImageInput.targetImages
      localized :=
  U.toM8BoundaryControlledTargetInput
    |>.toBulkCanonicalLocalFactsReconstructionRoute
      localized reconstruction reconstruction_active
      omegaSupport_subset_selected measure

end BoundarySourceAlignmentUnifiedData

end BulkBoundaryActiveAlignmentAuto

end Stokes

end
