import Stokes.Global.CoverIndexedZeroCompactAmbientThickening
import Stokes.Global.CoverIndexedZeroCompactBoxPartitionRefinement
import Stokes.Global.CoverIndexedZeroCompactFiniteBoxImageControl

/-!
# Refined finite-box image control

This file is the image-control adapter for the box-refined boundary route.
`CoverIndexedBoundaryBoxRefinedPartition` carries many smaller half-space
source boxes under each selected boundary chart.  The existing
`CoverIndexedFiniteBoxImageControlData` API already proves the honest ambient
`MapsTo` statements from closed-preimage, open-preimage, or
`ContinuousOn + image_subset` hypotheses.  Here we package a refined box
family into that finite-control API.

The point is deliberately narrow: no theorem below tries to derive an ambient
half-space `MapsTo` statement from tangential boundary-face data.  The three
routes all require whole-box `Icc` preimage/image hypotheses.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open Set MeasureTheory Filter
open scoped BigOperators Manifold Topology

namespace Stokes

section RefinedImageControl

universe uH uM uB uι

variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {BoundaryPiece : Type uB}
variable {ι : Type uι} [Fintype ι]
variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {K : Set M}
variable {ω : ManifoldForm I M n}
variable {C : CompactSupportChartCoverSelection I K}
variable {P : SupportControlledSelectedPartition C}

/--
A finite external indexing of the refined boundary boxes carried by
`CoverIndexedBoundaryBoxRefinedPartition`.

The partition itself stores boxes as `q ∈ D.boundaryPieces i`.  Downstream image
control is easier to reuse with an arbitrary finite index type, so this records
which boundary chart owns each finite refined box and which piece of that chart
it is.
-/
structure CoverIndexedRefinedBoxImageControlFamily
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)
    (ι : Type uι) [Fintype ι] where
  /-- Boundary chart index owning the refined finite box. -/
  owner : ι → CoverIndexedBoundaryIndex (I := I) C
  /-- Refined piece under the owner boundary chart. -/
  piece : ι → BoundaryPiece
  /-- The selected piece really belongs to the owner's finite refined family. -/
  piece_mem : ∀ r : ι, piece r ∈ D.boundaryPieces (owner r)
  /--
  The refined source chart is synchronized with the owning boundary chart.

  This field is essential: `CoverIndexedFiniteBoxImageControlData` uses the
  cover-selected boundary chart as the source chart.  A refined partition whose
  `sourceChart` is different needs a different image-control package, not this
  adapter.
  -/
  sourceChart_eq_boundaryChart :
    ∀ r : ι, D.sourceChart (owner r) (piece r) = C.boundaryChart (owner r).1
  /-- Lower corner of the target box selected for this refined source box. -/
  targetLower : ι → Fin (n + 1) → Real
  /-- Upper corner of the target box selected for this refined source box. -/
  targetUpper : ι → Fin (n + 1) → Real

namespace CoverIndexedBoundaryBoxRefinedPartition

variable
    (D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece)

/--
Canonical flattened refined-box index.

Callers may use this type directly when they want one finite family containing
all refined boxes, or use `CoverIndexedRefinedBoxImageControlFamily` with a
custom finite index when a later construction already has its own names.
-/
abbrev RefinedBoxIndex : Type (max uM uB) :=
  Σ i : CoverIndexedBoundaryIndex (I := I) C,
    {q : BoundaryPiece // q ∈ D.boundaryPieces i}

/-- Flattened refined-box family from a partition plus target boxes. -/
def flattenedImageControlFamily
    [Fintype D.RefinedBoxIndex]
    (sourceChart_eq_boundaryChart :
      ∀ r : D.RefinedBoxIndex,
        D.sourceChart r.1 r.2.1 = C.boundaryChart r.1.1)
    (targetLower targetUpper :
      D.RefinedBoxIndex → Fin (n + 1) → Real) :
    CoverIndexedRefinedBoxImageControlFamily
      (I := I) (K := K) (C := C) (P := P) (ω := ω)
      D D.RefinedBoxIndex where
  owner := fun r => r.1
  piece := fun r => r.2.1
  piece_mem := fun r => r.2.2
  sourceChart_eq_boundaryChart := sourceChart_eq_boundaryChart
  targetLower := targetLower
  targetUpper := targetUpper

end CoverIndexedBoundaryBoxRefinedPartition

namespace CoverIndexedRefinedBoxImageControlFamily

variable
    {D :
      CoverIndexedBoundaryBoxRefinedPartition
        (I := I) (K := K) C P ω BoundaryPiece}
    (R :
      CoverIndexedRefinedBoxImageControlFamily
        (I := I) (K := K) (C := C) (P := P) (ω := ω)
        D ι)

/-- Source chart of a refined finite box. -/
def sourceChart (r : ι) : M :=
  C.boundaryChart (R.owner r).1

/-- Source chart stored in the refined partition before synchronizing with the cover chart. -/
def refinedSourceChart (r : ι) : M :=
  D.sourceChart (R.owner r) (R.piece r)

/-- The refined source chart agrees with the cover-selected boundary chart. -/
theorem refinedSourceChart_eq_sourceChart (r : ι) :
    R.refinedSourceChart r = R.sourceChart r :=
  R.sourceChart_eq_boundaryChart r

/-- Target chart of a refined finite box. -/
def targetChart (r : ι) : M :=
  D.targetChart (R.owner r) (R.piece r)

/-- Source lower corner of a refined finite box. -/
def sourceLower (r : ι) : Fin (n + 1) → Real :=
  D.lower (R.owner r) (R.piece r)

/-- Source upper corner of a refined finite box. -/
def sourceUpper (r : ι) : Fin (n + 1) → Real :=
  D.upper (R.owner r) (R.piece r)

/-- Ambient chart transition of a refined finite box. -/
def chartTransition (r : ι) :
    (Fin (n + 1) → Real) → (Fin (n + 1) → Real) :=
  ManifoldForm.chartTransition I (R.sourceChart r) (R.targetChart r)

/--
The refined box family as the existing finite image-control data.

This is the central adapter of the file: all following image-control theorems
delegate to `CoverIndexedFiniteBoxImageControlData`.
-/
def toFiniteBoxImageControlData :
    CoverIndexedFiniteBoxImageControlData
      (I := I) (K := K) C ι where
  owner := R.owner
  targetChart := R.targetChart
  sourceLower := R.sourceLower
  sourceUpper := R.sourceUpper
  targetLower := R.targetLower
  targetUpper := R.targetUpper

@[simp]
theorem toFiniteBoxImageControlData_owner :
    (R.toFiniteBoxImageControlData
      (I := I) (K := K) (C := C)).owner = R.owner :=
  rfl

@[simp]
theorem toFiniteBoxImageControlData_targetChart :
    (R.toFiniteBoxImageControlData
      (I := I) (K := K) (C := C)).targetChart = R.targetChart :=
  rfl

@[simp]
theorem toFiniteBoxImageControlData_sourceLower :
    (R.toFiniteBoxImageControlData
      (I := I) (K := K) (C := C)).sourceLower = R.sourceLower :=
  rfl

@[simp]
theorem toFiniteBoxImageControlData_sourceUpper :
    (R.toFiniteBoxImageControlData
      (I := I) (K := K) (C := C)).sourceUpper = R.sourceUpper :=
  rfl

@[simp]
theorem toFiniteBoxImageControlData_targetLower :
    (R.toFiniteBoxImageControlData
      (I := I) (K := K) (C := C)).targetLower = R.targetLower :=
  rfl

@[simp]
theorem toFiniteBoxImageControlData_targetUpper :
    (R.toFiniteBoxImageControlData
      (I := I) (K := K) (C := C)).targetUpper = R.targetUpper :=
  rfl

@[simp]
theorem toFiniteBoxImageControlData_sourceChart
    (r : ι) :
    (R.toFiniteBoxImageControlData
      (I := I) (K := K) (C := C)).sourceChart r =
      R.sourceChart r :=
  rfl

@[simp]
theorem toFiniteBoxImageControlData_chartTransition
    (r : ι) :
    (R.toFiniteBoxImageControlData
      (I := I) (K := K) (C := C)).chartTransition r =
      R.chartTransition r :=
  rfl

/-- Endpoint-shaped ambient `MapsTo` field for all refined boxes. -/
def ChartTransitionMapsToField : Prop :=
  (R.toFiniteBoxImageControlData
    (I := I) (K := K) (C := C)).ChartTransitionMapsToField

/-- Closed-preimage shrink field for all refined boxes. -/
def ClosedPreimageShrinkField : Prop :=
  (R.toFiniteBoxImageControlData
    (I := I) (K := K) (C := C)).ClosedPreimageShrinkField

/-- Open-preimage shrink field for all refined boxes. -/
def OpenPreimageShrinkField
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real)) : Prop :=
  (R.toFiniteBoxImageControlData
    (I := I) (K := K) (C := C)).OpenPreimageShrinkField
      sourceOpen targetOpen

/-- Image-containment field through target opens for all refined boxes. -/
def ImageSubsetTargetOpenField
    (targetOpen : ι → Set (Fin (n + 1) → Real)) : Prop :=
  (R.toFiniteBoxImageControlData
    (I := I) (K := K) (C := C)).ImageSubsetTargetOpenField targetOpen

/-- Target opens sit inside the refined target closed boxes. -/
def TargetOpenSubsetIccField
    (targetOpen : ι → Set (Fin (n + 1) → Real)) : Prop :=
  (R.toFiniteBoxImageControlData
    (I := I) (K := K) (C := C)).TargetOpenSubsetIccField targetOpen

/--
Closed-preimage route for refined image control.

This requires whole source `Icc` containment in the preimage of the target
closed box, hence proves the ambient half-space `MapsTo` on each refined box.
-/
theorem chartTransitionMapsToField_of_refined_closedPreimageShrink
    (hpre : R.ClosedPreimageShrinkField) :
    R.ChartTransitionMapsToField := by
  exact
    CoverIndexedFiniteBoxImageControlData.chartTransition_mapsTo_of_closed_preimage_shrink
      (R.toFiniteBoxImageControlData
        (I := I) (K := K) (C := C))
      hpre

/--
Open-preimage route for refined image control.

The source opens must lie in the source chart target and chart overlap; this is
the honest ambient condition needed for whole half-space boxes.
-/
theorem chartTransitionMapsToField_of_refined_openPreimageShrink
    [IsManifold I ⊤ M]
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real))
    (hUopen : ∀ r : ι, IsOpen (sourceOpen r))
    (hUtarget :
      ∀ r : ι, sourceOpen r ⊆ (extChartAt I (R.sourceChart r)).target)
    (hUoverlap :
      ∀ r : ι,
        sourceOpen r ⊆
          ManifoldForm.chartOverlap I (R.sourceChart r) (R.targetChart r))
    (hVopen : ∀ r : ι, IsOpen (targetOpen r))
    (hVsubset : R.TargetOpenSubsetIccField targetOpen)
    (hbox : R.OpenPreimageShrinkField sourceOpen targetOpen) :
    R.ChartTransitionMapsToField := by
  exact
    CoverIndexedFiniteBoxImageControlData.chartTransition_mapsTo_of_open_preimage_shrink
      (R.toFiniteBoxImageControlData
        (I := I) (K := K) (C := C))
      sourceOpen targetOpen hUopen hUtarget hUoverlap
      hVopen hVsubset hbox

/--
Continuity and image-subset route for refined image control.

The input controls the image of each whole refined closed source box inside a
target open set; the theorem then returns the ambient `MapsTo` field for the
corresponding half-space support boxes.
-/
theorem chartTransitionMapsToField_of_refined_continuousOn_image_subset
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real))
    (hUopen : ∀ r : ι, IsOpen (sourceOpen r))
    (hcont :
      ∀ r : ι, ContinuousOn (R.chartTransition r) (sourceOpen r))
    (hVopen : ∀ r : ι, IsOpen (targetOpen r))
    (hVsubset : R.TargetOpenSubsetIccField targetOpen)
    (hIcc_source :
      ∀ r : ι, Icc (R.sourceLower r) (R.sourceUpper r) ⊆ sourceOpen r)
    (himage : R.ImageSubsetTargetOpenField targetOpen) :
    R.ChartTransitionMapsToField := by
  exact
    CoverIndexedFiniteBoxImageControlData.chartTransition_mapsTo_of_continuousOn_image_subset
      (R.toFiniteBoxImageControlData
        (I := I) (K := K) (C := C))
      sourceOpen targetOpen hUopen hcont hVopen hVsubset
      hIcc_source himage

/--
Closed-preimage route, expanded as an ordinary `∀ r, MapsTo ...` statement for
callers that do not want to unfold `ChartTransitionMapsToField` themselves.
-/
theorem refined_mapsTo_of_closedPreimageShrink
    (hpre : R.ClosedPreimageShrinkField) :
    ∀ r : ι,
      MapsTo (R.chartTransition r)
        (halfSpaceSupportBox (R.sourceLower r) (R.sourceUpper r))
        (Icc (R.targetLower r) (R.targetUpper r)) :=
  R.chartTransitionMapsToField_of_refined_closedPreimageShrink
    (I := I) (K := K) (C := C) hpre

/--
Open-preimage route, expanded as an ordinary `∀ r, MapsTo ...` statement.
-/
theorem refined_mapsTo_of_openPreimageShrink
    [IsManifold I ⊤ M]
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real))
    (hUopen : ∀ r : ι, IsOpen (sourceOpen r))
    (hUtarget :
      ∀ r : ι, sourceOpen r ⊆ (extChartAt I (R.sourceChart r)).target)
    (hUoverlap :
      ∀ r : ι,
        sourceOpen r ⊆
          ManifoldForm.chartOverlap I (R.sourceChart r) (R.targetChart r))
    (hVopen : ∀ r : ι, IsOpen (targetOpen r))
    (hVsubset : R.TargetOpenSubsetIccField targetOpen)
    (hbox : R.OpenPreimageShrinkField sourceOpen targetOpen) :
    ∀ r : ι,
      MapsTo (R.chartTransition r)
        (halfSpaceSupportBox (R.sourceLower r) (R.sourceUpper r))
        (Icc (R.targetLower r) (R.targetUpper r)) :=
  R.chartTransitionMapsToField_of_refined_openPreimageShrink
    (I := I) (K := K) (C := C)
    sourceOpen targetOpen hUopen hUtarget hUoverlap
    hVopen hVsubset hbox

/--
Continuity/image-subset route, expanded as an ordinary `∀ r, MapsTo ...`
statement.
-/
theorem refined_mapsTo_of_continuousOn_image_subset
    (sourceOpen targetOpen : ι → Set (Fin (n + 1) → Real))
    (hUopen : ∀ r : ι, IsOpen (sourceOpen r))
    (hcont :
      ∀ r : ι, ContinuousOn (R.chartTransition r) (sourceOpen r))
    (hVopen : ∀ r : ι, IsOpen (targetOpen r))
    (hVsubset : R.TargetOpenSubsetIccField targetOpen)
    (hIcc_source :
      ∀ r : ι, Icc (R.sourceLower r) (R.sourceUpper r) ⊆ sourceOpen r)
    (himage : R.ImageSubsetTargetOpenField targetOpen) :
    ∀ r : ι,
      MapsTo (R.chartTransition r)
        (halfSpaceSupportBox (R.sourceLower r) (R.sourceUpper r))
        (Icc (R.targetLower r) (R.targetUpper r)) :=
  R.chartTransitionMapsToField_of_refined_continuousOn_image_subset
    (I := I) (K := K) (C := C)
    sourceOpen targetOpen hUopen hcont hVopen hVsubset
    hIcc_source himage

end CoverIndexedRefinedBoxImageControlFamily

end RefinedImageControl

end Stokes

end
