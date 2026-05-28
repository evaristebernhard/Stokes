import Stokes.BoundaryChart.TargetImageFieldReduction

/-!
# Target-image families from local-inverse data

This file is a pure `BoundaryChart` constructor layer.  It gives downstream
global code a more natural way to build
`BoundaryChartTargetImageResolvedFamily` from the local-inverse and compact-image
packages already selected in the boundary chart layer.

The resolved-family shape uses a proof-free target-box function on all pieces.
For compact covers, only active pieces carry geometric data, so the constructors
below take an explicit inactive-piece default and prove that active pieces reduce
to the compact/local-inverse cover selection.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w c p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

namespace BoundaryChartSelectedBoxCOVFamilyData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Forget the COV-facing wrapper down to the proof-free resolved target-image
family.  This is the most direct constructor when the local-inverse target boxes
have already been materialized as `targetBox`.
-/
def toTargetImageResolvedFamily
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece where
  activeCharts := data.activeCharts
  localPieces := data.localPieces
  sourceChart := data.sourceChart
  boundarySourceChart := data.boundarySourceChart
  boundaryTargetChart := data.boundaryTargetChart
  sourceLowerCorner := data.sourceLowerCorner
  sourceUpperCorner := data.sourceUpperCorner
  sourceSelectedBox := data.sourceSelectedBox
  targetBox := data.targetBox
  targetSelectedBox := data.targetSelectedBox

/-- The resolved-family projection back to COV data is definitionally unchanged. -/
theorem toTargetImageResolvedFamily_toSelectedBoxCOVFamilyData
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece) :
    data.toTargetImageResolvedFamily.toSelectedBoxCOVFamilyData = data :=
  rfl

/-- The resolved-family constructor preserves the proof-free target box. -/
theorem toTargetImageResolvedFamily_targetBox
    (data : BoundaryChartSelectedBoxCOVFamilyData I ω Chart Piece)
    (x : Chart) (q : Piece) :
    data.toTargetImageResolvedFamily.targetBox x q = data.targetBox x q :=
  rfl

end BoundaryChartSelectedBoxCOVFamilyData

namespace BoundaryChartTargetBoxFamilySelection

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Resolve a proof-indexed target-box family using a proof-free representative.

Compared with `BoundaryChartTargetImageResolvedFamily.ofTargetBoxFamilySelection`,
the selected target box is stated directly in terms of the supplied proof-free
`targetBox`, which is usually how local-inverse constructors produce it.
-/
def toTargetImageResolvedFamilyOfTargetBox
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (boundaryTargetChart : Chart → Piece → M)
    (targetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (F.sourceChart x q)
          (F.boundarySourceChart x q)
          (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
    (targetSelectedBox :
      ∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          boundaryChartSelectedBox I (F.boundarySourceChart x q)
            (boundaryTargetChart x q) ω
            ((targetBox x q).lowerCorner) ((targetBox x q).upperCorner)) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece where
  activeCharts := F.activeCharts
  localPieces := F.localPieces
  sourceChart := F.sourceChart
  boundarySourceChart := F.boundarySourceChart
  boundaryTargetChart := boundaryTargetChart
  sourceLowerCorner := F.sourceLowerCorner
  sourceUpperCorner := F.sourceUpperCorner
  sourceSelectedBox := F.sourceSelectedBox
  targetBox := targetBox
  targetSelectedBox := targetSelectedBox

/-- Active target lower corners agree with the original proof-indexed selection. -/
theorem toTargetImageResolvedFamilyOfTargetBox_targetLowerCorner
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (boundaryTargetChart : Chart → Piece → M)
    (targetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (F.sourceChart x q)
          (F.boundarySourceChart x q)
          (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
    (targetBox_eq :
      ∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          targetBox x q = F.targetSelection x hx q hq)
    (targetSelectedBox :
      ∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          boundaryChartSelectedBox I (F.boundarySourceChart x q)
            (boundaryTargetChart x q) ω
            ((targetBox x q).lowerCorner) ((targetBox x q).upperCorner))
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    ((F.toTargetImageResolvedFamilyOfTargetBox boundaryTargetChart
        targetBox targetSelectedBox).toTargetBoxFamilySelection).targetLowerCorner
          x hx q hq =
      F.targetLowerCorner x hx q hq := by
  simpa [toTargetImageResolvedFamilyOfTargetBox,
    BoundaryChartTargetImageResolvedFamily.toTargetBoxFamilySelection] using
    congrArg BoundaryChartTargetBoxSelection.lowerCorner (targetBox_eq x hx q hq)

/-- Active target upper corners agree with the original proof-indexed selection. -/
theorem toTargetImageResolvedFamilyOfTargetBox_targetUpperCorner
    (F : BoundaryChartTargetBoxFamilySelection I ω Chart Piece)
    (boundaryTargetChart : Chart → Piece → M)
    (targetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (F.sourceChart x q)
          (F.boundarySourceChart x q)
          (F.sourceLowerCorner x q) (F.sourceUpperCorner x q))
    (targetBox_eq :
      ∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          targetBox x q = F.targetSelection x hx q hq)
    (targetSelectedBox :
      ∀ x, (hx : x ∈ F.activeCharts) →
        ∀ q, (hq : q ∈ F.localPieces x) →
          boundaryChartSelectedBox I (F.boundarySourceChart x q)
            (boundaryTargetChart x q) ω
            ((targetBox x q).lowerCorner) ((targetBox x q).upperCorner))
    (x : Chart) (hx : x ∈ F.activeCharts)
    (q : Piece) (hq : q ∈ F.localPieces x) :
    ((F.toTargetImageResolvedFamilyOfTargetBox boundaryTargetChart
        targetBox targetSelectedBox).toTargetBoxFamilySelection).targetUpperCorner
          x hx q hq =
      F.targetUpperCorner x hx q hq := by
  simpa [toTargetImageResolvedFamilyOfTargetBox,
    BoundaryChartTargetImageResolvedFamily.toTargetBoxFamilySelection] using
    congrArg BoundaryChartTargetBoxSelection.upperCorner (targetBox_eq x hx q hq)

end BoundaryChartTargetBoxFamilySelection

namespace BoundaryChartCompactImageCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Extend an active compact-image cover to the proof-free target-box function
required by resolved families.  Active entries use the cover data; inactive
entries use the supplied default.
-/
def targetBoxWithDefault
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (defaultTargetBox :
      ∀ q,
        BoundaryChartTargetBoxSelection I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q))
    (q : Piece) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) := by
  classical
  exact if hq : q ∈ C.activePieces then C.toTargetBoxSelection q hq
    else defaultTargetBox q

/-- Active compact-image cover entries ignore the inactive default. -/
theorem targetBoxWithDefault_of_mem
    (C : BoundaryChartCompactImageCover I x0 x1 a b Piece)
    (defaultTargetBox :
      ∀ q,
        BoundaryChartTargetBoxSelection I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q))
    (q : Piece) (hq : q ∈ C.activePieces) :
    C.targetBoxWithDefault defaultTargetBox q = C.toTargetBoxSelection q hq := by
  classical
  simp [targetBoxWithDefault, hq]

end BoundaryChartCompactImageCover

namespace BoundaryChartCompactImageForLocalInverseTargetCover

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Extend a local-inverse target cover to a proof-free target-box function, first
materializing compact-image control on active entries.
-/
def targetBoxWithDefault
    (C : BoundaryChartCompactImageForLocalInverseTargetCover I x0 x1 a b Piece)
    (defaultTargetBox :
      ∀ q,
        BoundaryChartTargetBoxSelection I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q))
    (q : Piece) :
    BoundaryChartTargetBoxSelection I x0 x1
      (C.sourceLowerCorner q) (C.sourceUpperCorner q) := by
  classical
  exact if hq : q ∈ C.activePieces then C.toTargetBoxSelection q hq
    else defaultTargetBox q

/-- Active local-inverse target cover entries ignore the inactive default. -/
theorem targetBoxWithDefault_of_mem
    (C : BoundaryChartCompactImageForLocalInverseTargetCover I x0 x1 a b Piece)
    (defaultTargetBox :
      ∀ q,
        BoundaryChartTargetBoxSelection I x0 x1
          (C.sourceLowerCorner q) (C.sourceUpperCorner q))
    (q : Piece) (hq : q ∈ C.activePieces) :
    C.targetBoxWithDefault defaultTargetBox q = C.toTargetBoxSelection q hq := by
  classical
  simp [targetBoxWithDefault, hq]

end BoundaryChartCompactImageForLocalInverseTargetCover

namespace BoundaryChartTargetImageResolvedFamily

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {ω : ManifoldForm I M n}
variable {Chart : Type c} {Piece : Type p}

/--
Build a resolved target-image family directly from per-chart compact-image
covers.  The local pieces are the active pieces of each cover.
-/
def ofCompactImageCoverFamily
    (activeCharts : Finset Chart)
    (sourceChart boundarySourceChart : Chart → M)
    (boundaryTargetChart : Chart → Piece → M)
    (chartLowerCorner chartUpperCorner : Chart → Fin (n + 1) → Real)
    (cover :
      ∀ x,
        BoundaryChartCompactImageCover I (sourceChart x) (boundarySourceChart x)
          (chartLowerCorner x) (chartUpperCorner x) Piece)
    (defaultTargetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (sourceChart x) (boundarySourceChart x)
          ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
            ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (boundarySourceChart x)
            (boundaryTargetChart x q) ω
            ((cover x).targetLowerCorner q) ((cover x).targetUpperCorner q)) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece where
  activeCharts := activeCharts
  localPieces := fun x => (cover x).activePieces
  sourceChart := fun x _ => sourceChart x
  boundarySourceChart := fun x _ => boundarySourceChart x
  boundaryTargetChart := boundaryTargetChart
  sourceLowerCorner := fun x q => (cover x).sourceLowerCorner q
  sourceUpperCorner := fun x q => (cover x).sourceUpperCorner q
  sourceSelectedBox := sourceSelectedBox
  targetBox := fun x q => (cover x).targetBoxWithDefault (defaultTargetBox x) q
  targetSelectedBox := by
    intro x hx q hq
    simpa [BoundaryChartCompactImageCover.targetBoxWithDefault, hq] using
      targetSelectedBox x hx q hq

/-- Active compact-image cover entries are the resolved target boxes. -/
theorem ofCompactImageCoverFamily_targetBox
    (activeCharts : Finset Chart)
    (sourceChart boundarySourceChart : Chart → M)
    (boundaryTargetChart : Chart → Piece → M)
    (chartLowerCorner chartUpperCorner : Chart → Fin (n + 1) → Real)
    (cover :
      ∀ x,
        BoundaryChartCompactImageCover I (sourceChart x) (boundarySourceChart x)
          (chartLowerCorner x) (chartUpperCorner x) Piece)
    (defaultTargetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (sourceChart x) (boundarySourceChart x)
          ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
            ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (boundarySourceChart x)
            (boundaryTargetChart x q) ω
            ((cover x).targetLowerCorner q) ((cover x).targetUpperCorner q))
    (x : Chart) (q : Piece) (hq : q ∈ (cover x).activePieces) :
    (ofCompactImageCoverFamily activeCharts sourceChart boundarySourceChart
        boundaryTargetChart chartLowerCorner chartUpperCorner cover
        defaultTargetBox sourceSelectedBox targetSelectedBox).targetBox x q =
      (cover x).toTargetBoxSelection q hq := by
  classical
  simp [ofCompactImageCoverFamily,
    BoundaryChartCompactImageCover.targetBoxWithDefault, hq]

/--
Build a resolved target-image family from local-inverse target covers, using the
cover's compact-image-for-local-inverse field to materialize active target boxes.
-/
def ofCompactImageForLocalInverseTargetCoverFamily
    (activeCharts : Finset Chart)
    (sourceChart boundarySourceChart : Chart → M)
    (boundaryTargetChart : Chart → Piece → M)
    (chartLowerCorner chartUpperCorner : Chart → Fin (n + 1) → Real)
    (cover :
      ∀ x,
        BoundaryChartCompactImageForLocalInverseTargetCover I
          (sourceChart x) (boundarySourceChart x)
          (chartLowerCorner x) (chartUpperCorner x) Piece)
    (defaultTargetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (sourceChart x) (boundarySourceChart x)
          ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
            ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (boundarySourceChart x)
            (boundaryTargetChart x q) ω
            ((cover x).targetLowerCorner q) ((cover x).targetUpperCorner q)) :
    BoundaryChartTargetImageResolvedFamily I ω Chart Piece where
  activeCharts := activeCharts
  localPieces := fun x => (cover x).activePieces
  sourceChart := fun x _ => sourceChart x
  boundarySourceChart := fun x _ => boundarySourceChart x
  boundaryTargetChart := boundaryTargetChart
  sourceLowerCorner := fun x q => (cover x).sourceLowerCorner q
  sourceUpperCorner := fun x q => (cover x).sourceUpperCorner q
  sourceSelectedBox := sourceSelectedBox
  targetBox := fun x q =>
    (cover x).targetBoxWithDefault (defaultTargetBox x) q
  targetSelectedBox := by
    intro x hx q hq
    simpa [BoundaryChartCompactImageForLocalInverseTargetCover.targetBoxWithDefault,
      hq] using
      targetSelectedBox x hx q hq

/-- Active local-inverse target cover entries are the resolved target boxes. -/
theorem ofCompactImageForLocalInverseTargetCoverFamily_targetBox
    (activeCharts : Finset Chart)
    (sourceChart boundarySourceChart : Chart → M)
    (boundaryTargetChart : Chart → Piece → M)
    (chartLowerCorner chartUpperCorner : Chart → Fin (n + 1) → Real)
    (cover :
      ∀ x,
        BoundaryChartCompactImageForLocalInverseTargetCover I
          (sourceChart x) (boundarySourceChart x)
          (chartLowerCorner x) (chartUpperCorner x) Piece)
    (defaultTargetBox :
      ∀ x q,
        BoundaryChartTargetBoxSelection I (sourceChart x) (boundarySourceChart x)
          ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (sourceSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (sourceChart x) (boundarySourceChart x) ω
            ((cover x).sourceLowerCorner q) ((cover x).sourceUpperCorner q))
    (targetSelectedBox :
      ∀ x, x ∈ activeCharts →
        ∀ q, q ∈ (cover x).activePieces →
          boundaryChartSelectedBox I (boundarySourceChart x)
            (boundaryTargetChart x q) ω
            ((cover x).targetLowerCorner q) ((cover x).targetUpperCorner q))
    (x : Chart) (q : Piece) (hq : q ∈ (cover x).activePieces) :
    (ofCompactImageForLocalInverseTargetCoverFamily activeCharts sourceChart
        boundarySourceChart boundaryTargetChart chartLowerCorner chartUpperCorner
        cover defaultTargetBox sourceSelectedBox targetSelectedBox).targetBox x q =
      (cover x).toTargetBoxSelection q hq := by
  classical
  simp [ofCompactImageForLocalInverseTargetCoverFamily,
    BoundaryChartCompactImageForLocalInverseTargetCover.targetBoxWithDefault, hq]

end BoundaryChartTargetImageResolvedFamily

end ManifoldBoundary

end Stokes

end
