import Stokes.BoundaryChart.ControlledTargetBoxFromLocalInverseAuto
import Stokes.BoundaryChart.SelectedBoxIFTAuto

/-!
# Controlled target boxes from IFT/local-openness data

This file is the IFT-facing wrapper for
`BoundaryChartControlledTargetBoxSelectionData`.

The lower layer `ControlledTargetBoxFromLocalInverseAuto` already knows how to
turn local-openness plus compact-image-for-local-inverse-targets into a single
controlled target box.  Here we expose caller-facing constructors that generate
the local-openness and compact-image predicates from the existing
IFT/selected-box/source-shrink APIs, so downstream boundary chart arguments no
longer have to pass raw `boundaryChartCompactCoordinateImageForLocalInverseTargets`
or source-image compactness fields.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

section ManifoldBoundary

universe u w p

variable {H : Type u} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/--
Local openness plus source-image containment for every selected local-inverse
target gives a controlled target box inside an arbitrary target-side
neighborhood `U`.
-/
theorem exists_controlledTargetBoxSelection_of_localOpenness_image_subset
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {y : Fin n → Real} {U : Set (Fin n → Real)}
    (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hsubset :
      ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
        y ∈ lowerZeroFaceDomain c d →
          boundaryChartLocalInverseData I x0 x1 a b c d →
            (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ⊆
              lowerZeroFaceDomain c d) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) (U := U) hU himage
    (boundaryChartCompactCoordinateImageForLocalInverseTargets_of_image_subset
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) hsubset)

/--
Local openness plus compact source-image-box containment gives a controlled
target box without asking callers for the raw local-inverse compact-image
predicate.
-/
theorem exists_controlledTargetBoxSelection_of_localOpenness_isCompactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {y : Fin n → Real} {U : Set (Fin n → Real)}
    (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hK : IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b))
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            y ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) (U := U) hU himage
    (boundaryChartCompactCoordinateImageForLocalInverseTargets_of_isCompactImage
      (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
      (y := y) hK hcontains)

/--
Selected-box version: compactness of the source image is generated from the
selected source boundary box.
-/
theorem exists_controlledTargetBoxSelection_of_localOpenness_selectedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    {y : Fin n → Real} {U : Set (Fin n → Real)}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hU : U ∈ 𝓝 y)
    (himage :
      (boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b ∈ 𝓝 y)
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            y ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d y U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_isCompactImage
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := y) (U := U) hU himage
    (boundaryChartTransition_isCompact_image_of_selectedBox
      (I := I) (x0 := x0) (x1 := x1)
      (ω := ω) (a := a) (b := b) hbox)
    hcontains

/--
IFT-facing constructor with an explicit compact image of the source boundary
box.  The local-openness neighborhood is generated by the strict derivative and
surjectivity fields.
-/
theorem exists_controlledTargetBoxSelection_of_IFT_isCompactImage
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    {x0 x1 : M} {a b : Fin (n + 1) → Real}
    {u : Fin n → Real} {U : Set (Fin n → Real)}
    (hU : U ∈ 𝓝 (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hK : IsCompact
      ((boundaryChartTransition I x0 x1) '' lowerZeroFaceDomain a b))
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d (boundaryChartTransition I x0 x1 u) U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_isCompactImage
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := boundaryChartTransition I x0 x1 u) (U := U)
    hU
    (boundaryChartTransition_image_mem_nhds_of_hasStrictFDerivAt_surj
      hderiv hsurj hsource)
    hK hcontains

/--
Selected-box IFT-facing constructor.  This is the pointwise route with no raw
`IsCompact` field and no raw
`boundaryChartCompactCoordinateImageForLocalInverseTargets` field.
-/
theorem exists_controlledTargetBoxSelection_of_IFT_selectedBox
    {n : Nat} {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
    [IsManifold I 1 M]
    {x0 x1 : M} {ω : ManifoldForm I M n}
    {a b : Fin (n + 1) → Real}
    {u : Fin n → Real} {U : Set (Fin n → Real)}
    (hbox : boundaryChartSelectedBox I x0 x1 ω a b)
    (hU : U ∈ 𝓝 (boundaryChartTransition I x0 x1 u))
    (hsource : lowerZeroFaceDomain a b ∈ 𝓝 u)
    (hderiv :
      HasStrictFDerivAt (boundaryChartTransition I x0 x1)
        (boundaryChartTransitionTangentMap I x0 x1 u) u)
    (hsurj : (boundaryChartTransitionTangentMap I x0 x1 u).range = ⊤)
    (hcontains :
      ∀ e f : Fin n → Real, e ≤ f →
        compactCoordinateImageBoxSelection (boundaryChartTransition I x0 x1)
          (lowerZeroFaceDomain a b) e f →
          ∀ c d : Fin (n + 1) → Real, c 0 = 0 → c ≤ d →
            boundaryChartTransition I x0 x1 u ∈ lowerZeroFaceDomain c d →
              boundaryChartLocalInverseData I x0 x1 a b c d →
                Set.Icc e f ⊆
                  Set.Icc (boundaryFaceLowerCorner c) (boundaryFaceUpperCorner d)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ D : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d (boundaryChartTransition I x0 x1 u) U,
        D.laterLowerCorner = c ∧ D.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_IFT_isCompactImage
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (u := u) (U := U) hU hsource hderiv hsurj
    (boundaryChartTransition_isCompact_image_of_selectedBox
      (I := I) (x0 := x0) (x1 := x1)
      (ω := ω) (a := a) (b := b) hbox)
    hcontains

namespace BoundaryChartSelectedBoxIFTPointAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real}

/--
Pointwise selected-box IFT auto-data produces a controlled target box in any
target-side neighborhood of the IFT image point.
-/
theorem exists_controlledTargetBoxSelection
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 D.targetPoint) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 a b c d D.targetPoint U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    (I := I) (x0 := x0) (x1 := x1) (a := a) (b := b)
    (y := D.targetPoint) (U := U)
    hU D.image_mem_nhds D.compactImageForLocalInverseTargets

/--
Canonical chosen controlled target box from pointwise selected-box IFT
auto-data.
-/
def controlledTargetBoxSelection
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTPointAutoData I x0 x1 ω a b)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 D.targetPoint) :
    Σ c : Fin (n + 1) → Real, Σ d : Fin (n + 1) → Real,
      BoundaryChartControlledTargetBoxSelectionData
        I x0 x1 a b c d D.targetPoint U :=
  ⟨Classical.choose (D.exists_controlledTargetBoxSelection hU),
    Classical.choose
      (Classical.choose_spec (D.exists_controlledTargetBoxSelection hU)),
    Classical.choose
      (Classical.choose_spec
        (Classical.choose_spec (D.exists_controlledTargetBoxSelection hU)))⟩

end BoundaryChartSelectedBoxIFTPointAutoData

namespace BoundaryChartIFTCompactImageCoverData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
One active IFT compact-image cover piece produces a controlled target box in
any target-side neighborhood of the piece's IFT image point.
-/
theorem exists_controlledTargetBoxSelection
    (D : BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
            c d (D.targetPoint q) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage_subset
    (I := I) (x0 := x0) (x1 := x1)
    (a := D.sourceLowerCorner q) (b := D.sourceUpperCorner q)
    (y := D.targetPoint q) (U := U)
    hU (D.image_mem_nhds q hq) (D.compactImageForLocalInverseTargets q hq)

/--
Image-neighborhood version for one active IFT compact-image cover piece.
-/
theorem exists_controlledTargetBoxSelectionInImage
    (D : BoundaryChartIFTCompactImageCoverData I x0 x1 a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
            c d (D.targetPoint q)
            ((boundaryChartTransition I x0 x1) ''
              lowerZeroFaceDomain (D.sourceLowerCorner q) (D.sourceUpperCorner q)),
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d :=
  exists_controlledTargetBoxSelection_of_localOpenness_compactImage
    (I := I) (x0 := x0) (x1 := x1)
    (a := D.sourceLowerCorner q) (b := D.sourceUpperCorner q)
    (y := D.targetPoint q)
    (D.image_mem_nhds q hq) (D.compactImageForLocalInverseTargets q hq)

end BoundaryChartIFTCompactImageCoverData

namespace BoundaryChartSelectedBoxIFTCompactCoverAutoData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M} {ω : ManifoldForm I M n}
variable {a b : Fin (n + 1) → Real} {Piece : Type p}

/--
Selected-box finite-cover IFT auto-data produces a controlled target box for
each active cover piece; compactness of the source image is generated from the
active selected source box.
-/
theorem exists_controlledTargetBoxSelection
    [IsManifold I 1 M]
    (D : BoundaryChartSelectedBoxIFTCompactCoverAutoData I x0 x1 ω a b Piece)
    (q : Piece) (hq : q ∈ D.activePieces)
    {U : Set (Fin n → Real)} (hU : U ∈ 𝓝 (D.targetPoint q)) :
    ∃ c d : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 (D.sourceLowerCorner q) (D.sourceUpperCorner q)
            c d (D.targetPoint q) U,
        C.laterLowerCorner = c ∧ C.laterUpperCorner = d := by
  simpa [BoundaryChartSelectedBoxIFTCompactCoverAutoData.targetPoint,
    BoundaryChartIFTCompactImageCoverData.targetPoint] using
    (D.toIFTCompactImageCoverData.exists_controlledTargetBoxSelection q hq hU)

end BoundaryChartSelectedBoxIFTCompactCoverAutoData

namespace BoundaryChartSourceShrinkOpenPartialHomeomorphData

variable {n : Nat}
variable {I : ModelWithCorners Real (Fin (n + 1) → Real) H}
variable {x0 x1 : M}
variable {a b c d : Fin (n + 1) → Real} {u y : Fin n → Real}

/--
Source-shrink local-homeomorphism/IFT data already contains the target
membership, target-neighborhood, compact-image, and local-inverse halves, so it
canonically produces the controlled target selection inside the ambient target
box.
-/
theorem exists_controlledTargetBoxSelectionInAmbient
    (D : BoundaryChartSourceShrinkOpenPartialHomeomorphData I x0 x1 a b c d u y) :
    ∃ e f : Fin (n + 1) → Real,
      ∃ C : BoundaryChartControlledTargetBoxSelectionData
          I x0 x1 D.sourceLowerCorner D.sourceUpperCorner e f y
            (lowerZeroFaceDomain c d),
        C.laterLowerCorner = e ∧ C.laterUpperCorner = f := by
  refine
    ⟨D.targetLowerCorner, D.targetUpperCorner,
      D.toControlledTargetBoxSelectionInAmbient, ?_, ?_⟩
  · rfl
  · rfl

end BoundaryChartSourceShrinkOpenPartialHomeomorphData

end ManifoldBoundary

end Stokes

end
