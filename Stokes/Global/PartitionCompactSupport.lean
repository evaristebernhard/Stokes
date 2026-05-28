import Stokes.Global.PartitionSumOne
import Stokes.Global.CompactSupportChartBox

/-!
# Compact support API for partition-localized forms

This file packages the compact-support bookkeeping needed after localizing a
global form by a smooth partition of unity.  The key reusable fact is already in
`LocalizedSupport`: in any chart, the localized transition-pullback has
topological support contained in the base transition-pullback support.  Here we
connect that fact to the compact finite-active packages used by the global
assembly layer.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold Topology

namespace Stokes

section Basic

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

namespace FiniteActiveOnCompact

/--
The part of a partition term's topological support that lies in the compact set
controlled by a finite-active package.
-/
def partitionTSupportOnCompact
    (P : FiniteActiveOnCompact (M := M) I) (i : M) : Set M :=
  tsupport (P.partition i) ∩ P.K

theorem partitionTSupportOnCompact_subset_tsupport
    (P : FiniteActiveOnCompact (M := M) I) (i : M) :
    P.partitionTSupportOnCompact i ⊆ tsupport (P.partition i) :=
  inter_subset_left

theorem partitionTSupportOnCompact_subset_K
    (P : FiniteActiveOnCompact (M := M) I) (i : M) :
    P.partitionTSupportOnCompact i ⊆ P.K :=
  inter_subset_right

/--
The compact part of each partition term's topological support is compact,
because it is a closed subset of the package's compact set.
-/
theorem isCompact_partitionTSupportOnCompact
    (P : FiniteActiveOnCompact (M := M) I) (i : M) :
    IsCompact (P.partitionTSupportOnCompact i) :=
  P.isCompact_K.inter_left (isClosed_tsupport (P.partition i))

/-- Any nonempty compact support piece belongs to the active finite set. -/
theorem mem_active_of_partitionTSupportOnCompact_nonempty
    (P : FiniteActiveOnCompact (M := M) I) {i : M}
    (hi : (P.partitionTSupportOnCompact i).Nonempty) :
    i ∈ P.active := by
  rcases hi with ⟨x, hxt, hxK⟩
  exact P.mem_active_of_mem_tsupport hxK hxt

/-- Inactive partition terms have empty topological support over the compact set. -/
theorem partitionTSupportOnCompact_eq_empty_of_not_mem_active
    (P : FiniteActiveOnCompact (M := M) I) {i : M}
    (hi : i ∉ P.active) :
    P.partitionTSupportOnCompact i = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro x ⟨hxt, hxK⟩
  exact hi (P.mem_active_of_mem_tsupport hxK hxt)

/--
On the controlled compact set, the algebraic support of a localized form lies
in the compact topological-support piece of its partition coefficient.
-/
theorem localizedForm_support_inter_K_subset_partitionTSupportOnCompact
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ∩
        P.K ⊆
      P.partitionTSupportOnCompact i := by
  rintro x ⟨hxloc, hxK⟩
  exact
    ⟨subset_tsupport (P.partition i)
        (ManifoldForm.localizedForm_support_subset_coefficient_support
          (I := I) (P.partition i) ω hxloc),
      hxK⟩

/-- A partition-localized form is algebraically supported where its coefficient is. -/
theorem localizedForm_support_subset_partition_support
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ⊆
      Function.support (P.partition i) :=
  ManifoldForm.localizedForm_support_subset_coefficient_support
    (I := I) (P.partition i) ω

/-- A partition-localized form is algebraically supported where the base form is. -/
theorem localizedForm_support_subset_form_support
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ⊆
      ManifoldForm.support I ω :=
  ManifoldForm.localizedForm_support_subset_form_support
    (I := I) (P.partition i) ω

/-- Combined algebraic support control for a partition-localized form. -/
theorem localizedForm_support_subset_inter
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ⊆
      Function.support (P.partition i) ∩ ManifoldForm.support I ω :=
  ManifoldForm.localizedForm_support_subset_inter
    (I := I) (P.partition i) ω

/--
Algebraic support of a partition-localized form is contained in the
topological support of the partition coefficient.
-/
theorem localizedForm_support_subset_partition_tsupport
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ⊆
      tsupport (P.partition i) :=
  (P.localizedForm_support_subset_partition_support ω i).trans
    (subset_tsupport (P.partition i))

/--
On the controlled compact set, a localized form can be nonzero only where both
the coefficient is topologically active and the base form is algebraically
nonzero.
-/
theorem localizedForm_support_inter_K_subset_partitionTSupportOnCompact_inter_form_support
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ∩
        P.K ⊆
      P.partitionTSupportOnCompact i ∩ ManifoldForm.support I ω := by
  rintro x ⟨hxloc, hxK⟩
  exact
    ⟨⟨P.localizedForm_support_subset_partition_tsupport ω i hxloc, hxK⟩,
      P.localizedForm_support_subset_form_support ω i hxloc⟩

/--
If a localized form is nonzero at a point of the controlled compact set, then
its partition index is active.
-/
theorem mem_active_of_mem_localizedForm_support
    (P : FiniteActiveOnCompact (M := M) I)
    {ω : ManifoldForm I M k} {x i : M}
    (hxK : x ∈ P.K)
    (hxloc :
      x ∈ ManifoldForm.support I
        (ManifoldForm.localizedForm I (P.partition i) ω)) :
    i ∈ P.active := by
  have hxρ : x ∈ Function.support (P.partition i) :=
    ManifoldForm.localizedForm_support_subset_coefficient_support
      (I := I) (P.partition i) ω hxloc
  exact P.mem_active_of_mem_tsupport hxK (subset_tsupport (P.partition i) hxρ)

/-- Inactive localized forms have empty algebraic support on the controlled compact set. -/
theorem localizedForm_support_inter_K_eq_empty_of_not_mem_active
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) {i : M}
    (hi : i ∉ P.active) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ∩
        P.K = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro x ⟨hxloc, hxK⟩
  exact hi (P.mem_active_of_mem_localizedForm_support (ω := ω) hxK hxloc)

/-- Inactive localized forms are support-disjoint from the controlled compact set. -/
theorem disjoint_localizedForm_support_K_of_not_mem_active
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) {i : M}
    (hi : i ∉ P.active) :
    Disjoint
      (ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω))
      P.K := by
  rw [Set.disjoint_left]
  intro x hxloc hxK
  exact hi (P.mem_active_of_mem_localizedForm_support (ω := ω) hxK hxloc)

/-- Inactive localized forms vanish pointwise on the controlled compact set. -/
theorem localizedForm_eq_zero_of_mem_K_of_not_mem_active
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) {x i : M}
    (hxK : x ∈ P.K) (hi : i ∉ P.active) :
    ManifoldForm.localizedForm I (P.partition i) ω x = 0 := by
  by_contra hxloc
  exact hi (P.mem_active_of_mem_localizedForm_support (ω := ω) hxK hxloc)

/--
Chartwise topological support of a partition-localized form is contained in the
base chartwise topological support.
-/
theorem localized_transitionPullback_tsupport_subset_base
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (i : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      tsupport (ManifoldForm.transitionPullbackInChart I i i ω) :=
  ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_form
    (I := I) i i (P.partition i) ω

/--
In arbitrary transition coordinates, the localized representative is
topologically supported where the partition coefficient is supported in those
coordinates.
-/
theorem localized_transitionPullback_tsupport_subset_coefficient
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (x0 x1 i : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 (P.partition i)) :=
  ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_coefficient
    (I := I) x0 x1 (P.partition i) ω

/--
In arbitrary transition coordinates, the localized representative is
topologically supported where the base representative is supported.
-/
theorem localized_transitionPullback_tsupport_subset_form
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (x0 x1 i : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) :=
  ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_form
    (I := I) x0 x1 (P.partition i) ω

/--
Combined chart-coordinate topological support control for a partition-localized
representative.
-/
theorem localized_transitionPullback_tsupport_subset_inter
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) (x0 x1 i : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 (P.partition i)) ∩
        tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) := by
  intro y hy
  exact
    ⟨P.localized_transitionPullback_tsupport_subset_coefficient ω x0 x1 i hy,
      P.localized_transitionPullback_tsupport_subset_form ω x0 x1 i hy⟩

/--
If active base chart representatives are supported in compact coordinate sets,
then the corresponding partition-localized representatives are supported there
as well.
-/
theorem localized_transitionPullback_tsupport_subset_coordSupport_of_base
    (P : FiniteActiveOnCompact (M := M) I)
    (ω : ManifoldForm I M k) {coordSupport : M → Set E}
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          coordSupport i)
    {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      coordSupport i :=
  (P.localized_transitionPullback_tsupport_subset_base ω i).trans (hsupp i hi)

end FiniteActiveOnCompact

/--
Compact coordinate-support data for the family of partition-localized active
chart representatives.

This is the pre-box analogue of `ActiveChartCompactSupportData`, but the
representative attached to index `i` is the localized form
`P.partition i • ω`.
-/
structure ActiveLocalizedChartCompactSupportData
    (P : FiniteActiveOnCompact (M := M) I) (ω : ManifoldForm I M k) where
  /-- Compact coordinate support for each active localized representative. -/
  coordSupport : M → Set E
  /-- Compactness of each active coordinate support. -/
  isCompact_coordSupport :
    ∀ i ∈ P.active, IsCompact (coordSupport i)
  /-- Each active localized chart representative is supported in its compact set. -/
  localized_tsupport_subset_coordSupport :
    ∀ i ∈ P.active,
      tsupport
          (ManifoldForm.transitionPullbackInChart I i i
            (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
        coordSupport i

namespace ActiveLocalizedChartCompactSupportData

variable {P : FiniteActiveOnCompact (M := M) I} {ω : ManifoldForm I M k}

/-- Constructor from explicit compact coordinate supports for localized terms. -/
def of (coordSupport : M → Set E)
    (hcompact : ∀ i ∈ P.active, IsCompact (coordSupport i))
    (hsupp :
      ∀ i ∈ P.active,
        tsupport
            (ManifoldForm.transitionPullbackInChart I i i
              (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
          coordSupport i) :
    ActiveLocalizedChartCompactSupportData P ω where
  coordSupport := coordSupport
  isCompact_coordSupport := hcompact
  localized_tsupport_subset_coordSupport := hsupp

/--
Build localized compact-support data from compact supports for the base active
chart representatives.
-/
def ofBase (coordSupport : M → Set E)
    (hcompact : ∀ i ∈ P.active, IsCompact (coordSupport i))
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          coordSupport i) :
    ActiveLocalizedChartCompactSupportData P ω where
  coordSupport := coordSupport
  isCompact_coordSupport := hcompact
  localized_tsupport_subset_coordSupport :=
    fun i hi =>
      P.localized_transitionPullback_tsupport_subset_coordSupport_of_base
        ω hsupp (i := i) hi

end ActiveLocalizedChartCompactSupportData

namespace FiniteActiveOnCompact

/--
Wrapper constructor turning base compact supports into compact supports for the
partition-localized active family.
-/
def activeLocalizedChartCompactSupportData
    (P : FiniteActiveOnCompact (M := M) I) (ω : ManifoldForm I M k)
    (coordSupport : M → Set E)
    (hcompact : ∀ i ∈ P.active, IsCompact (coordSupport i))
    (hsupp :
      ∀ i ∈ P.active,
        tsupport (ManifoldForm.transitionPullbackInChart I i i ω) ⊆
          coordSupport i) :
    ActiveLocalizedChartCompactSupportData P ω :=
  ActiveLocalizedChartCompactSupportData.ofBase coordSupport hcompact hsupp

end FiniteActiveOnCompact

end Basic

section BoxedSupport

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [Preorder E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners Real E H} {k : Nat}

namespace ActiveLocalizedChartCompactSupportData

variable {P : FiniteActiveOnCompact (M := M) I} {ω : ManifoldForm I M k}

/-- The single-chart compact-support package for an active localized term. -/
def chartSupport
    (D : ActiveLocalizedChartCompactSupportData P ω)
    (i : M) (hi : i ∈ P.active) :
    ChartCompactSupportData I i i
      (ManifoldForm.localizedForm I (P.partition i) ω) where
  K := D.coordSupport i
  isCompact_K := D.isCompact_coordSupport i hi
  tsupport_subset_K := D.localized_tsupport_subset_coordSupport i hi

omit [Preorder E] in
@[simp]
theorem chartSupport_K
    (D : ActiveLocalizedChartCompactSupportData P ω)
    {i : M} (hi : i ∈ P.active) :
    (D.chartSupport i hi).K = D.coordSupport i :=
  rfl

end ActiveLocalizedChartCompactSupportData

/--
Boxed compact-support data for the active family of partition-localized chart
representatives.

It mirrors `CompactActiveBoxData`, but the form at active index `i` is the
localized form `P.partition i • ω`.
-/
structure ActiveLocalizedCompactBoxData
    (P : FiniteActiveOnCompact (M := M) I) (ω : ManifoldForm I M k) where
  /-- Compact coordinate support for each active localized representative. -/
  coordSupport : M → Set E
  /-- Compactness of each active coordinate support. -/
  isCompact_coordSupport :
    ∀ i ∈ P.active, IsCompact (coordSupport i)
  /-- A selected coordinate box for each index.  Only active indices are used. -/
  box : M → CompactCoordinateBoxSelection E
  /-- The selected coordinate box packages the corresponding coordinate support. -/
  box_K_eq_coordSupport :
    ∀ i ∈ P.active, (box i).K = coordSupport i
  /-- The localized transition-pullback support lies in the compact coordinate set. -/
  localized_tsupport_subset_coordSupport :
    ∀ i ∈ P.active,
      tsupport
          (ManifoldForm.transitionPullbackInChart I i i
            (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
        coordSupport i
  /-- The selected box lies in the target of the active chart. -/
  Icc_subset_target :
    ∀ i ∈ P.active,
      Set.Icc (box i).a (box i).b ⊆ (extChartAt I i).target
  /-- The selected box lies in the self-overlap domain for the active chart. -/
  Icc_subset_overlap :
    ∀ i ∈ P.active,
      Set.Icc (box i).a (box i).b ⊆ ManifoldForm.chartOverlap I i i

namespace ActiveLocalizedCompactBoxData

variable {P : FiniteActiveOnCompact (M := M) I} {ω : ManifoldForm I M k}

/-- Lower corner of the selected localized coordinate box for each index. -/
def lower (D : ActiveLocalizedCompactBoxData P ω) : M → E :=
  fun i => (D.box i).a

/-- Upper corner of the selected localized coordinate box for each index. -/
def upper (D : ActiveLocalizedCompactBoxData P ω) : M → E :=
  fun i => (D.box i).b

@[simp]
theorem lower_apply (D : ActiveLocalizedCompactBoxData P ω) (i : M) :
    D.lower i = (D.box i).a :=
  rfl

@[simp]
theorem upper_apply (D : ActiveLocalizedCompactBoxData P ω) (i : M) :
    D.upper i = (D.box i).b :=
  rfl

theorem coordSupport_subset_Icc
    (D : ActiveLocalizedCompactBoxData P ω) {i : M} (hi : i ∈ P.active) :
    D.coordSupport i ⊆ Set.Icc (D.lower i) (D.upper i) := by
  intro y hy
  change y ∈ Set.Icc (D.box i).a (D.box i).b
  exact (D.box i).subset_Icc (by
    simpa [D.box_K_eq_coordSupport i hi] using hy)

theorem localized_tsupport_subset_box
    (D : ActiveLocalizedCompactBoxData P ω) {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      Set.Icc (D.lower i) (D.upper i) :=
  (D.localized_tsupport_subset_coordSupport i hi).trans
    (D.coordSupport_subset_Icc hi)

/--
The active localized compact box data produces the selected interior chart box
for the localized form at an active index.
-/
theorem localizedInteriorChartSelectedBox
    (D : ActiveLocalizedCompactBoxData P ω) {i : M} (hi : i ∈ P.active) :
    Stokes.interiorChartSelectedBox I i i
      (ManifoldForm.localizedForm I (P.partition i) ω)
      (D.lower i) (D.upper i) := by
  change
    Stokes.interiorChartSelectedBox I i i
      (ManifoldForm.localizedForm I (P.partition i) ω)
      (D.box i).a (D.box i).b
  exact Stokes.interiorChartSelectedBox.mk_of_subsets
    (D.box i).le (D.Icc_subset_target i hi) (D.Icc_subset_overlap i hi)
    (by simpa [lower, upper] using D.localized_tsupport_subset_box hi)

/--
Base compact active box data immediately controls every partition-localized
active representative, using the `tsupport` subset from `LocalizedSupport`.
-/
def ofCompactActiveBoxData
    (D : CompactActiveBoxData I ω) :
    ActiveLocalizedCompactBoxData D.finiteActive ω where
  coordSupport := D.coordSupport
  isCompact_coordSupport := D.isCompact_coordSupport
  box := D.box
  box_K_eq_coordSupport := D.box_K_eq_coordSupport
  localized_tsupport_subset_coordSupport := fun i hi =>
    D.finiteActive.localized_transitionPullback_tsupport_subset_coordSupport_of_base
      ω D.tsupport_subset_coordSupport (i := i) hi
  Icc_subset_target := D.Icc_subset_target
  Icc_subset_overlap := D.Icc_subset_overlap

@[simp]
theorem ofCompactActiveBoxData_coordSupport
    (D : CompactActiveBoxData I ω) :
    (ofCompactActiveBoxData D).coordSupport = D.coordSupport :=
  rfl

@[simp]
theorem ofCompactActiveBoxData_box
    (D : CompactActiveBoxData I ω) :
    (ofCompactActiveBoxData D).box = D.box :=
  rfl

end ActiveLocalizedCompactBoxData

namespace CompactActiveBoxData

variable {ω : ManifoldForm I M k}

/-- Forget the base-form viewpoint and keep the induced localized compact boxes. -/
def toActiveLocalizedCompactBoxData
    (D : CompactActiveBoxData I ω) :
    ActiveLocalizedCompactBoxData D.finiteActive ω :=
  ActiveLocalizedCompactBoxData.ofCompactActiveBoxData D

@[simp]
theorem toActiveLocalizedCompactBoxData_coordSupport
    (D : CompactActiveBoxData I ω) :
    D.toActiveLocalizedCompactBoxData.coordSupport = D.coordSupport :=
  rfl

@[simp]
theorem toActiveLocalizedCompactBoxData_box
    (D : CompactActiveBoxData I ω) :
    D.toActiveLocalizedCompactBoxData.box = D.box :=
  rfl

theorem localized_tsupport_subset_coordSupport
    (D : CompactActiveBoxData I ω) {i : M}
    (hi : i ∈ D.finiteActive.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (D.finiteActive.partition i) ω)) ⊆
      D.coordSupport i :=
  D.finiteActive.localized_transitionPullback_tsupport_subset_coordSupport_of_base
    ω D.tsupport_subset_coordSupport hi

theorem localized_tsupport_subset_box
    (D : CompactActiveBoxData I ω) {i : M}
    (hi : i ∈ D.finiteActive.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (D.finiteActive.partition i) ω)) ⊆
      Set.Icc (D.lower i) (D.upper i) :=
  D.toActiveLocalizedCompactBoxData.localized_tsupport_subset_box hi

theorem localizedInteriorChartSelectedBox
    (D : CompactActiveBoxData I ω) {i : M}
    (hi : i ∈ D.finiteActive.active) :
    Stokes.interiorChartSelectedBox I i i
      (ManifoldForm.localizedForm I (D.finiteActive.partition i) ω)
      (D.lower i) (D.upper i) :=
  D.toActiveLocalizedCompactBoxData.localizedInteriorChartSelectedBox hi

end CompactActiveBoxData

namespace CompactActiveExtendedBoxData

variable {ω : ManifoldForm I M k}

/-- The localized compact-box family induced by an extended active box package. -/
def toActiveLocalizedCompactBoxData
    (D : CompactActiveExtendedBoxData I ω) :
    ActiveLocalizedCompactBoxData D.boxData.finiteActive ω :=
  D.boxData.toActiveLocalizedCompactBoxData

@[simp]
theorem toActiveLocalizedCompactBoxData_coordSupport
    (D : CompactActiveExtendedBoxData I ω) :
    D.toActiveLocalizedCompactBoxData.coordSupport = D.boxData.coordSupport :=
  rfl

@[simp]
theorem toActiveLocalizedCompactBoxData_box
    (D : CompactActiveExtendedBoxData I ω) :
    D.toActiveLocalizedCompactBoxData.box = D.boxData.box :=
  rfl

end CompactActiveExtendedBoxData

namespace SelectedBoxPartitionOfUnity

variable {ω : ManifoldForm I M k}

/--
The compact part of a selected partition term's topological support, viewed
through the underlying finite-active package.
-/
def partitionTSupportOnCompact
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) : Set M :=
  P.toFiniteActiveOnCompact.partitionTSupportOnCompact i

@[simp]
theorem partitionTSupportOnCompact_eq
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    P.partitionTSupportOnCompact i = tsupport (P.partition i) ∩ P.K :=
  rfl

theorem isCompact_partitionTSupportOnCompact
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    IsCompact (P.partitionTSupportOnCompact i) :=
  P.toFiniteActiveOnCompact.isCompact_partitionTSupportOnCompact i

theorem mem_active_of_partitionTSupportOnCompact_nonempty
    (P : SelectedBoxPartitionOfUnity I ω) {i : M}
    (hi : (P.partitionTSupportOnCompact i).Nonempty) :
    i ∈ P.active := by
  simpa using
    P.toFiniteActiveOnCompact.mem_active_of_partitionTSupportOnCompact_nonempty hi

/-- A selected-box localized form is algebraically supported where its coefficient is. -/
theorem localizedForm_support_subset_partition_support
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ⊆
      Function.support (P.partition i) := by
  simpa using
    P.toFiniteActiveOnCompact.localizedForm_support_subset_partition_support
      ω i

/-- A selected-box localized form is algebraically supported where the base form is. -/
theorem localizedForm_support_subset_form_support
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ⊆
      ManifoldForm.support I ω := by
  simpa using
    P.toFiniteActiveOnCompact.localizedForm_support_subset_form_support
      ω i

/-- Combined algebraic support control for a selected-box localized form. -/
theorem localizedForm_support_subset_inter
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ⊆
      Function.support (P.partition i) ∩ ManifoldForm.support I ω := by
  simpa using
    P.toFiniteActiveOnCompact.localizedForm_support_subset_inter
      ω i

/--
Algebraic support of a selected-box localized form is contained in the
topological support of the partition coefficient.
-/
theorem localizedForm_support_subset_partition_tsupport
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ⊆
      tsupport (P.partition i) := by
  simpa using
    P.toFiniteActiveOnCompact.localizedForm_support_subset_partition_tsupport
      ω i

/--
On the selected compact set, a localized form can be nonzero only where both
the coefficient is topologically active and the base form is algebraically
nonzero.
-/
theorem localizedForm_support_inter_K_subset_partitionTSupportOnCompact_inter_form_support
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ∩
        P.K ⊆
      P.partitionTSupportOnCompact i ∩ ManifoldForm.support I ω := by
  intro x hx
  exact
    P.toFiniteActiveOnCompact
      |>.localizedForm_support_inter_K_subset_partitionTSupportOnCompact_inter_form_support
        ω i hx

/-- Localized selected-box terms vanish on `K` when their index is inactive. -/
theorem localizedForm_eq_zero_of_mem_K_of_not_mem_active
    (P : SelectedBoxPartitionOfUnity I ω) {x i : M}
    (hxK : x ∈ P.K) (hi : i ∉ P.active) :
    ManifoldForm.localizedForm I (P.partition i) ω x = 0 := by
  simpa using
    P.toFiniteActiveOnCompact.localizedForm_eq_zero_of_mem_K_of_not_mem_active
      ω hxK hi

/-- Inactive selected-box localized forms have empty algebraic support on `K`. -/
theorem localizedForm_support_inter_K_eq_empty_of_not_mem_active
    (P : SelectedBoxPartitionOfUnity I ω) {i : M}
    (hi : i ∉ P.active) :
    ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω) ∩
        P.K = ∅ := by
  simpa using
    P.toFiniteActiveOnCompact.localizedForm_support_inter_K_eq_empty_of_not_mem_active
      ω hi

/-- Inactive selected-box localized forms are support-disjoint from `K`. -/
theorem disjoint_localizedForm_support_K_of_not_mem_active
    (P : SelectedBoxPartitionOfUnity I ω) {i : M}
    (hi : i ∉ P.active) :
    Disjoint
      (ManifoldForm.support I (ManifoldForm.localizedForm I (P.partition i) ω))
      P.K := by
  simpa using
    P.toFiniteActiveOnCompact.disjoint_localizedForm_support_K_of_not_mem_active
      ω hi

/--
If a localized selected-box term is nonzero at a point of `K`, then its index
is active.
-/
theorem mem_active_of_mem_localizedForm_support
    (P : SelectedBoxPartitionOfUnity I ω) {x i : M}
    (hxK : x ∈ P.K)
    (hxloc :
      x ∈ ManifoldForm.support I
        (ManifoldForm.localizedForm I (P.partition i) ω)) :
    i ∈ P.active := by
  simpa using
    P.toFiniteActiveOnCompact.mem_active_of_mem_localizedForm_support
      (ω := ω) hxK hxloc

/-- Localized chart support is contained in the base selected-box support. -/
theorem localized_transitionPullback_tsupport_subset_base
    (P : SelectedBoxPartitionOfUnity I ω) (i : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      tsupport (ManifoldForm.transitionPullbackInChart I i i ω) :=
  P.toFiniteActiveOnCompact.localized_transitionPullback_tsupport_subset_base ω i

/--
Selected-box localized representatives are topologically supported where their
transition-coordinate coefficient is supported.
-/
theorem localized_transitionPullback_tsupport_subset_coefficient
    (P : SelectedBoxPartitionOfUnity I ω) (x0 x1 i : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 (P.partition i)) :=
  P.toFiniteActiveOnCompact.localized_transitionPullback_tsupport_subset_coefficient
    ω x0 x1 i

/--
Selected-box localized representatives are topologically supported where the
base transition representative is supported.
-/
theorem localized_transitionPullback_tsupport_subset_form
    (P : SelectedBoxPartitionOfUnity I ω) (x0 x1 i : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) :=
  P.toFiniteActiveOnCompact.localized_transitionPullback_tsupport_subset_form
    ω x0 x1 i

/--
Combined chart-coordinate topological support control for a selected-box
localized representative.
-/
theorem localized_transitionPullback_tsupport_subset_inter
    (P : SelectedBoxPartitionOfUnity I ω) (x0 x1 i : M) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I x0 x1
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      tsupport (ManifoldForm.transitionCoefficientInChart I x0 x1 (P.partition i)) ∩
        tsupport (ManifoldForm.transitionPullbackInChart I x0 x1 ω) :=
  P.toFiniteActiveOnCompact.localized_transitionPullback_tsupport_subset_inter
    ω x0 x1 i

/-- Each active localized selected-box representative is supported in the selected box. -/
theorem localized_tsupport_subset_Icc
    (P : SelectedBoxPartitionOfUnity I ω) {i : M} (hi : i ∈ P.active) :
    tsupport
        (ManifoldForm.transitionPullbackInChart I i i
          (ManifoldForm.localizedForm I (P.partition i) ω)) ⊆
      Set.Icc (P.lower i) (P.upper i) :=
  (P.localized_transitionPullback_tsupport_subset_base i).trans
    (P.tsupport_subset_Icc hi)

/--
The selected box for a base active representative is also a selected box for
the corresponding partition-localized representative.
-/
theorem localizedInteriorChartSelectedBox
    (P : SelectedBoxPartitionOfUnity I ω) {i : M} (hi : i ∈ P.active) :
    Stokes.interiorChartSelectedBox I i i
      (ManifoldForm.localizedForm I (P.partition i) ω)
      (P.lower i) (P.upper i) :=
  Stokes.interiorChartSelectedBox.mk_of_subsets (P.le hi)
    (P.selectedBox hi).Icc_subset_target
    (P.selectedBox hi).Icc_subset_overlap
    (P.localized_tsupport_subset_Icc hi)

end SelectedBoxPartitionOfUnity

end BoxedSupport

end Stokes

end
