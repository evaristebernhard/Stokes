# Stokes M8 Measure Localization Route

Scope: documentation-only worker output for the current Lean 4 Stokes
workspace. No Lean source files were changed.

Date: 2026-05-24.

## Purpose

This report records the preferred route for the next measure-localization
wave. The main choice is to prove reconstruction by finite sums of indicator
localized integrands, using mathlib's Bochner integral linearity
`MeasureTheory.integral_finset_sum`, rather than trying to decompose the
manifold into a disjoint union of chart domains.

The target is to turn the current explicit reconstruction fields into theorems:

- bulk: the global integral of the top-degree exterior derivative localizes to
  the finite interior and boundary-chart bulk terms;
- boundary: the represented boundary measure integral localizes to the finite
  boundary partition terms.

## Main Route

The measure-localization proof should be organized around a pointwise or
almost-everywhere identity of integrands:

```lean
Filter.EventuallyEq (MeasureTheory.Measure.ae mu) globalIntegrand
  (fun x => Finset.sum active fun i =>
    (domain i).indicator (localizedIntegrand i) x)
```

Then the integral reconstruction is a three-step calculation:

1. Replace the global integrand by the finite indicator sum using
   `integral_congr_ae` or an exact pointwise congruence.
2. Move the finite sum outside the integral with
   `MeasureTheory.integral_finset_sum`, after proving integrability of each
   indicator term.
3. Rewrite each whole-space indicator integral as the intended local set
   integral with `MeasureTheory.integral_indicator` or
   `MeasureTheory.setIntegral_indicator`, then identify that set integral with
   the existing project-local term.

In schematic form:

```lean
calc
  globalIntegral
      = integral mu globalIntegrand := by rfl
  _ = integral mu (fun x =>
        Finset.sum active fun i =>
          (domain i).indicator (localizedIntegrand i) x) := by
        exact integral_congr_ae hae
  _ = Finset.sum active fun i =>
        integral mu ((domain i).indicator (localizedIntegrand i)) := by
        rw [MeasureTheory.integral_finset_sum active hintegrable]
  _ = Finset.sum active fun i =>
        integral (mu.restrict (domain i)) (localizedIntegrand i) := by
        simp_rw [MeasureTheory.integral_indicator hdomain]
  _ = finiteLocalTermSum := by
        exact Finset.sum_congr rfl hlocalTerm
```

This is the theorem shape that should fill the existing reconstruction fields.

## Why Not Disjoint Union

A disjoint-union proof is the wrong primary abstraction for the partition of
unity layer.

- The active chart neighborhoods naturally overlap. The overlap is not an
  error; it is exactly where the partition coefficients add to `1`.
- A disjoint refinement such as `U_i \ \bigcup_{j<i} U_j` would create
  nonsmooth artificial domains that do not match the selected boxes, local
  Stokes hypotheses, or chart-change packages.
- Disjointness proves additivity of measures over sets. Here the needed
  identity is linearity of the integral over functions:
  `omega = sum_i rho_i * omega` on the support.
- Indicator functions keep local domain restriction explicit without requiring
  domains to be disjoint. Overlap is handled by the pointwise coefficient
  sum-one theorem, not by set subtraction.
- This avoids adding extra boundary faces from arbitrary disjoint refinements.
  The only artificial faces should remain the selected-box faces already owned
  by the artificial-face cancellation layer.

Disjointness may still appear locally where it is already mathematically
natural, for example in artificial-face cancellation or support-disjoint
vanishing lemmas. It should not be the mechanism for global integral
reconstruction.

## Lean API Map

| Layer | File | Existing declarations or fields | M8 role |
|---|---|---|---|
| Pointwise partition reconstruction | `Stokes/Global/Reconstruction.lean` | `localizedFormSum`, `localizedFormSum_apply_eq_coeff_sum_smul`, `localizedFormSum_eqOn_of_coeff_sum_eq_one_on` | Supplies the pointwise equality behind the integrand identity. |
| Compact active coefficients | `Stokes/Global/PartitionSumOne.lean` | `FiniteActiveOnCompact.coeff_sum_eq_one_on`, `SelectedBoxPartitionOfUnity.coeff_sum_eq_one_on` | Produces `sum_i rho_i x = 1` on the compact support set. |
| Support/everywhere extension | `Stokes/Global/PartitionLocalizedEventually.lean` | `LocalizedFormEventuallyEqData`, `localizedFormSum_eq_self`, `transitionPullbackInChart_eventuallyEq_self`, `extDeriv_transitionPullbackInChart_eq_self` | Converts on-support reconstruction into global or local eventual equality. |
| Finite-sum support control | `Stokes/Global/SupportFiniteSum.lean` | `localizedFormSum_support_subset_form_support`, `transitionPullbackInChart_localizedFormSum_tsupport_subset_*` | Keeps the finite sum integrable and supported inside selected chart boxes. |
| Localized interior terms | `Stokes/Global/LocalizedInteriorPieces.lean` | `LocalizedInteriorPieces.bulkTerm`, `artificialBoundaryTerm`, `localProjectEquality` | Supplies the interior local terms that bulk localization must sum. |
| Boundary local terms | `Stokes/Global/BoundaryPieceFamilyConstructor.lean` | `BoundaryPieceFamilyInput.boundaryBulkTerm`, `boundaryBulkSum`, `boundaryBoundaryTerm` | Supplies the boundary-chart bulk terms and transported boundary terms. |
| Generic finite additivity fields | `Stokes/Global/LocalIntegralFiniteAdditivity.lean` | `LocalIntegralFiniteAdditivityData.globalIntegral_eq_localSum`, `BulkBoundaryIntegralFiniteAdditivityData.globalBulkIntegral_eq_localBulkSum`, `globalBoundaryIntegral_eq_boundaryPartitionSum`, `ProjectLocalIntegralFiniteAdditivityData.globalBulkIntegral_eq_projectLocalSum` | Best place for reusable indicator-based theorem constructors. |
| Bulk reconstruction | `Stokes/Global/BulkIntegralPartitionReconstruction.lean` | `SplitBulkIntegralReconstructionInput.bulkIntegralLocalizes`, `BulkIntegralPartitionInput.bulkIntegralLocalizes` | Main bulk field to be replaced by a theorem from indicator localization. |
| Core bulk package | `Stokes/Global/IntegralReconstruction.lean` | `BulkIntegralReconstructionData.globalBulkIntegral_eq_localBulkSum`, `BoundaryPartitionFields.globalBoundaryIntegral_eq_boundaryPartitionSum` | Receives the filled finite-additivity/reconstruction fields. |
| Boundary reconstruction | `Stokes/Global/BoundaryIntegralPartitionReconstruction.lean` | `BoundaryIntegralPartitionReconstructionData.boundaryMeasureIntegral`, `manifoldBoundaryIntegral_eq_boundaryMeasureIntegral`, `boundaryMeasureIntegral_eq_partitionSum` | Main boundary-measure field to be replaced by a theorem from indicator localization. |
| Natural input | `Stokes/Global/NaturalInputData.lean` | `CompactlySupportedSmoothFormData`, `NaturalGlobalStokesInput.bulkReconstruction`, `boundaryReconstruction` | Final consumer once the bulk and boundary reconstruction data can be constructed. |

## Theorem Targets

### M8-MEAS-01: finite indicator integral sum

Reusable theorem, probably in `Stokes/Global/LocalIntegralFiniteAdditivity.lean`
or a new small imported helper:

```lean
theorem integral_indicator_finset_sum_eq_chartPieceSum
    (activeCharts : Finset Chart)
    (localPieces : Chart -> Finset Piece)
    (domain : Chart -> Piece -> Set X)
    (f : Chart -> Piece -> X -> Real)
    ...
    :
    integral mu (fun x =>
      chartPieceSum activeCharts localPieces
        (fun c p => (domain c p).indicator (f c p) x))
      =
    chartPieceSum activeCharts localPieces
      (fun c p => integral mu ((domain c p).indicator (f c p)))
```

The exact codomain may need to be a complete normed additive group if reused
outside `Real`. The proof should be only `chartPieceSum_eq_indexSet_sum` plus
`MeasureTheory.integral_finset_sum`.

### M8-MEAS-02: one-family reconstruction

Fill `LocalIntegralFiniteAdditivityData.globalIntegral_eq_localSum` from:

- a definition of `globalIntegral` as `integral mu globalIntegrand`;
- an a.e. equality between `globalIntegrand` and the finite indicator sum;
- integrability of each indicator-local term;
- identification of each local indicator integral with `localIntegralTerm`.

This target can produce constructors like:

```lean
def LocalIntegralFiniteAdditivityData.ofIndicatorLocalization ...
```

### M8-MEAS-03: mixed bulk reconstruction

Fill:

- `BulkBoundaryIntegralFiniteAdditivityData.globalBulkIntegral_eq_localBulkSum`;
- `BulkIntegralPartitionInput.bulkIntegralLocalizes`;
- `SplitBulkIntegralReconstructionInput.bulkIntegralLocalizes`;
- ultimately `BulkIntegralReconstructionData.globalBulkIntegral_eq_localBulkSum`.

Expected theorem name:

```lean
theorem bulkIntegralLocalizes_of_indicator_partition ...
```

The proof should split the global bulk integrand into the interior localized
pieces plus boundary-chart bulk pieces, use `integral_finset_sum` on the
combined finite index set, and then transport each term to
`LocalizedInteriorPieces.bulkTerm` or
`BoundaryPieceFamilyInput.boundaryBulkTerm`.

### M8-MEAS-04: boundary measure reconstruction

Fill:

- `BoundaryIntegralPartitionReconstructionData.boundaryMeasureIntegral_eq_partitionSum`;
- then `BoundaryIntegralReconstructionData.manifoldBoundaryIntegral_eq_selectedBoundarySum`
  through the existing wrapper.

Expected theorem name:

```lean
theorem boundaryMeasureIntegral_eq_partitionSum_of_indicator_partition ...
```

This is the boundary analogue of M8-MEAS-03. The key difference is that the
base measure and local integrands are boundary-measure objects with orientation
signs already folded into `boundaryPartitionTerm`.

### M8-MEAS-05: natural input constructor

After M8-MEAS-03 and M8-MEAS-04, add a constructor for
`NaturalGlobalStokesInput` that takes genuine compact-support integration data
and produces:

- `bulkReconstruction`;
- `boundaryReconstruction`;
- `selectedPartition_active`;
- the unchanged local, artificial-face, and chart-change packages.

This should remain a wrapper; the analytic work belongs to the previous
targets.

## Remaining Blockers

1. Genuine integrals are still not defined at the final theorem boundary.
   `NaturalGlobalStokesInput` carries represented real numbers, not yet
   canonical definitions of `integral_M (d omega)` and
   `integral_boundary_M omega`.
2. The global and boundary integrands need final names. In practice these are
   top-degree coefficient densities in charts, with orientation/Jacobian
   conventions fixed by the local chart and boundary chart layers.
3. Measurability and integrability must be proved for every indicator-local
   term. The expected ingredients are compact support, selected-box containment,
   chartwise smoothness, and finite dimensionality.
4. The a.e. reconstruction theorem must connect form-level
   `localizedFormSum` / `extDeriv` reconstruction to scalar integrand
   reconstruction. The existing `LocalizedFormEventuallyEqData` and
   exterior-derivative reconstruction APIs are the likely bridge.
5. Each local indicator integral must be identified with the existing local
   term definitions: `projectInteriorBulkIntegral`, `projectLocalBulkIntegral`,
   and the chosen boundary `boundaryPartitionTerm`.
6. Boundary orientation and boundary measure reconstruction remain fieldized.
   M8 can package the indicator theorem, but a later worker must still connect
   it to the induced boundary orientation API.
7. Active-set alignment must stay consistent across selected partition data,
   localized interior pieces, boundary pieces, and mixed reconstruction. The
   existing wrappers already expect this, so M8 should avoid introducing a
   second indexing convention.

## Suggested Claim Order

1. Prove a generic `chartPieceSum`/indicator finite-integral lemma over a
   flattened sigma finite set.
2. Use it to construct `LocalIntegralFiniteAdditivityData` from an a.e.
   indicator reconstruction.
3. Specialize the constructor to bulk reconstruction and fill
   `BulkIntegralPartitionInput.bulkIntegralLocalizes`.
4. Specialize the same pattern to boundary measure reconstruction and fill
   `BoundaryIntegralPartitionReconstructionData.boundaryMeasureIntegral_eq_partitionSum`.
5. Only after those fields are theorem-produced, add the natural-input
   constructor that feeds `naturalGlobalStokes`.

## Verification

This is a documentation-only report. I did not run `lake build`.

Placeholder scan performed:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

Result: no matches.
