# Stokes M8 Field Reduction Report

Scope: documentation-only worker output for the current Lean 4 Stokes
workspace. No Lean source files were changed.

Date: 2026-05-24.

## Executive Summary

This round reduced several broad "supply this field by hand" obligations into
smaller theorem-backed packages, but the final M8 statement is still conditional
on explicit analytic data.

The strongest real progress is around finite sums and measure localization:
indicator support lemmas, pure Bochner finite-sum localization, boundary
measure reconstruction, boundary COV finite-sum transport, and artificial-face
cancellation wrappers are all proved in Lean.  The M8 theorem itself is also a
proved wrapper, but it proves Stokes only after the M8 input supplies the
remaining measure-localization, target-image, boundary-orientation, and
artificial-face packages.

## Truly Proved This Round

These declarations are theorem-backed in the current Lean sources; they are not
new axioms or `sorry` placeholders.

| Area | Main declarations | What is genuinely proved |
|---|---|---|
| Indicator support localization | `Stokes/Global/IndicatorSupportLocalization.lean` | Inserting set or box indicators is pointwise or a.e. equal to the original function/sum when support containment or vanishing off the set is known.  Includes finite-sum and common-support variants. |
| Pure measure finite-sum localization | `Stokes/Global/MeasureIntegralLocalization.lean`: `integral_eq_finset_sum_setIntegral_of_ae_eq_sum_indicator`, `integral_eq_finset_sum_setIntegral_of_support_subset` | A Bochner integral of a global integrand is rewritten as a finite sum of local set integrals from an a.e. finite indicator reconstruction plus integrability. |
| Boundary measure finite-sum localization | `Stokes/Global/BoundaryMeasureLocalization.lean`: `boundaryMeasureIntegral_eq_selectedBoundaryPieceSum_of_ae_eq`, `boundaryMeasureIntegral_eq_selectedBoundaryPieceSum_of_ae_indicator_eq`, `BoundaryMeasureLocalizationData.boundaryMeasureIntegral_eq_selectedBoundaryPieceSum` | Given an arbitrary boundary measure, an a.e. indicator decomposition, integrability, and per-piece integral identifications, the boundary measure integral equals the selected boundary-piece finite sum. |
| Boundary COV to measure reconstruction | `Stokes/Global/BoundaryCOVMeasureConstructor.lean`: `pointwise_sourceBoundaryTerm_eq_partitionTerm`, `sourceBoundarySum_eq_partitionSum`, `boundaryMeasureIntegral_eq_projectLocalPartitionSum` | Finite boundary COV families transport source boundary terms to the chosen partition terms, and can fill boundary partition reconstruction once the boundary measure integral is identified with the COV source sum. |
| Bulk localization bookkeeping | `Stokes/Global/BulkIntegralLocalizationConstructor.lean`: `BulkMeasureLocalizationTermFields.globalBulkIntegral_eq_integrandLocalSum`, `BulkMeasureLocalizationTermFields.bulkIntegralLocalizes`, `BulkIntegralLocalizationInput.bulkIntegralLocalizes` | The existing `BulkIntegralPartitionInput.bulkIntegralLocalizes` field is derived from smaller local measure-term, a.e.-replacement, integrability, and box-identification packages. |
| Artificial-face output reduction | `Stokes/Global/ArtificialFaceFieldReduction.lean`: `ArtificialFaceResolvedData`, `of_forall_eq_zero`, `ofInteriorSupportZero`, `ofOverlapPairing`, `ofCoordinateOverlapPairing`, `ofAdjacentSelectedFaces`, `to_interiorBoundaryCancellation` | Multiple existing artificial-face resolution routes now project to one small resolved-cancellation package consumed by global constructors. |
| Target-image field reduction | `Stokes/BoundaryChart/TargetImageFieldReduction.lean`: `BoundaryChartTargetImageResolvedFamily` and its COV-family constructors | Separate target lower/upper corner, compact-image, and local-inverse projections are recovered from one `targetBox` source of truth.  This reduces duplicated target-image fields, while still requiring `targetBox` itself. |
| Remaining-field minimization | `Stokes/Global/RemainingFieldsMinimized.lean` | Once `PartitionReconstructionData` is available, the final global theorem needs exactly the minimized local-Stokes, artificial-cancellation, and chart-change fields, and those fields construct both `GlobalStokesData` and `MixedGlobalStokesData`. |
| Natural measure wrapper and M8 statement | `Stokes/Global/NaturalMeasureConstructor.lean`, `Stokes/Global/M8Statement.lean`: `NaturalMeasureStokesInput.stokes`, `naturalMeasureStokes`, `M8GlobalStokesInput.stokes`, `m8GlobalStokes` | The measure-level global Stokes equality is proved from the current natural global Stokes theorem plus bulk and boundary measure-localization fields.  This is a real wrapper proof, not a new analytic proof. |

## Still Fieldized

The main analytic and geometric content is still carried as explicit fields.

| Remaining fieldized layer | Representative fields or structures | What is still missing |
|---|---|---|
| Final global integral definitions | `GlobalIntegralInterface`, represented `Real` fields in global packages | No canonical definition yet of the manifold integral of `d omega` or the induced-boundary integral of `omega`. |
| M8 measure localization | `M8MeasureLocalizationData.globalBulkIntegral_eq_bulkMeasureIntegral`, `bulkMeasureIntegral_eq_localBulkSum`, `globalBoundaryIntegral_eq_boundaryMeasureIntegral`, `boundaryMeasureIntegral_eq_partitionSum` | M8 still assumes the bulk and boundary measure integrals and their finite-sum reconstructions. |
| Bulk analytic localization | `BulkMeasureLocalizationTermFields.bulkMeasureIntegral_eq_measureSum`, `BulkIntegrandAELocalFields`, `CompactSupportIntegrability`, `MeasureBoxAPI` | The finite bulk measure split, a.e. scalar-integrand replacement, active-piece integrability, and identification with box terms are not yet derived from compact support and chart definitions. |
| Boundary analytic localization | `BoundaryMeasureLocalizationData.boundaryMeasureIntegral_eq_integral`, `boundaryIntegrand_ae_eq_indicatorSum`, `boundaryPieceIntegrable`, `boundaryPartitionTerm_eq_integral` | The pure theorem exists, but an actual boundary measure, boundary integrand, per-piece integrands, and integral identifications must still be supplied. |
| Boundary target images | `BoundaryChartTargetImageResolvedFamily.targetBox`, `targetSelectedBox`; M8 `targetImages_source_mem`, `targetImages_boundarySource_mem`, `targetBoundaryTerm_eq_partition` | Target boxes and oriented-atlas membership are reduced but not constructed from general chart geometry. |
| Artificial-face geometry | Pairing fields in `ArtificialFaceOverlapPairingData`, selected-face adjacency data, or support-zero hypotheses | The final cancellation package is small, but a genuine geometric construction of the pairing/support-zero input is still required. |
| Partition and localized pieces | `SelectedBoxPartitionOfUnity`, `LocalizedInteriorPieces`, `BoundaryPieceFamilyInput` | Compact-support-to-partition construction, localized piece construction, and boundary-piece family construction remain explicit input data. |
| Boundary orientation | `BoundaryChartOrientedAtlas`, `BoundaryChartOrientedManifold` inputs | The induced boundary orientation from a smooth oriented manifold with boundary is still not connected to the global statement. |

## Net Field Reduction

The current shape has moved from one large monolithic "global Stokes data"
field package toward three smaller front doors:

1. Measure localization for represented bulk and boundary integrals.
2. Resolved artificial-face cancellation for localized interior pieces.
3. Target-image/COV data for boundary chart pieces.

That is a real reduction in field surface area: downstream M8 wrappers no
longer need to see every finite-sum alignment detail.  However, the most
mathematical fields are still present at the interfaces above.  In particular,
`m8GlobalStokes` is best described as a conditional M8-facing theorem, not yet
as the final compact-support Stokes theorem.

## Next Minimal Target

The smallest next Lean target should be boundary-side, because the pure measure
localization theorem already exists.

Recommended next declaration:

```lean
def M8MeasureLocalizationData.ofBoundaryMeasureLocalization ...
```

or an equivalent constructor that replaces the direct
`M8MeasureLocalizationData.boundaryMeasureIntegral_eq_partitionSum` field by a
`BoundaryMeasureLocalizationData` input and derives the partition-sum equality
using:

```lean
BoundaryMeasureLocalizationData.boundaryMeasureIntegral_eq_selectedBoundaryPieceSum
```

Keep the represented-boundary equality
`globalBoundaryIntegral_eq_boundaryMeasureIntegral` as a field for that first
step.  This removes exactly one M8 field without touching bulk localization,
chart construction, or induced orientation.

After that lands, the next analogous bulk target is a constructor deriving
`BulkMeasureLocalizationTermFields.bulkMeasureIntegral_eq_measureSum` from
`integral_eq_finset_sum_setIntegral_of_ae_eq_sum_indicator`, leaving the
per-piece box-identification fields intact.

## Verification

Requested placeholder scan:

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

Result: no Lean placeholders matched.
