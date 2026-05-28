# Current gap-reduction audit

Worker H scope:

- Added `Stokes/Global/CurrentGapReductionAudit.lean`.
- Did not modify public imports or facade files.
- No new analytic theorem is claimed; the Lean file is an audit/projection layer plus one constructor.

## Lean artifacts

- `CurrentEndpointAutomatedFields D`
  - formalizes fields already generated once a `NaturalCompactSupportEndToEndInput` exists:
    `measureBuilder`, `strictAlignment`, and the final `NaturalCompactSupportStokesInput`.

- `CurrentEndpointMathematicalFields D`
  - formalizes the fields that are still real proof obligations in the current route:
    bulk measure localization, boundary target/measure route, compact-active/selected-box alignment,
    localized-piece alignment, and the two strict margin inequalities.

- `CurrentEndpointGlueFields I omega BoundaryPiece μ`
  - formalizes the object-selection layer:
    `formData`, `orientedBoundaryAtlas`, `selectedPartition`,
    `selectedPartition_supportSet`, `targetImageInput`, `globalBulkIntegral`,
    and `compactActiveBoxes`.

- `CurrentEndpointGlueFields.toEndToEndInputOfStrictAlignment`
  - low-risk constructor added in this audit.
  - If a caller already has `NaturalMeasureStrictBuilderAlignment`, the constructor builds
    `NaturalCompactSupportEndToEndInput` without separately passing
    `selectedPartitionAlignment`, `localizedPieceAlignment`, and the two strict-margin fields.

## Already automated

- `boundaryTarget.toMeasureBuilderData bulk` builds the compact-support measure builder.
- `NaturalCompactSupportEndToEndInput.measureBuilder` is a definitional projection of that builder.
- `NaturalCompactSupportEndToEndInput.naturalMeasureStrictBuilderAlignment` packages the selected-box alignment, localized-piece alignment, strict margins, and the boundary-term equality supplied by `boundaryTarget`.
- `NaturalCompactSupportEndToEndInput.toNaturalCompactSupportStokesInput` builds the current natural compact-support theorem input.
- Downstream endpoint theorem wrappers already turn this input into the canonical Stokes equality.
- Recent strict-buffer / artificial-face modules already turn strict-buffer alignment into artificial-face cancellation data.
- Recent partition constructor modules already reduce support-set bookkeeping from compact-support form data and finite-active selection.

## Still mathematical proof

- Construct the actual `bulk : BulkMeasureFromPartitionData` from the chartwise exterior-derivative measure story, not as an input.
- Construct the actual `boundaryTarget : CanonicalBoundaryTargetCompactSupportInput` from boundary chart COV, orientation compatibility, and lower-dimensional boundary measure data.
- Produce `CompactActiveBoxData` and `CompactActiveSelectedPartitionAlignment` from the chosen compact-support chart-box selection in the final natural route.
- Prove the localized-piece alignment between selected labels and M8 localized pieces from the real localized chart construction.
- Prove the strict margin inequalities showing compact active boxes lie strictly inside localized-piece boxes.
- Finish the target-box/local-inverse/IFT route that supplies controlled boundary chart image boxes.
- For the singular-cube route, prove the remaining ext-derivative locality/congruence theorem from equality on neighborhoods.

## Mostly engineering glue

- Choosing which endpoint route should become the public theorem-facing facade.
- Deciding whether the final public API should expose `NaturalCompactSupportEndToEndInput`, the new glue-field constructor, or a more natural constructor from partition data plus boundary route data.
- Consolidating scattered facade modules once the hard fields above are constructed.
- Adding public imports only after the constructor layer is stable; this audit intentionally avoided public-entry changes.

## Net reduction

This audit does not remove a mathematical assumption. It removes one wiring shape:
callers with an existing `NaturalMeasureStrictBuilderAlignment` can now assemble
the end-to-end input directly from glue fields, `bulk`, `boundaryTarget`, and that
single alignment package.

The next useful reduction is to build that strict alignment automatically from
the localized chart-box construction, because that would discharge the two strict
margin fields and the localized-piece alignment at the same time.
