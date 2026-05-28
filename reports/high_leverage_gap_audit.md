# High-leverage gap audit

Worker H scope:

- Added `Stokes/Global/HighLeverageGapAudit.lean`.
- Did not modify public imports or facade files.
- No new analytic, orientation, inverse-function, change-of-variables, or measure-localization theorem is claimed.

## Lean artifacts

- `HighLeverageNearestEndpointRoute`
  - Precise audit package for the nearest compact-support route after `NaturalCompactSupportPartitionConstructorData`.
  - Its remaining large inputs are:
    - `NaturalCompactSupportEndpointEndToEndSources`
    - `LocalizedInteriorM8ChartAlignment`
    - endpoint `SelectedBoxStrictMarginData`

- `NaturalCompactSupportEndpointEndToEndSources.EndpointSelectedBoxStrictMargins`
  - Endpoint-local abbreviation for the existing selected-box strict-margin package.

- `NaturalCompactSupportEndpointEndToEndSources.localizedPieceStrictMarginsOfSelectedStrictMargins`
  - New high-yield constructor.
  - Converts endpoint selected-box strict margins into the compact-active localized-piece margin package consumed by the strict-buffer route.

- `NaturalCompactSupportEndpointEndToEndSources.canonical_stokes_ofM8ChartAlignmentAndSelectedStrictMargins`
  - New theorem form that consumes one packaged strict-margin witness instead of two raw pointwise strict-margin functions.

- `NaturalCompactSupportEndpointEndToEndSources.manifoldExtDerivIntegral_eq_boundaryFormIntegral_ofM8ChartAlignmentAndSelectedStrictMargins`
  - Same route in final equality form.

- `HighLeverageBoundaryTargetPackage`
  - Audit package recording that the current largest boundary target-image input is now `M8BoundaryControlledTargetInput`.

- `HighLeverageChartBoxPackage`
  - Audit package recording that the current largest natural chart-box input is `NaturalFiniteActiveChartBoxSelectionData`.

## What this kills

Before this file, the end-to-end canonical theorem still exposed:

```lean
pieceLower_lt_compactLower :
  ∀ x, x ∈ selectedPartition.active → ∀ j,
    piece.lowerCorner j < compactActive.lower x j

compactUpper_lt_pieceUpper :
  ∀ x, x ∈ selectedPartition.active → ∀ j,
    compactActive.upper x j < piece.upperCorner j
```

The new constructor lets callers pass the existing endpoint selected-margin package instead:

```lean
margins : E.EndpointSelectedBoxStrictMargins
```

This is not just cosmetic: it makes the next real geometric target “construct selected strict margins from chart-box selection” instead of threading two loose functions through every theorem.

## Biggest remaining packaged inputs

Priority 1: `NaturalCompactSupportEndpointEndToEndSources`

This still hides the heaviest mixed endpoint assumptions: boundary source alignment, boundary chart-change/COV route, selected reconstruction source, bulk local canonical facts, volume-measure identification, and boundary face continuity.

Priority 2: `M8BoundaryControlledTargetInput`

This is the current best boundary target-image package.  It is close to the IFT/local-inverse route, but still requires global assembly fields and target/partition selected boxes.

Priority 3: `NaturalFiniteActiveChartBoxSelectionData`

This is the cleanest chart-box selection package.  It still depends on genuine finite-active compact support selection, chart-box containment, and smoothness neighborhoods.

Priority 4: `LocalizedInteriorM8ChartAlignment`

This is still a visible chart-label compatibility witness between selected partition pieces and M8 localized pieces.

Priority 5: `EndpointSelectedBoxStrictMargins`

After this audit, this is the preferred strict-margin target.  The next theorem should construct it from real selected inner/outer chart boxes.

## Next 5 agent targets

1. `Stokes/Global/LocalizedPieceStrictMarginsAuto.lean`
   - Lemma to attack: `endpointSelectedBoxStrictMarginsOfNaturalChartBoxSelection`
   - Goal: build `EndpointSelectedBoxStrictMargins` from the selected chart-box/inner-outer construction, instead of asking for the package as an input.

2. `Stokes/BoundaryChart/ControlledTargetBoxFromIFTAuto.lean`
   - Lemma to attack: remove the remaining `compactBox_subset` / `hcontains` style fields from the IFT selected-box route.
   - Goal: construct controlled target boxes directly from selected box + local openness/IFT + compact image cover.

3. `Stokes/Global/BoundaryControlledTargetToM8Auto.lean`
   - Lemma to attack: `BoundarySourceAlignmentUnifiedData.toM8BoundaryControlledTargetInput`.
   - Goal: make `M8BoundaryControlledTargetInput` emerge from the unified boundary source package, not from manually assembled fields.

4. `Stokes/Global/NaturalCompactSupportEndpointEndToEndAuto.lean`
   - Lemma to attack: public end-to-end selected-margin theorem using the constructor added in this audit.
   - Goal: replace raw localized-piece strict-margin theorem forms with selected-margin theorem forms in the endpoint-facing route.

5. `Stokes/Global/BulkMeasureCanonicalLocalFacts.lean` or `Stokes/Global/BulkExtDerivProjectLocalAuto.lean`
   - Lemma to attack: construct `SelectedPartitionBulkCanonicalLocalFacts` from the partition reconstruction/ext-derivative locality route.
   - Goal: reduce the largest bulk-side mathematical package inside `NaturalCompactSupportEndpointEndToEndSources`.

## Recommended next wave shape

The next parallel wave should be split by ownership, not by theorem names:

- one agent on selected strict margins from chart-box geometry;
- one agent on controlled target boxes from IFT/local openness;
- one agent on boundary controlled target input from unified boundary data;
- one agent on bulk canonical local facts;
- one agent on promoting the selected-margin endpoint theorem into the public facade after the above files stabilize.

