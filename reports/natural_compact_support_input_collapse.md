# Natural compact-support input collapse audit

## Added constructors

- `NaturalCompactSupportCanonicalPiecesCollapsedInput`
  - Chooses `K := formData.supportSet`.
  - Chooses `hK := formData.isCompact_supportSet`.
  - Fills the old `supportSet_eq` field by `rfl`.
  - Constructs the existing `NaturalCompactSupportCanonicalPiecesInput`.
  - Constructs the endpoint `NaturalCompactSupportStokesInput`.
  - Proves `canonical_stokes`.

- `NaturalCompactSupportLocalFactsCollapsedInput`
  - Makes the same support-set collapse.
  - Constructs `bulkExtDerivInput` from `bulkLocalFacts`, `measureTerms`,
    `extDerivAE`, and the three bulk integral-identification fields.
  - Constructs `boundaryCOVInput` from `boundarySupportCOV`.
  - Constructs `NaturalCompactSupportCanonicalPiecesCollapsedInput`.
  - Constructs the endpoint `NaturalCompactSupportStokesInput`.
  - Proves `canonical_stokes`.

## Dependency graph

```text
formData
  -> supportSet := formData.supportSet
  -> hK := formData.isCompact_supportSet
  -> supportSet_eq := rfl

selection + smoothness
  -> selectedPartition
  -> compact active boxes through existing selected-box constructors

bulkLocalFacts
  + measureTerms
  + extDerivAE
  + globalBulkIntegral_eq_integral
  + interiorBulkTerm_eq_integral
  + boundaryBulkTerm_eq_integral
  -> SelectedPartitionBulkMeasureExtDerivInput
  -> BulkMeasureFromPartitionData

boundarySupportCOV
  -> BoundaryMeasureFromTargetCOVInput
  -> CanonicalBoundaryTargetCompactSupportInput

canonical bulk + canonical boundary + localizedChartAlignment + strictMargins
  -> NaturalCompactSupportCanonicalPiecesInput
  -> NaturalCompactSupportEndToEndInput
  -> NaturalCompactSupportStokesInput
  -> naturalCompactSupportStokes_canonical
```

## Minimal remaining fields

After this collapse, the remaining fields are not bookkeeping in the current
API. They still require mathematical construction or upstream theorems:

- `formData`: compact support, support containment, and chartwise smoothness.
- `selection` and `smoothness`: finite active chart selection and selected box
  smoothness.
- `orientedBoundaryAtlas`: oriented boundary chart data.
- `targetImageInput`: target-image geometry, selected boundary pieces, and
  oriented change-of-variables data.
- `localized`, `measureTerms`, `extDerivAE`, `bulkLocalFacts`: the selected
  local exterior-derivative and scalar bulk-measure facts.
- The three bulk integral-identification fields:
  `globalBulkIntegral_eq_integral`, `interiorBulkTerm_eq_integral`, and
  `boundaryBulkTerm_eq_integral`.
- `boundarySupportCOV`: finite boundary piece sums, boundary measure integral,
  source project-local set-integral theorem, and global-boundary equality.
- `localizedChartAlignment`: identification of localized measure pieces with
  selected chart labels.
- `strictMargins`: strict inner/outer selected-box inequalities needed by the
  artificial-face cancellation route.

No further field was eliminated in this module because the current imported
API does not provide constructors for these remaining geometric, analytic, or
measure-identification facts from earlier fields alone.
