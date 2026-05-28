# Target-box Geometry Decision

## Decision

Prefer the source-shrink route over the large compact-image target-box route.

The obstruction is structural: local openness can choose a small target
lower-zero box contained in the image of a source box, but that does not imply
the image of the whole source box is contained in that same small target box.
So the field
`boundaryChartCompactCoordinateImageForLocalInverseTargets` should not be
derived from local openness alone.

## Formalized Progress

`Stokes/BoundaryChart/TargetBoxSourceShrink.lean` now proves the honest
continuity half of the source-shrink route:

```text
continuousAt boundaryChartTransition at u
+ original source box is a neighborhood of u
+ fixed target box is a neighborhood of f u
=> there exists a shrunken source lower-zero box
   inside the original source box
   whose image maps into the fixed target box.
```

This is packaged as:

- `BoundaryChartSourceShrinkMapsToData`
- `nonempty_boundaryChartSourceShrinkMapsToData_of_continuousAt`
- `BoundaryChartSourceShrinkTargetBoxData`

The module also records the comparison route:

- `BoundaryChartCompactImageTargetBoxRoute`

This route chooses a target box large enough to contain the compact image, but
then must prove local-inverse data on that same large target box.

## Remaining Blocker

The source-shrink route still needs the inverse half:

```text
local inverse target box -> shrunken source box
```

A local inverse landing in the original source box is not enough. Downstream
geometry should either:

1. choose source and target boxes simultaneously from a local homeomorphism /
   inverse-function package, or
2. prove continuity/control of the local inverse and shrink the target box so
   its inverse image lands in the chosen shrunken source box.

The large target-box route remains possible, but its hard field is stronger in
practice: the compact-image bounding box may be too large to lie in the local
image where the inverse theorem applies.
