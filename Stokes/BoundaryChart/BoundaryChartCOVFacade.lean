import Stokes.BoundaryChart.ChangeOfVariablesFamily
import Stokes.BoundaryChart.OrientedAtlasSelectedBoxCOV
import Stokes.BoundaryChart.BoundaryChartPositiveJacobianFromAtlas
import Stokes.BoundaryChart.SelectedBoxCOVFromOrientationAuto
import Stokes.BoundaryChart.SelectedBoxContainsAuto
import Stokes.BoundaryChart.SelectedImageBoxFromTargetAuto
import Stokes.BoundaryChart.SourceShrinkMapsToAuto
import Stokes.BoundaryChart.SelectedImageBoxContainmentFromShrinkAuto
import Stokes.BoundaryChart.LaterTargetShrinkFromSelectionAuto
import Stokes.BoundaryChart.ConstrainedTargetBoxSelectionAuto
import Stokes.BoundaryChart.SourceShrinkSelectedCOVFacade
import Stokes.BoundaryChart.SourceShrinkSelectedCOVFromShrinkAuto

/-!
# Boundary chart COV facade

This module is a thin public import facade for boundary-chart
change-of-variables work.

It deliberately stays inside `Stokes.BoundaryChart`: global/M8 assembly files
should import this facade when they need the boundary COV API, while local
geometry files should continue importing the narrower implementation modules
they actually prove against.

The facade includes the source-shrink route up through the selected-image-box
containment, controlled target boxes, later-target shrink data, and selected
COV wrappers, but deliberately does not import `TargetBoxToM8Glue`, which
belongs to the global/M8 assembly layer.
-/
