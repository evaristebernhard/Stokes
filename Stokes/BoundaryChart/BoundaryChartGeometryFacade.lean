import Stokes.BoundaryChart.Basic
import Stokes.BoundaryChart.SelectedBox
import Stokes.BoundaryChart.LocalInverse
import Stokes.BoundaryChart.TransitionDerivative
import Stokes.BoundaryChart.TransitionCompactBox
import Stokes.BoundaryChart.BoundaryBoxSelection
import Stokes.BoundaryChart.TargetBoxSelection
import Stokes.BoundaryChart.TargetBoxFromIFT
import Stokes.BoundaryChart.TargetBoxCompactImage
import Stokes.BoundaryChart.TargetBoxSourceShrink
import Stokes.BoundaryChart.TargetBoxSourceShrinkInverse
import Stokes.BoundaryChart.TargetBoxSourceShrinkIFT
import Stokes.BoundaryChart.SelectedImageBoxContainmentFromShrinkAuto
import Stokes.BoundaryChart.LaterTargetShrinkFromSelectionAuto
import Stokes.BoundaryChart.ConstrainedTargetBoxSelectionAuto
import Stokes.BoundaryChart.ControlledTargetBoxFromLocalInverseAuto
import Stokes.BoundaryChart.ControlledTargetBoxFromIFTAuto
import Stokes.BoundaryChart.CompactImageBoxContainmentAuto
import Stokes.BoundaryChart.ControlledTargetNoContainmentAuto
import Stokes.BoundaryChart.ControlledTargetFromSourceShrinkCoverAuto
import Stokes.BoundaryChart.SelectedTargetBoxFromControlledCoverAuto

/-!
# Boundary chart geometry facade

This module is a pure boundary-chart geometry import facade.  It collects the
stable selection, local-inverse, target-box, source-shrink, controlled target
selection, and later-target shrink APIs used by downstream boundary-chart work.

The facade deliberately does not import `TargetBoxToM8Glue`: that module imports
global/M8 assembly material and belongs on the global integration side of the
project, not in the reusable boundary geometry layer.
-/
