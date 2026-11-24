import PLAStochastic.Index.CEPS.Band.Main
import PLAStochastic.Index.CEPS.Band.ClassicalWidth

/-!
# Fixed-drift killed-band budgets with classical width derivatives

`Main` supplies the previously established coarse budgets and `C¹,¹` control.
`ClassicalWidth` closes pointwise second differentiability under the explicit
hypothesis that the density is differentiable everywhere with bounded derivative.
The density derivative need not be continuous. All closed-window width statements
hold for `w ≥ 4` and `Re q ≥ -κ/(64w²)`, including both endpoints.
-/
