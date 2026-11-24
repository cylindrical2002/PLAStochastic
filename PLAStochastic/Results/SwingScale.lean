import PLAStochastic.Swing.SecondSegment.MeanLowerBound
import PLAStochastic.Swing.Transient.LaterSegmentLogOrder
import PLAStochastic.Swing.Transient.Coefficients.Exact

/-!
# S-SCALE: native Swing segment-length scales

Linear order of the second segment and `E log E` order of every fixed later segment, with the
geometric limsup bound towards the stationary constant; the first-restart entrance law
`ρ = θ Law(-O) + (1 - θ) Law(-(U + O))`; and the exact constants
`κ₂ = 2 ∫ a⁻¹ α₂(da)` and `c_k = α₂ T^{k-3} h` with `α₂ = ρ𝖠`.

## Main theorems

* `SwingRepair.secondSegment_mean_le`
* `SwingRepair.secondSegment_mean_ge`
* `SwingRepair.theorem_4_4_swing_gaussian`
* `SwingRepair.nativeTransientMarginProb_tendsto_entranceLaw`
* `SwingRepair.swing_transient_coefficients`
-/
