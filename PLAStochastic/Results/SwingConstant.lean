import PLAStochastic.Swing.ConstantEvaluation.KernelRewardIteration
import PLAStochastic.Swing.Transient.Coefficients.Exact

/-!
# Swing stationary constant: actual-coefficient brackets and kernel-reward iteration

S-BRACKET: the actual segment coefficients `c_k = α₂ T^{k-3} h` alternate around the
stationary constant `γ_Swing`, the even offsets decreasing and the odd offsets increasing to
it, with `|c_k - γ_Swing| ≤ L_h W₁(α₂, λ) (3/4)^{k-3}`. Also the geometric approximation of
`γ_Swing` by the stationary slope-kernel reward iteration.

## Main theorems

* `SwingRepair.swing_transient_brackets`
* `SwingRepair.theorem_I1_swing_gaussian`
-/
