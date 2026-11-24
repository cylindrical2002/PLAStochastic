import PLAStochastic.Index.KEP.PivotStopping
import PLAStochastic.ForMathlib.Probability.OrderStatistics.GammaRatio

/-!
# The anchored Model K sample

After a reset at an anchor with value `u`, the remaining keys of a Model K sample are
`Q u, Q (u + (1-u) w₀), …, Q (u + (1-u) w_{M-1})` for a fresh sorted uniform sample `w`
of size `M` (`PLAStochastic.Index.KEP.OrderStatisticReset`).  This file only fixes the shared definitions:

* `anchPairsW Q u w`: the anchored base pair sequence (counts `1`), zero gaps after key `M`;
* `anchPairs Q u M ω`: the same, with `w = gammaRatio (ω 0, …, ω M)` on the canonical
  exponential sequence space, so that `w` has the sorted uniform law;
* `refPairsE ω`: the affine reference pair sequence with gaps `ω t`.
-/

namespace PGM

noncomputable section

/-- Position of anchored key `t`: `0` at the anchor, `w (t-1)` for `1 ≤ t ≤ M`, else `0`. -/
def anchPos {M : ℕ} (w : Fin M → ℝ) (t : ℕ) : ℝ :=
  if h : 1 ≤ t ∧ t ≤ M then w ⟨t - 1, by omega⟩ else 0

/-- Anchored base pairs: keys `Q (u + (1-u) · anchPos w t)` for `t ≤ M`, zero gaps afterwards. -/
def anchPairsW (Q : ℝ → ℝ) (u : ℝ) {M : ℕ} (w : Fin M → ℝ) : ℕ → ℝ × ℕ := fun t =>
  (if t < M then Q (u + (1 - u) * anchPos w (t + 1)) - Q (u + (1 - u) * anchPos w t) else 0, 1)

/-- The anchored model on the canonical exponential sequence space. -/
def anchPairs (Q : ℝ → ℝ) (u : ℝ) (M : ℕ) (ω : ℕ → ℝ) : ℕ → ℝ × ℕ :=
  anchPairsW Q u (Renyi.gammaRatio (fun i : Fin (M + 1) => ω i))

/-- The affine reference pair sequence: gaps `ω t`, counts `1`. -/
def refPairsE (ω : ℕ → ℝ) : ℕ → ℝ × ℕ := fun t => (ω t, 1)

end

end PGM
