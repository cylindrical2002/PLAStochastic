import PLAStochastic.Index.GEP.Kernel.Row.Long.TimeWeighted

/-!
# WP4 kernel rows: the actual exponentially weighted Green series

The four partial-sum bounds in `GEPKernelRowWeighted` imply summability and the
same bounds for the actual infinite killed-kernel sums. The weight range remains
`0 ≤ ε ≤ krKappa / 16`; no smaller cutoff from the long-row decomposition is used.
Survival starts at time zero, while density sums start at time one.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-- The exponentially weighted boundary occupation series is summable. -/
theorem summable_expw_krSurv_bdry {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    Summable fun n : ℕ =>
      Real.exp (ε * n / w ^ 2) * krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b :=
  summable_of_sum_range_le
    (fun n => mul_nonneg (Real.exp_pos _).le (krSurv_nonneg H.hJ ν β a' n b))
    (sum_expw_krSurv_bdry_le ν H hb hε0 hε)

/-- The actual weighted occupation Green sum has the same uniform bound as its partial sums. -/
theorem tsum_expw_krSurv_bdry_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    ∑' n : ℕ, Real.exp (ε * n / w ^ 2) * krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤
      Real.exp (3 * ε) *
        ((krCO D K L vlo vhi + 4 * krC₃ D K L / krKappa D vlo vhi) * (1 + A) * w) :=
  Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (Real.exp_pos _).le (krSurv_nonneg H.hJ ν β a' n b))
    (sum_expw_krSurv_bdry_le ν H hb hε0 hε)

/-- The actual density representatives form a summable weighted Green row at every endpoint. -/
theorem summable_expw_krDens_bdry_row {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) (z : ℝ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    Summable fun n : ℕ => Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
      krDens (Icc 0 w) ν f β a' (n + 1) b z :=
  summable_of_sum_range_le
    (fun n => mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν H.hf0 (n + 1) b z))
    (sum_expw_krDens_bdry_row_le ν H hb z hε0 hε)

/-- The weighted Green row is bounded pointwise, uniformly in its terminal location. -/
theorem tsum_expw_krDens_bdry_row_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) (z : ℝ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    ∑' n : ℕ, Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
        krDens (Icc 0 w) ν f β a' (n + 1) b z ≤
      Real.exp (3 * ε) * ((krCG D K L vlo vhi + 4 * krC₄ D K L / krKappa D vlo vhi) *
        (1 + A) * (1 + Real.log w)) :=
  Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν H.hf0 (n + 1) b z))
    (sum_expw_krDens_bdry_row_le ν H hb z hε0 hε)

/-- The exponentially weighted opposite-side pin series is summable. -/
theorem summable_expw_krDens_bdry_pin {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w) {b b' : ℝ}
    (hb : b = 0 ∨ b = w) (hb' : b' = 0 ∨ b' = w) (hbb : b ≠ b')
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    Summable fun n : ℕ => Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
      krDens (Icc 0 w) ν f β a' (n + 1) b b' :=
  summable_of_sum_range_le
    (fun n => mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν H.hf0 (n + 1) b b'))
    (sum_expw_krDens_bdry_pin_le ν H hAw hb hb' hbb hε0 hε)

/-- The opposite-side weighted Green pin keeps its inverse-square-root bandwidth bound. -/
theorem tsum_expw_krDens_bdry_pin_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w) {b b' : ℝ}
    (hb : b = 0 ∨ b = w) (hb' : b' = 0 ∨ b' = w) (hbb : b ≠ b')
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    ∑' n : ℕ, Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
        krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      Real.exp (3 * ε) * ((krCP D θ K L vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi) *
        (1 + A) ^ 2 / Real.sqrt w) :=
  Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (Real.exp_pos _).le (krDens_nonneg ν H.hf0 (n + 1) b b'))
    (sum_expw_krDens_bdry_pin_le ν H hAw hb hb' hbb hε0 hε)

/-- Adding the length-and-width reward preserves summability for any pair of boundaries. -/
theorem summable_expw_weighted_krDens_bdry_pin {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ}
    (hb : b = 0 ∨ b = w) (hb' : b' = 0 ∨ b' = w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    Summable fun n : ℕ => Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
      (((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b') :=
  summable_of_sum_range_le
    (fun n => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (by linarith [H.hw0, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        (krDens_nonneg ν H.hf0 (n + 1) b b')))
    (sum_expw_weighted_krDens_bdry_pin_le ν H hb hb' hε0 hε)

/-- The actual length-weighted Green pin sum is linear in the bandwidth. -/
theorem tsum_expw_weighted_krDens_bdry_pin_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ}
    (hb : b = 0 ∨ b = w) (hb' : b' = 0 ∨ b' = w)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    ∑' n : ℕ, Real.exp (ε * ((n + 1 : ℕ) : ℝ) / w ^ 2) *
        (((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b') ≤
      Real.exp (3 * ε) * ((krCB D K L vlo vhi + 264 * krC₂ D K L / krKappa D vlo vhi ^ 2) *
        (1 + A) ^ 2 * w) :=
  Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (by linarith [H.hw0, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        (krDens_nonneg ν H.hf0 (n + 1) b b')))
    (sum_expw_weighted_krDens_bdry_pin_le ν H hb hb' hε0 hε)

end

end PGM
