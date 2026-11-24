import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesApproxUnique

/-! # Reality of finite expansion coefficients from a genuine real approximation -/

noncomputable section
open Complex Filter Topology PowerSeries
namespace PGM

theorem seriesApprox_coeff_im_eq_zero {f : ℝ → ℝ} {F : PowerSeries ℂ}
    {N j : ℕ} {K R : ℝ} (hR : 0 < R)
    (hF : ∀ b : ℝ, 0 < b → b < R → SeriesApprox (f b : ℂ) F N b K)
    (hj : j ≤ N) : (coeff j F).im = 0 := by
  have hI := (inverseExpansion_re_im_of_seriesApprox hR hF).2
  have hI' : HasInverseExpansionAtOrder (fun _ : ℝ => (0 : ℝ))
      (fun i => (coeff i F).im) N := by simpa only [ofReal_im] using hI
  have hZ : HasInverseExpansionAtOrder (fun _ : ℝ => (0 : ℝ)) (fun _ => 0) N := by
    refine ⟨0, 1, fun _ _ => ?_⟩
    simp [inversePolynomial]
  exact inverseExpansion_coeff_eq_of_orders hI' hZ hj hj

theorem seriesApprox_coeff_im_eq_zero_of_close {f : ℝ → ℂ} {g : ℝ → ℝ}
    {F : PowerSeries ℂ} {N j : ℕ} {K L R : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hF : ∀ b : ℝ, 0 < b → b < R → SeriesApprox (f b) F N b K)
    (hclose : ∀ b : ℝ, 0 < b → b < R → ‖f b - (g b : ℂ)‖ ≤ L * b ^ (N + 1))
    (hj : j ≤ N) : (coeff j F).im = 0 := by
  apply seriesApprox_coeff_im_eq_zero hR (f := g) (K := K + L) _ hj
  intro b hb hbR
  exact (hF b hb hbR).of_close hL (by simpa only [norm_sub_rev] using hclose b hb hbR)

theorem inversePolynomial_im_half_scale (F : PowerSeries ℂ) (N : ℕ) (eps : ℝ) :
    inversePolynomial (fun j => (2⁻¹ : ℝ) ^ j * (coeff j F).im) N eps =
      (truncEval F N ((2 * eps)⁻¹)).im := by
  simp only [inversePolynomial, truncEval, im_sum, ← ofReal_pow, mul_im,
    ofReal_re, ofReal_im, mul_zero, zero_add, mul_inv, mul_pow]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Reality follows from a finite half-scale expansion and an equally accurate
approximation of the same function by a genuine real mean. -/
theorem halfScale_coeff_im_eq_zero_of_real_mean {f : ℝ → ℂ} {g : ℝ → ℝ}
    {F : PowerSeries ℂ} {N j : ℕ} {K L E S : ℝ}
    (hF : ∀ eps : ℝ, E ≤ eps →
      ‖f eps + truncEval F N ((2 * eps)⁻¹)‖ ≤ K * (eps⁻¹) ^ (N + 1))
    (hmean : ∀ eps : ℝ, S ≤ eps →
      ‖(g eps : ℂ) + 4 * f eps‖ ≤ L * (eps⁻¹) ^ (N + 1))
    (hj : j ≤ N) : (coeff j F).im = 0 := by
  have hI : HasInverseExpansionAtOrder (fun eps => -(f eps).im)
      (fun i => (2⁻¹ : ℝ) ^ i * (coeff i F).im) N := by
    refine ⟨K, E, fun eps heps => ?_⟩
    rw [inversePolynomial_im_half_scale,
      show -(f eps).im - (truncEval F N ((2 * eps)⁻¹)).im =
        -(f eps + truncEval F N ((2 * eps)⁻¹)).im by simp only [add_im]; ring,
      abs_neg]
    exact (abs_im_le_norm _).trans (hF eps heps)
  have hZ : HasInverseExpansionAtOrder (fun eps => -(f eps).im) (fun _ => 0) N := by
    refine ⟨|L| / 4, max S 1, fun eps heps => ?_⟩
    have heps1 : 1 ≤ eps := (le_max_right _ _).trans heps
    have heps0 : 0 < eps := zero_lt_one.trans_le heps1
    have ht := (abs_im_le_norm ((g eps : ℂ) + 4 * f eps)).trans
      (hmean eps ((le_max_left _ _).trans heps))
    have ht' : 4 * |(f eps).im| ≤ L * (eps⁻¹) ^ (N + 1) := by
      norm_num [add_im, mul_im, abs_mul] at ht
      simpa only [inv_pow] using ht
    have hL := mul_le_mul_of_nonneg_right (le_abs_self L)
      (pow_nonneg (inv_pos.mpr heps0).le (N + 1))
    simp only [inversePolynomial, zero_mul, Finset.sum_const_zero, sub_zero, abs_neg]
    nlinarith
  have he := inverseExpansion_coeff_eq_of_orders hI hZ hj hj
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by norm_num))

end PGM
