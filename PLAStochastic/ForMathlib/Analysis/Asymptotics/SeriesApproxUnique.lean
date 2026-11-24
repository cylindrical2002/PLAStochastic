import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesApprox
import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseExpansion

/-! # Uniqueness of finite complex coefficient budgets at small positive scale -/

noncomputable section
open Complex Filter Topology Finset PowerSeries
namespace PGM

theorem inversePolynomial_re_coeff_eq_trunc (F : PowerSeries ℂ) (N : ℕ) (eps : ℝ) :
    inversePolynomial (fun j => (coeff j F).re) N eps = (truncEval F N eps⁻¹).re := by
  simp only [inversePolynomial, truncEval, re_sum, ← ofReal_pow, mul_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero]

theorem inversePolynomial_im_coeff_eq_trunc (F : PowerSeries ℂ) (N : ℕ) (eps : ℝ) :
    inversePolynomial (fun j => (coeff j F).im) N eps = (truncEval F N eps⁻¹).im := by
  simp only [inversePolynomial, truncEval, im_sum, ← ofReal_pow, mul_im,
    ofReal_re, ofReal_im, mul_zero, zero_add]

theorem inverseExpansion_re_im_of_seriesApprox {f : ℝ → ℂ} {F : PowerSeries ℂ}
    {N : ℕ} {K R : ℝ} (hR : 0 < R)
    (hF : ∀ b : ℝ, 0 < b → b < R → SeriesApprox (f b) F N b K) :
    HasInverseExpansionAtOrder (fun eps => (f eps⁻¹).re) (fun j => (coeff j F).re) N ∧
      HasInverseExpansionAtOrder (fun eps => (f eps⁻¹).im) (fun j => (coeff j F).im) N := by
  have hsmall : ∀ eps : ℝ, max 1 (2 / R) ≤ eps → 0 < eps⁻¹ ∧ eps⁻¹ < R := by
    intro eps heps
    have heps0 : 0 < eps := zero_lt_one.trans_le ((le_max_left _ _).trans heps)
    have hB : 2 / R ≤ eps := (le_max_right _ _).trans heps
    refine ⟨inv_pos.mpr heps0, ?_⟩
    rw [← one_div, div_lt_iff₀ heps0]
    have := (div_le_iff₀ hR).mp hB
    nlinarith
  constructor
  · refine ⟨K, max 1 (2 / R), fun eps heps => ?_⟩
    obtain ⟨hb, hbR⟩ := hsmall eps heps
    rw [inversePolynomial_re_coeff_eq_trunc, ← sub_re]
    exact (abs_re_le_norm _).trans (hF eps⁻¹ hb hbR).2
  · refine ⟨K, max 1 (2 / R), fun eps heps => ?_⟩
    obtain ⟨hb, hbR⟩ := hsmall eps heps
    rw [inversePolynomial_im_coeff_eq_trunc, ← sub_im]
    exact (abs_im_le_norm _).trans (hF eps⁻¹ hb hbR).2

theorem seriesApprox_coeff_eq_of_small_scale {f : ℝ → ℂ} {F G : PowerSeries ℂ}
    {N M j : ℕ} {K L R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hF : ∀ b : ℝ, 0 < b → b < R → SeriesApprox (f b) F N b K)
    (hG : ∀ b : ℝ, 0 < b → b < S → SeriesApprox (f b) G M b L)
    (hjN : j ≤ N) (hjM : j ≤ M) : coeff j F = coeff j G := by
  obtain ⟨hFr, hFi⟩ := inverseExpansion_re_im_of_seriesApprox hR hF
  obtain ⟨hGr, hGi⟩ := inverseExpansion_re_im_of_seriesApprox hS hG
  exact Complex.ext (inverseExpansion_coeff_eq_of_orders hFr hGr hjN hjM)
    (inverseExpansion_coeff_eq_of_orders hFi hGi hjN hjM)

end PGM
