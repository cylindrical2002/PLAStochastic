import PLAStochastic.Index.GEP.StrongApprox.Quantile.GaussianInversion

/-! # WP5: local density sandwiches control both tails and the quantile -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem SADensity.tail_eq_integral {p : ℝ → ℝ} (hp : SADensity p) (x : ℝ) :
    1 - cdf (hp.law : Measure ℝ) x = ∫ y in Ioi x, p y := by
  have h := intervalIntegral.integral_Iic_add_Ioi (b := x) hp.integrable.integrableOn
    hp.integrable.integrableOn
  rw [hp.mass, ← hp.cdf_eq_integral] at h
  linarith

theorem SADensity.tail_split {p : ℝ → ℝ} (hp : SADensity p) (x Y : ℝ) :
    1 - cdf (hp.law : Measure ℝ) x =
      (∫ y in x..Y, p y) + (1 - cdf (hp.law : Measure ℝ) Y) := by
  simp_rw [hp.tail_eq_integral]
  exact (intervalIntegral.integral_interval_add_Ioi hp.integrable.integrableOn
    hp.integrable.integrableOn).symm

/-- Local density bounds and the two upper-tail remainders control a smaller tail. -/
theorem SADensity.tail_sandwich {p q : ℝ → ℝ} (hp : SADensity p) (hq : SADensity q)
    {x Y L U b : ℝ} (hxY : x ≤ Y) (hL1 : L ≤ 1) (hU : 0 ≤ U)
    (hlocal : ∀ y ∈ Icc x Y, L * p y ≤ q y ∧ q y ≤ U * p y)
    (hpY : 1 - cdf (hp.law : Measure ℝ) Y ≤ b)
    (hqY : 1 - cdf (hq.law : Measure ℝ) Y ≤ b) :
    L * (1 - cdf (hp.law : Measure ℝ) x) - b ≤ 1 - cdf (hq.law : Measure ℝ) x ∧
      1 - cdf (hq.law : Measure ℝ) x ≤ U * (1 - cdf (hp.law : Measure ℝ) x) + b := by
  have hlo : L * (∫ y in x..Y, p y) ≤ ∫ y in x..Y, q y := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hxY (hp.integrable.const_mul L).intervalIntegrable
      hq.integrable.intervalIntegrable (fun y hy => (hlocal y hy).1)
  have hhi : (∫ y in x..Y, q y) ≤ U * ∫ y in x..Y, p y := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hxY hq.integrable.intervalIntegrable
      (hp.integrable.const_mul U).intervalIntegrable (fun y hy => (hlocal y hy).2)
  have hp0 : 0 ≤ 1 - cdf (hp.law : Measure ℝ) Y := sub_nonneg.mpr (cdf_le_one _ _)
  have hq0 : 0 ≤ 1 - cdf (hq.law : Measure ℝ) Y := sub_nonneg.mpr (cdf_le_one _ _)
  have hLp : L * (1 - cdf (hp.law : Measure ℝ) Y) ≤ b :=
    (mul_le_of_le_one_left hp0 hL1).trans hpY
  have hUp : 0 ≤ U * (1 - cdf (hp.law : Measure ℝ) Y) := mul_nonneg hU hp0
  rw [hp.tail_split x Y, hq.tail_split x Y]
  constructor <;> nlinarith

/-- Reflection preserves the regular density class. -/
theorem SADensity.reflect {p : ℝ → ℝ} (hp : SADensity p) : SADensity (fun x => p (-x)) := by
  refine ⟨hp.continuous.comp continuous_neg, fun x => hp.pos _, hp.integrable.comp_neg,
    ?_, ?_⟩
  · rw [integral_neg_eq_self, hp.mass]
  · obtain ⟨C, hC⟩ := hp.bounded
    exact ⟨C, fun x => hC (-x)⟩

theorem SADensity.reflect_tail {p : ℝ → ℝ} (hp : SADensity p) (x : ℝ) :
    1 - cdf (hp.reflect.law : Measure ℝ) x = cdf (hp.law : Measure ℝ) (-x) := by
  rw [hp.reflect.tail_eq_integral, hp.cdf_eq_integral]
  have h := MeasureTheory.integral_indicator (μ := volume) (s := Ioi x)
    (f := fun y => p (-y)) measurableSet_Ioi
  rw [← h]
  have he : (Ioi x).indicator (fun y => p (-y)) = fun y => (Iio (-x)).indicator p (-y) := by
    funext y
    by_cases hy : x < y
    · have hn : -y < -x := neg_lt_neg hy
      simp [hy, hn]
    · have hn : ¬ -y < -x := by simpa using hy
      simp [hy, hn]
  rw [he, integral_neg_eq_self, integral_indicator measurableSet_Iio]
  exact setIntegral_congr_set Iio_ae_eq_Iic

/-- A local Gaussian density sandwich with negligible tails gives a quantitative
quantile coupling. The constant `32` is deliberately coarse. -/
theorem saQuantile_error_of_density {q : ℝ → ℝ} (hq : SADensity q) {ε R Y z : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 32) (hR : 0 ≤ R) (hY : R + 1 ≤ Y) (hz : |z| ≤ R)
    (hlocal : ∀ x, |x| ≤ Y →
      Real.exp (-ε) * gaussianPDFReal 0 1 x ≤ q x ∧ q x ≤ Real.exp ε * gaussianPDFReal 0 1 x)
    (hright : 1 - cdf (hq.law : Measure ℝ) Y ≤ ε * saGaussianTail R)
    (hleft : cdf (hq.law : Measure ℝ) (-Y) ≤ ε * saGaussianTail R)
    (hgauss : saGaussianTail Y ≤ ε * saGaussianTail R) :
    |saQuantile (cdf (hq.law : Measure ℝ)) (cdf (gaussianReal 0 1) z) - z| ≤ 32 * ε := by
  have hL : Real.exp (-ε) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hε)
  have hpY : 1 - cdf (saDensity_standardGaussian.law : Measure ℝ) Y ≤ ε * saGaussianTail R := by
    rw [sa_standardGaussian_law]
    exact hgauss
  apply saQuantile_gaussian_error hq.regularCDF hε hε1 hz
  · intro x hx
    have hb := saDensity_standardGaussian.tail_sandwich hq (show x ≤ Y by linarith [hx.2])
      hL (Real.exp_nonneg ε) (fun y hy => hlocal y (abs_le.mpr ⟨by linarith [hx.1, hy.1], hy.2⟩))
      hpY hright
    rw [sa_standardGaussian_law] at hb
    exact hb
  · intro x hx
    have hrY : 1 - cdf (hq.reflect.law : Measure ℝ) Y ≤ ε * saGaussianTail R := by
      rw [hq.reflect_tail]
      exact hleft
    have hl : ∀ y ∈ Icc x Y, Real.exp (-ε) * gaussianPDFReal 0 1 y ≤ q (-y) ∧
        q (-y) ≤ Real.exp ε * gaussianPDFReal 0 1 y := by
      intro y hy
      have ha : |-y| ≤ Y := by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hx.1, hy.1], hy.2⟩
      have hq' := hlocal (-y) ha
      have hg : gaussianPDFReal 0 1 (-y) = gaussianPDFReal 0 1 y := by
        simp only [gaussianPDFReal, sub_zero, neg_sq]
      rwa [hg] at hq'
    have hb := saDensity_standardGaussian.tail_sandwich hq.reflect (show x ≤ Y by linarith [hx.2])
      hL (Real.exp_nonneg ε) hl hpY hrY
    rw [sa_standardGaussian_law, hq.reflect_tail] at hb
    exact hb

end

end PGM
