import PLAStochastic.Index.GEP.StrongApprox.Quantile.ConditionalSplit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-! # WP5: Gaussian CDF derivatives and tail shifts for quantile comparison -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Filter Topology
open scoped Real ENNReal NNReal

theorem SADensity.cdf_eq_integral {p : ℝ → ℝ} (hp : SADensity p) (x : ℝ) :
    cdf (hp.law : Measure ℝ) x = ∫ y in Iic x, p y := by
  rw [cdf_eq_real, measureReal_def]
  change (volume.withDensity (fun y => ENNReal.ofReal (p y)) (Iic x)).toReal = _
  rw [withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hp.integrable.integrableOn
      (ae_of_all _ fun y => (hp.pos y).le), ENNReal.toReal_ofReal]
  exact integral_nonneg fun y => (hp.pos y).le

theorem SADensity.hasDerivAt_cdf {p : ℝ → ℝ} (hp : SADensity p) (x : ℝ) :
    HasDerivAt (cdf (hp.law : Measure ℝ)) (p x) x := by
  have he : (cdf (hp.law : Measure ℝ) : ℝ → ℝ) =
      fun y => cdf (hp.law : Measure ℝ) 0 + ∫ z in (0 : ℝ)..y, p z := by
    funext y
    rw [hp.cdf_eq_integral, hp.cdf_eq_integral,
      ← intervalIntegral.integral_Iic_sub_Iic hp.integrable.integrableOn hp.integrable.integrableOn]
    ring
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right hp.integrable.intervalIntegrable
    hp.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    hp.continuous.continuousAt).const_add _

theorem saDensity_standardGaussian : SADensity (gaussianPDFReal 0 1) := by
  refine ⟨?_, fun x => gaussianPDFReal_pos 0 1 x one_ne_zero,
    integrable_gaussianPDFReal _ _, integral_gaussianPDFReal_eq_one _ one_ne_zero,
    ⟨_, fun x => gaussianPDFReal_le_inv_sqrt 0 x 1⟩⟩
  unfold gaussianPDFReal
  fun_prop

theorem sa_standardGaussian_law :
    (saDensity_standardGaussian.law : Measure ℝ) = gaussianReal 0 1 := by
  exact (gaussianReal_of_var_ne_zero 0 one_ne_zero).symm

theorem hasDerivAt_standardGaussian_cdf (x : ℝ) :
    HasDerivAt (cdf (gaussianReal 0 1)) (gaussianPDFReal 0 1 x) x := by
  rw [← sa_standardGaussian_law]
  exact saDensity_standardGaussian.hasDerivAt_cdf x

def saGaussianTail (x : ℝ) : ℝ := 1 - cdf (gaussianReal 0 1) x

theorem saGaussianTail_pos (x : ℝ) : 0 < saGaussianTail x := by
  have h := (saCDF_gaussianReal 0 (v := 1) one_ne_zero).mem_Ioo x
  exact sub_pos.mpr h.2

theorem saGaussianTail_le_one (x : ℝ) : saGaussianTail x ≤ 1 := by
  have h := cdf_nonneg (gaussianReal 0 1) x
  dsimp [saGaussianTail]
  linarith

theorem hasDerivAt_saGaussianTail (x : ℝ) :
    HasDerivAt saGaussianTail (-gaussianPDFReal 0 1 x) x := by
  exact (hasDerivAt_standardGaussian_cdf x).const_sub 1

theorem saGaussianTail_eq_real (x : ℝ) :
    saGaussianTail x = (gaussianReal 0 1).real (Ioi x) := by
  rw [saGaussianTail, cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

theorem saGaussianCDF_neg (x : ℝ) : cdf (gaussianReal 0 1) (-x) = saGaussianTail x := by
  let := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hn : (gaussianReal 0 1).map (fun y : ℝ => -y) = gaussianReal 0 1 := by
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
  have hm := congrArg (fun μ : Measure ℝ => μ (Iic (-x))) hn
  rw [Measure.map_apply measurable_neg measurableSet_Iic] at hm
  have he : (fun y : ℝ => -y) ⁻¹' Iic (-x) = Ici x := by
    ext y
    simp only [mem_preimage, mem_Iic, neg_le_neg_iff, mem_Ici]
  rw [he] at hm
  rw [cdf_eq_real, saGaussianTail_eq_real, measureReal_def, measureReal_def, ← hm]
  exact congrArg ENNReal.toReal (measure_congr (Ioi_ae_eq_Ici (μ := gaussianReal 0 1)).symm)

/-- A Chernoff bound, with constants sufficient for the quantile argument. -/
theorem saGaussianTail_le_exp {x : ℝ} (hx : 0 ≤ x) :
    saGaussianTail x ≤ Real.exp (-(x ^ 2 / 2)) := by
  have hb := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) x hx
    (integrable_exp_mul_gaussianReal x)
  rw [mgf_id_gaussianReal] at hb
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add] at hb
  rw [← Real.exp_add] at hb
  have he : -x * x + x ^ 2 / 2 = -(x ^ 2 / 2) := by ring
  rw [he] at hb
  rw [saGaussianTail_eq_real]
  exact (measureReal_mono Ioi_subset_Ici_self).trans hb

/-- A coarse uniform Mills ratio on the interval needed by the quantile lemma. -/
theorem saGaussianTail_le_eight_pdf {x : ℝ} (hx : -1 ≤ x) :
    saGaussianTail x ≤ 8 * gaussianPDFReal 0 1 x := by
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hsl : Real.sqrt (2 * π) ≤ 4 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · have := Real.pi_lt_four
      nlinarith
  have hinv : (1 : ℝ) / 4 ≤ (Real.sqrt (2 * π))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hs hsl
  have hpdf : gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
    simp [gaussianPDFReal, neg_div]
  rw [hpdf]
  by_cases hx0 : 0 ≤ x
  · have ht := saGaussianTail_le_exp hx0
    have he := Real.exp_pos (-(x ^ 2 / 2))
    nlinarith [mul_le_mul_of_nonneg_right hinv he.le]
  · have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hexp : (1 : ℝ) / 2 ≤ Real.exp (-(x ^ 2 / 2)) := by
      have he := Real.add_one_le_exp (-(x ^ 2 / 2))
      linarith
    have hp := mul_le_mul hinv hexp (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (inv_nonneg.mpr hs.le)
    have ht := saGaussianTail_le_one x
    nlinarith

/-- The Gaussian tail has a fixed positive hazard on `[-1,∞)`. -/
theorem antitoneOn_exp_mul_saGaussianTail :
    AntitoneOn (fun x => Real.exp (x / 8) * saGaussianTail x) (Ici (-1)) := by
  have hd (x : ℝ) : HasDerivAt (fun x => Real.exp (x / 8) * saGaussianTail x)
      (Real.exp (x / 8) * (saGaussianTail x / 8 - gaussianPDFReal 0 1 x)) x := by
    have h := (((hasDerivAt_id x).div_const 8).exp.mul (hasDerivAt_saGaussianTail x))
    have he : Real.exp (x / 8) * (saGaussianTail x / 8 - gaussianPDFReal 0 1 x) =
        Real.exp (id x / 8) * (1 / 8) * saGaussianTail x +
          Real.exp (id x / 8) * -gaussianPDFReal 0 1 x := by simp only [id_eq]; ring
    rw [he]
    exact h
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (-1))
    ((fun x => (hd x).continuousAt) |> continuous_iff_continuousAt.mpr |>.continuousOn)
    (fun x _ => (hd x).hasDerivWithinAt)
  intro x hx
  apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
  have hb := saGaussianTail_le_eight_pdf (interior_subset hx)
  linarith

theorem saGaussianTail_shift_le {x η : ℝ} (hx : -1 ≤ x) (hη : 0 ≤ η) :
    saGaussianTail (x + η) ≤ Real.exp (-(η / 8)) * saGaussianTail x := by
  have h := antitoneOn_exp_mul_saGaussianTail (a := x) (b := x + η) hx
    (show -1 ≤ x + η by linarith) (by linarith)
  dsimp only at h
  have he : Real.exp ((x + η) / 8) = Real.exp (x / 8) * Real.exp (η / 8) := by
    rw [add_div, Real.exp_add]
  rw [he, mul_assoc, mul_le_mul_iff_right₀ (Real.exp_pos (x / 8))] at h
  calc
    _ ≤ saGaussianTail x / Real.exp (η / 8) := (le_div_iff₀ (Real.exp_pos _)).mpr (by
      simpa only [mul_comm] using h)
    _ = _ := by rw [Real.exp_neg, div_eq_mul_inv, mul_comm]

end

end PGM
