import PLAStochastic.ForMathlib.Probability.Hellinger.ScaleMeasure
import Mathlib.Probability.Distributions.Exponential

/-! # Unconditional scale regularity of the actual exponential base law -/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

def positiveExpDensity : HellingerDensity (volume : Measure ℝ) where
  density := (Ioi (0 : ℝ)).indicator (fun x => Real.exp (-x))
  measurable := (Real.measurable_exp.comp measurable_neg).indicator measurableSet_Ioi
  nonneg x := indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  integrable := (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).congr_fun
    (fun x _ => by simp) measurableSet_Ioi |>.integrable_indicator measurableSet_Ioi
  integral_eq_one := by
    rw [integral_indicator measurableSet_Ioi]
    exact integral_exp_neg_Ioi_zero

theorem positiveExpDensity_nonpos {x : ℝ} (hx : x ≤ 0) : positiveExpDensity.density x = 0 := by
  change (Ioi (0 : ℝ)).indicator (fun x => Real.exp (-x)) x = 0
  exact indicator_of_notMem (s := Ioi (0 : ℝ)) (not_lt_of_ge hx) _

theorem positiveExpDensity_toMeasure : positiveExpDensity.toMeasure = expMeasure 1 := by
  unfold HellingerDensity.toMeasure expMeasure gammaMeasure
  apply withDensity_congr_ae
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  filter_upwards [hne] with x hx
  change ENNReal.ofReal ((Ioi (0 : ℝ)).indicator (fun x => Real.exp (-x)) x) = gammaPDF 1 1 x
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) (not_lt_of_ge hx.le),
      ENNReal.ofReal_zero, gammaPDF_of_neg hx]
  · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hx, gammaPDF_of_nonneg hx.le]
    simp

def logExpDensity : HellingerDensity (volume : Measure ℝ) :=
  positiveExpDensity.logCoordinates (fun _ hx => positiveExpDensity_nonpos hx)

theorem logExpDensity_density (y : ℝ) :
    logExpDensity.density y = Real.exp y * Real.exp (-Real.exp y) := by
  change Real.exp y * (Ioi (0 : ℝ)).indicator (fun x => Real.exp (-x)) (Real.exp y) = _
  rw [indicator_of_mem (s := Ioi (0 : ℝ)) (Real.exp_pos y)]

def logExpFirst (y : ℝ) : ℝ := Real.exp y * Real.exp (-Real.exp y) * (1 - Real.exp y)

def logExpSecond (y : ℝ) : ℝ :=
  Real.exp y * Real.exp (-Real.exp y) * (1 - 3 * Real.exp y + Real.exp y ^ 2)

set_option backward.isDefEq.respectTransparency.types false in
theorem logExpDensity_hasDerivAt (y : ℝ) :
    HasDerivAt logExpDensity.density (logExpFirst y) y := by
  have h := (Real.hasDerivAt_exp y).mul (Real.hasDerivAt_exp y).neg.exp
  have he : logExpDensity.density = fun y => Real.exp y * Real.exp (-Real.exp y) :=
    funext logExpDensity_density
  rw [he]
  convert h using 1 <;> first | rfl | (dsimp only [logExpFirst, Pi.neg_apply]; ring)

set_option backward.isDefEq.respectTransparency.types false in
theorem logExpFirst_hasDerivAt (y : ℝ) : HasDerivAt logExpFirst (logExpSecond y) y := by
  have h := ((Real.hasDerivAt_exp y).mul (Real.hasDerivAt_exp y).neg.exp).mul
    ((Real.hasDerivAt_exp y).const_sub 1)
  convert h using 1 <;> first | rfl |
    (dsimp only [logExpSecond, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]; ring)

theorem integral_Ioi_nat_pow_exp_neg (n : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ n * Real.exp (-x)) = (n.factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := 1)
    (by positivity) one_pos
  simpa only [add_sub_cancel_right, Real.rpow_natCast, one_mul, one_div_one, Real.one_rpow,
    Real.Gamma_nat_eq_factorial] using h

theorem nat_pow_exp_neg_integrableOn (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Ioi 0) volume := by
  by_contra h
  have hz := integral_undef h
  rw [integral_Ioi_nat_pow_exp_neg] at hz
  exact (by exact_mod_cast Nat.factorial_pos n : (0 : ℝ) < n.factorial).ne' hz

theorem logExpFirst_integrable : Integrable logExpFirst volume := by
  have hi : IntegrableOn (fun x : ℝ => (1 + x) * Real.exp (-x)) (Ioi 0) volume := by
    convert (nat_pow_exp_neg_integrableOn 0).add (nat_pow_exp_neg_integrableOn 1) using 1 <;>
      first | rfl | (funext x; simp only [Pi.add_apply, pow_zero, pow_one, one_mul, add_mul])
  have hh := (HellingerDensity.integrable_exp_mul_comp_exp_iff _).2 hi
  refine hh.mono' (by unfold logExpFirst; fun_prop) (ae_of_all _ fun y => ?_)
  change ‖logExpFirst y‖ ≤ Real.exp y * ((1 + Real.exp y) * Real.exp (-Real.exp y))
  have hb : |1 - Real.exp y| ≤ 1 + Real.exp y := abs_le.mpr
    ⟨by linarith [Real.exp_pos y], by linarith [Real.exp_pos y]⟩
  rw [logExpFirst, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity :
    0 < Real.exp y * Real.exp (-Real.exp y))]
  nlinarith [mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ Real.exp y * Real.exp (-Real.exp y))]

theorem logExpSecond_integrable : Integrable logExpSecond volume := by
  have hi : IntegrableOn (fun x : ℝ => (1 + 3 * x + x ^ 2) * Real.exp (-x)) (Ioi 0) volume := by
    convert ((nat_pow_exp_neg_integrableOn 0).add
      ((nat_pow_exp_neg_integrableOn 1).const_mul 3)).add (nat_pow_exp_neg_integrableOn 2) using 1 <;>
      first | rfl | (funext x; simp only [Pi.add_apply, pow_zero, pow_one, one_mul, add_mul]; ring)
  have hh := (HellingerDensity.integrable_exp_mul_comp_exp_iff _).2 hi
  refine hh.mono' (by unfold logExpSecond; fun_prop) (ae_of_all _ fun y => ?_)
  change ‖logExpSecond y‖ ≤ Real.exp y * ((1 + 3 * Real.exp y + Real.exp y ^ 2) * Real.exp (-Real.exp y))
  have hb : |1 - 3 * Real.exp y + Real.exp y ^ 2| ≤ 1 + 3 * Real.exp y + Real.exp y ^ 2 :=
    abs_le.mpr ⟨by nlinarith [Real.exp_pos y, sq_nonneg (Real.exp y)],
      by nlinarith [Real.exp_pos y]⟩
  rw [logExpSecond, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity :
    0 < Real.exp y * Real.exp (-Real.exp y))]
  nlinarith [mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ Real.exp y * Real.exp (-Real.exp y))]

theorem hellinger_positiveExpDensity_scale_two_thirds (s : ℝ) :
    (positiveExpDensity.dilate (Real.exp s) (Real.exp_pos s)).hellinger positiveExpDensity ≤
      (2 * Real.sqrt (2 * ∫ y, |logExpSecond y|) + Real.sqrt (∫ y, |logExpFirst y|) / 2) *
        |s| ^ (2 / 3 : ℝ) := by
  rw [HellingerDensity.hellinger_dilate_exp_eq_translate positiveExpDensity
    (fun _ hx => positiveExpDensity_nonpos hx)]
  exact logExpDensity.hellinger_translate_le_two_thirds logExpDensity_hasDerivAt
    logExpFirst_hasDerivAt (by unfold logExpFirst; fun_prop) (by unfold logExpSecond; fun_prop)
    logExpFirst_integrable logExpSecond_integrable s

theorem measureHellinger_exp_one_scale_two_thirds (s : ℝ) :
    let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
    let : IsProbabilityMeasure ((expMeasure 1).map (fun x => Real.exp s * x)) :=
      Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
    measureHellinger ((expMeasure 1).map (fun x => Real.exp s * x)) (expMeasure 1) ≤
      (2 * Real.sqrt (2 * ∫ y, |logExpSecond y|) + Real.sqrt (∫ y, |logExpFirst y|) / 2) *
        |s| ^ (2 / 3 : ℝ) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  let : IsProbabilityMeasure ((expMeasure 1).map (fun x => Real.exp s * x)) :=
    Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
  have h := (HellingerDensity.measureHellinger_map_mul_le_density positiveExpDensity
    (Real.exp_pos s)).trans (hellinger_positiveExpDensity_scale_two_thirds s)
  simpa only [positiveExpDensity_toMeasure] using h

end

end ProbabilityTheory
