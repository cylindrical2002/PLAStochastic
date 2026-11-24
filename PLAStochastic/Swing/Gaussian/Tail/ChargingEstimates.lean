import PLAStochastic.Swing.Gaussian.Tail.ExcessTailShift

/-! # Scalar Gaussian estimates for two-step charging

All probabilities below are evaluated under the actual standard Gaussian law.
The lower bounds integrate the Gaussian density over a finite interval; no
tail asymptotic or comparison law is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem gaussianPDFReal_antitone_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gaussianPDFReal 0 1 y ≤ gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (y-x)]

/-- A lower bound obtained by integrating the minimum density on a positive
interval. -/
theorem gaussianReal_Ioc_density_lower {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b) :
    ENNReal.ofReal ((b-a)*gaussianPDFReal 0 1 b) ≤ gaussianReal 0 1 (Ioc a b) := by
  rw [gaussianReal_apply _ (by norm_num) (Ioc a b)]
  have hm : (∫⁻ _ : ℝ in Ioc a b, gaussianPDF 0 1 b) ≤
      ∫⁻ x : ℝ in Ioc a b, gaussianPDF 0 1 x := by
    apply setLIntegral_mono' measurableSet_Ioc
    intro x hx
    exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_antitone_nonneg (ha.trans hx.1.le) hx.2)
  simpa only [setLIntegral_const, Real.volume_Ioc, gaussianPDF,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), mul_comm] using hm

theorem gaussianReal_Icc_density_lower {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ENNReal.ofReal ((b-a)*gaussianPDFReal 0 1 b) ≤ gaussianReal 0 1 (Icc a b) :=
  (gaussianReal_Ioc_density_lower ha hab).trans (measure_mono Ioc_subset_Icc_self)

/-- A simple genuine Gaussian upper-tail bound. -/
theorem gaussianReal_Ioi_gaussian_bound {r : ℝ} (hr : 0 ≤ r) :
    gaussianReal 0 1 (Ioi r) ≤ ENNReal.ofReal (Real.exp (-r^2/2)) := by
  have h := gaussianReal_Ioi_shift_le (r := 0) (u := r) le_rfl hr
  simp only [zero_add] at h
  exact h.trans ((mul_le_mul_right (prob_le_one (μ := gaussianReal 0 1)) _).trans_eq (mul_one _))

/-- An explicit constant for comparing the upper tail to the interval just
below the threshold. -/
def gaussianChargingConstant : ℝ := 2*Real.sqrt (2*Real.pi)*Real.exp (1/8)

theorem gaussianChargingConstant_pos : 0 < gaussianChargingConstant := by
  unfold gaussianChargingConstant
  positivity

/-- The density calculation behind the tail/interval comparison. -/
theorem gaussianCharging_density_identity (r : ℝ) :
    (gaussianChargingConstant*Real.exp (-r/2)) *
      ((1/2)*gaussianPDFReal 0 1 (r-1/2)) = Real.exp (-r^2/2) := by
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (by positivity)
  simp only [gaussianChargingConstant, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  have he : Real.exp (1/8)*Real.exp (-r/2)*Real.exp (-(r-1/2)^2/2) =
      Real.exp (-r^2/2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (1/8)*Real.exp (-r/2)*Real.exp (-(r-1/2)^2/2) := by field_simp
    _ = _ := he

/-- The actual upper Gaussian tail is exponentially small relative to the
charging interval. This multiplicative form avoids dividing measures. -/
theorem gaussianReal_tail_le_charging_interval {r : ℝ} (hr : 1 < r) :
    gaussianReal 0 1 (Ioi r) ≤
      ENNReal.ofReal (gaussianChargingConstant*Real.exp (-r/2)) *
        gaussianReal 0 1 (Icc (r-1) (r-1/2)) := by
  have hl := gaussianReal_Icc_density_lower (a := r-1) (b := r-1/2) (by linarith) (by linarith)
  have hlen : (r-1/2)-(r-1) = (1/2 : ℝ) := by ring
  rw [hlen] at hl
  calc
    gaussianReal 0 1 (Ioi r) ≤ ENNReal.ofReal (Real.exp (-r^2/2)) :=
      gaussianReal_Ioi_gaussian_bound (by linarith)
    _ = ENNReal.ofReal (gaussianChargingConstant*Real.exp (-r/2)) *
        ENNReal.ofReal ((1/2)*gaussianPDFReal 0 1 (r-1/2)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg gaussianChargingConstant_pos.le (Real.exp_pos _).le),
        gaussianCharging_density_identity]
    _ ≤ _ := mul_le_mul_right hl _

/-- Real-valued ratio form of the charging comparison. -/
theorem gaussianReal_tail_charging_ratio {r : ℝ} (hr : 1 < r) :
    (gaussianReal 0 1 (Ioi r)).toReal /
        (gaussianReal 0 1 (Icc (r-1) (r-1/2))).toReal ≤
      gaussianChargingConstant*Real.exp (-r/2) := by
  have hl := gaussianReal_Icc_density_lower (a := r-1) (b := r-1/2)
    (by linarith) (by linarith)
  have hp : 0 < gaussianReal 0 1 (Icc (r-1) (r-1/2)) := lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr (mul_pos (by linarith)
      (gaussianPDFReal_pos 0 1 _ (by norm_num)))) hl
  have hpr := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  apply (div_le_iff₀ hpr).mpr
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (gaussianReal_tail_le_charging_interval hr)
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg gaussianChargingConstant_pos.le (Real.exp_pos _).le)] using h

/-- Integrating one unit interval gives a global lower bound for every
nonnegative threshold. -/
theorem gaussianReal_tail_density_lower {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (gaussianPDFReal 0 1 (r+1)) ≤ gaussianReal 0 1 (Ioi r) := by
  have h := gaussianReal_Ioc_density_lower hr (show r ≤ r+1 by linarith)
  have he : (r+1)-r = (1 : ℝ) := by ring
  rw [he, one_mul] at h
  exact h.trans (measure_mono fun _ hx => hx.1)

def gaussianChargingCutoffConstant : ℝ := Real.sqrt (2*Real.pi)*Real.exp 3

theorem gaussianChargingCutoffConstant_pos : 0 < gaussianChargingCutoffConstant := by
  unfold gaussianChargingCutoffConstant
  positivity

/-- With `M = sqrt(t)/4`, the crude Gaussian lower bound is already enough to
absorb `exp(-t/4)`, with an explicit exponential rate. -/
theorem gaussianCharging_cutoff_density {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t/4) ≤ gaussianChargingCutoffConstant*Real.exp (-t/8) *
      gaussianPDFReal 0 1 (Real.sqrt t/4+2) := by
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (by positivity)
  have he : -t/4 ≤ 3-t/8-(Real.sqrt t/4+2)^2/2 := by
    have hsq := Real.sq_sqrt ht
    nlinarith [sq_nonneg (Real.sqrt t-4)]
  have hcalc : gaussianChargingCutoffConstant*Real.exp (-t/8) *
      gaussianPDFReal 0 1 (Real.sqrt t/4+2) =
      Real.exp (3-t/8-(Real.sqrt t/4+2)^2/2) := by
    simp only [gaussianChargingCutoffConstant, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    rw [show 3-t/8-(Real.sqrt t/4+2)^2/2 = 3+(-t/8)+(-(Real.sqrt t/4+2)^2/2) by ring,
      Real.exp_add, Real.exp_add]
    field_simp
  rw [hcalc]
  exact Real.exp_le_exp.mpr he

theorem gaussianCharging_cutoff_tail {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-t/4)) ≤
      ENNReal.ofReal (gaussianChargingCutoffConstant*Real.exp (-t/8)) *
        gaussianReal 0 1 (Ioi (Real.sqrt t/4+1)) := by
  have hl := gaussianReal_tail_density_lower (show 0 ≤ Real.sqrt t/4+1 by positivity)
  have he : Real.sqrt t/4+1+1 = Real.sqrt t/4+2 := by ring
  rw [he] at hl
  calc
    ENNReal.ofReal (Real.exp (-t/4)) ≤ ENNReal.ofReal
        (gaussianChargingCutoffConstant*Real.exp (-t/8)*gaussianPDFReal 0 1 (Real.sqrt t/4+2)) :=
      ENNReal.ofReal_le_ofReal (gaussianCharging_cutoff_density ht)
    _ = _ := ENNReal.ofReal_mul (mul_nonneg gaussianChargingCutoffConstant_pos.le (Real.exp_pos _).le)
    _ ≤ _ := mul_le_mul_right hl _

/-- Real-valued ratio form for the cutoff appearing in the charging argument. -/
theorem gaussianCharging_cutoff_ratio {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t/4) / (gaussianReal 0 1 (Ioi (Real.sqrt t/4+1))).toReal ≤
      gaussianChargingCutoffConstant*Real.exp (-t/8) := by
  have hp : 0 < (gaussianReal 0 1 (Ioi (Real.sqrt t/4+1))).toReal :=
    ENNReal.toReal_pos (gaussianReal_Ioi_pos _).ne' (measure_ne_top _ _)
  apply (div_le_iff₀ hp).mpr
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) (gaussianCharging_cutoff_tail ht)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (mul_nonneg gaussianChargingCutoffConstant_pos.le (Real.exp_pos _).le)] using h

end SwingRepair
