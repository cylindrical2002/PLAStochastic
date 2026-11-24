import PLAStochastic.Affine.Process.DriftedSurvival.ExitWeight

/-! # Uniform small-time survival from near the boundary -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem driftedExitWeight_factor (d x : ℝ) :
    driftedExitWeight d x = Real.exp (d*x) * (1 - Real.exp (-4*d*x)) := by
  unfold driftedExitWeight
  rw [mul_sub, mul_one, ← Real.exp_add]
  congr 2
  ring

theorem one_sub_exp_neg_le (a : ℝ) : 1 - Real.exp (-a) ≤ a := by
  linarith [Real.add_one_le_exp (-a)]

theorem one_sub_exp_neg_two_mul_ge {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1/2) :
    2 * Real.exp (-1) * z ≤ 1 - Real.exp (-2*z) := by
  have he : Real.exp (-1) ≤ Real.exp (-2*z) := Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2*z))
    (Real.exp_nonneg (-2*z))
  rw [← Real.exp_add] at hm
  have heq : 2*z + -2*z = 0 := by ring
  rw [heq, Real.exp_zero] at hm
  nlinarith [mul_le_mul_of_nonneg_right he hz]

theorem driftedExitWeight_small_le {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    driftedExitWeight 1 z ≤ 4 * Real.exp 1 * z := by
  rw [driftedExitWeight_factor]
  have hu := one_sub_exp_neg_le (4*z)
  have he : Real.exp z ≤ Real.exp 1 := Real.exp_le_exp.mpr hz'
  simp only [one_mul, mul_one] at *
  calc
    Real.exp z * (1 - Real.exp (-4*z)) ≤ Real.exp z * (4*z) :=
      mul_le_mul_of_nonneg_left (by simpa only [neg_mul] using hu) (Real.exp_nonneg _)
    _ ≤ 4 * Real.exp 1 * z := by nlinarith [mul_le_mul_of_nonneg_right he hz]

theorem driftedExitWeight_far_ge {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.exp (2/t) / 2 ≤ driftedExitWeight (1/t) 2 := by
  rw [driftedExitWeight_factor]
  have h8 : 8 ≤ 8/t := (le_div_iff₀ ht).mpr (by linarith)
  have hexp : Real.exp (-8/t) ≤ 1/2 := by
    have hlow : 2 ≤ Real.exp (8/t) := by linarith [Real.add_one_le_exp (8/t)]
    have heq : Real.exp (-8/t) * Real.exp (8/t) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      congr 1
      ring
    nlinarith [Real.exp_pos (-8/t)]
  have h1 : (1/t)*2 = 2/t := by ring
  have h2 : -4*(1/t)*2 = -8/t := by ring
  rw [h1, h2]
  nlinarith [Real.exp_pos (2/t)]

/-- The upper exit penalty is exponentially smaller than the boundary-distance
factor at drift 1/t. -/
theorem driftedExitWeight_penalty_le {t x : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)
    (hx : 0 ≤ x) (hxt : x ≤ t/2) :
    driftedExitWeight (1/t) x /
      (Real.exp (-(3*(1/t)^2/2)*t) * driftedExitWeight (1/t) 2) ≤
        Real.exp (-1) * (x/t) := by
  have hz : 0 ≤ x/t := div_nonneg hx ht.le
  have hz' : x/t ≤ 1/2 := (div_le_iff₀ ht).mpr (by linarith)
  have hnum : driftedExitWeight (1/t) x ≤ 4 * Real.exp 1 * (x/t) := by
    convert driftedExitWeight_small_le hz (show x/t ≤ 1 by linarith) using 1
    unfold driftedExitWeight
    congr 1 <;> congr 1 <;> ring
  have hfar := driftedExitWeight_far_ge ht (show t ≤ 1 by linarith)
  have hden : Real.exp (1/(2*t)) / 2 ≤
      Real.exp (-(3*(1/t)^2/2)*t) * driftedExitWeight (1/t) 2 := by
    have hm := mul_le_mul_of_nonneg_left hfar (Real.exp_nonneg (-(3*(1/t)^2/2)*t))
    have heq : Real.exp (-(3*(1/t)^2/2)*t) * (Real.exp (2/t)/2) =
        Real.exp (1/(2*t))/2 := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      field_simp
      ring
    rwa [heq] at hm
  have hlarge : 16 ≤ 1/(2*t) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have he : 8 * Real.exp 1 ≤ Real.exp (-1) * Real.exp (1/(2*t)) := by
    have he14 : 8 ≤ Real.exp 14 := by linarith [Real.add_one_le_exp 14]
    have hmono : Real.exp 15 ≤ Real.exp (-1 + 1/(2*t)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hmul := mul_le_mul_of_nonneg_left he14 (Real.exp_nonneg 1)
    rw [← Real.exp_add] at hmul
    norm_num at hmul
    rw [← Real.exp_add]
    simpa only [mul_comm] using hmul.trans hmono
  have hdpos : 0 < Real.exp (-(3*(1/t)^2/2)*t) * driftedExitWeight (1/t) 2 :=
    mul_pos (Real.exp_pos _) (driftedExitWeight_pos (by positivity) (by norm_num))
  apply (div_le_iff₀ hdpos).mpr
  have hm := mul_le_mul_of_nonneg_left hden (mul_nonneg (Real.exp_nonneg (-1)) hz)
  have hm' := mul_le_mul_of_nonneg_right he hz
  nlinarith

/-- A genuine finite-horizon drifted survival bound with no assumed exit law. -/
theorem measureReal_drifted_survival_small_ge (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : 0 < T) (hTsmall : (T : ℝ) ≤ 1/32)
    {x : ℝ} (hx : 0 ≤ x) (hxT : x ≤ (T : ℝ)/2) :
    Real.exp (-1) * (x / (T : ℝ)) ≤
      μ.real {ω | boundedDriftedIntervalExit B x (1/(T : ℝ)) 2 T ω = T} := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hs := measureReal_drifted_survival_ge hB
    (show x ∈ Icc 0 2 from ⟨hx, by linarith⟩)
    (show 0 < 1/(T : ℝ) by positivity) (show (0 : ℝ) < 2 by norm_num) T
  have hl := one_sub_exp_neg_two_mul_ge (div_nonneg hx ht.le)
    ((div_le_iff₀ ht).mpr (show x ≤ 1/2*(T : ℝ) by linarith))
  have hu := driftedExitWeight_penalty_le ht hTsmall hx hxT
  have heq : -2*(1/(T : ℝ))*x = -2*(x/(T : ℝ)) := by ring
  rw [heq] at hs
  linarith

/-- Survival of the genuine cutoff exit is exactly staying in the closed strip,
on continuous Brownian paths started inside it. -/
theorem boundedDriftedIntervalExit_eq_cutoff_implies_strip_ae (hB : IsBrownianReal B μ)
    {x r : ℝ} (hx : x ∈ Icc 0 r) (d : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, boundedDriftedIntervalExit B x d r T ω = T →
      ∀ u : ℝ≥0, u ≤ T → x + B u ω + d * (u : ℝ) ∈ Icc 0 r := by
  filter_upwards [boundedDriftedIntervalExit_endpoint_mem_ae hB hx d T] with ω hω he u hu
  rcases hu.lt_or_eq with hu | rfl
  · have hb := before_boundedOpenExitTime_mem_strip
      (X := fun u ω => x + B u ω + d * (u : ℝ)) (a := r) (b := 0)
      (show u < boundedDriftedIntervalExit B x d r T ω by rwa [he])
    simpa only [neg_zero] using hb
  · rwa [he] at hω

/-- The lower estimate concerns the actual continuum strip event. -/
theorem measureReal_drifted_strip_survival_small_ge (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : 0 < T) (hTsmall : (T : ℝ) ≤ 1/32)
    {x : ℝ} (hx : 0 ≤ x) (hxT : x ≤ (T : ℝ)/2) :
    Real.exp (-1) * (x / (T : ℝ)) ≤
      μ.real {ω | ∀ u : ℝ≥0, u ≤ T → x + B u ω + (1/(T : ℝ)) * (u : ℝ) ∈ Icc 0 2} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  refine (measureReal_drifted_survival_small_ge hB hT hTsmall hx hxT).trans ?_
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  exact boundedDriftedIntervalExit_eq_cutoff_implies_strip_ae hB
    ⟨hx, by linarith⟩ (1/(T : ℝ)) T

end BrownianAffine
