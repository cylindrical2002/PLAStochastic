import PLAStochastic.Swing.Restart.MaximalPrefix.ObservedHistory
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Probability.ConditionalProbability

/-! # Genuine Gaussian tail-shift estimates for exit overshoots -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Exact density ratio underlying the Gaussian overshoot estimate. -/
theorem gaussianPDFReal_shift_ratio (x u : ℝ) :
    gaussianPDFReal 0 1 (x + u) = gaussianPDFReal 0 1 x * Real.exp (-x*u-u^2/2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [show -(x+u)^2/2 = -x^2/2 + (-x*u-u^2/2) by ring, Real.exp_add]
  ring

/-- Nonnegative exit thresholds give a Gaussian bound uniform in the threshold. -/
theorem gaussianPDFReal_shift_le {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    gaussianPDFReal 0 1 (x + u) ≤ Real.exp (-u^2/2) * gaussianPDFReal 0 1 x := by
  rw [gaussianPDFReal_shift_ratio, mul_comm (Real.exp _) _]
  apply mul_le_mul_of_nonneg_left _ (gaussianPDFReal_nonneg _ _ _)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hx hu]

/-- Actual translated Gaussian tail probability, with no tail-law assumption. -/
theorem gaussianReal_Ioi_shift_le {r u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) :
    gaussianReal 0 1 (Ioi (r + u)) ≤
      ENNReal.ofReal (Real.exp (-u^2/2)) * gaussianReal 0 1 (Ioi r) := by
  have hshift : (∫⁻ x in Ioi r, gaussianPDF 0 1 (x+u)) =
      ∫⁻ x in Ioi (r+u), gaussianPDF 0 1 x := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
    convert lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      ((Ioi (r+u)).indicator (gaussianPDF 0 1)) u using 1
    congr 1
    funext x
    simp only [indicator_apply, mem_Ioi]
    by_cases hx : r < x
    · simp [hx, show r+u < x+u by linarith]
    · simp [hx, show ¬r+u < x+u by linarith]
  rw [gaussianReal_apply _ (by norm_num) (Ioi (r+u)), ← hshift,
    gaussianReal_apply _ (by norm_num) (Ioi r), ← lintegral_const_mul' _ _ (by simp)]
  apply setLIntegral_mono' measurableSet_Ioi
  intro x hx
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_shift_le (hr.trans hx.le) hu)

/-- Conditioning is on a strictly positive original Gaussian event for every finite threshold. -/
theorem gaussianReal_Ioi_pos (r : ℝ) : 0 < gaussianReal 0 1 (Ioi r) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := gaussianReal_absolutelyContinuous' 0 (show (1 : ℝ≥0) ≠ 0 by norm_num) hz
  exact ENNReal.top_ne_zero (by simpa only [Real.volume_Ioi] using hv)

/-- The actual conditional excess law, obtained by restricting and translating the standard Gaussian. -/
def gaussianExcessLaw (r : ℝ) : Measure ℝ :=
  ((gaussianReal 0 1)[|Ioi r]).map (fun x => x-r)

instance gaussianExcessLaw_isProbabilityMeasure (r : ℝ) : IsProbabilityMeasure (gaussianExcessLaw r) := by
  have : IsProbabilityMeasure ((gaussianReal 0 1)[|Ioi r]) :=
    cond_isProbabilityMeasure (gaussianReal_Ioi_pos r).ne'
  exact Measure.isProbabilityMeasure_map (measurable_id.sub_const r).aemeasurable

/-- Exact conditional tail identity, including the normalization by the exit probability. -/
theorem gaussianExcessLaw_tail (r : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    gaussianExcessLaw r (Ioi u) =
      (gaussianReal 0 1 (Ioi r))⁻¹ * gaussianReal 0 1 (Ioi (r+u)) := by
  rw [gaussianExcessLaw, Measure.map_apply (show Measurable (fun x : ℝ => x-r) by fun_prop) measurableSet_Ioi,
    cond_apply measurableSet_Ioi]
  congr 2
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_preimage]
  constructor
  · intro hx
    linarith [hx.2]
  · intro hx
    constructor <;> linarith

/-- The conditional excess is strictly positive almost surely. -/
theorem gaussianExcessLaw_positive_ae (r : ℝ) : ∀ᵐ x ∂gaussianExcessLaw r, 0 < x := by
  have hmass : gaussianExcessLaw r (Ioi 0) = 1 := by
    rw [gaussianExcessLaw_tail r (le_rfl : (0 : ℝ) ≤ 0), add_zero,
      ENNReal.inv_mul_cancel (gaussianReal_Ioi_pos r).ne' (measure_ne_top _ _)]
  rw [ae_iff]
  change gaussianExcessLaw r (Ioi 0)ᶜ = 0
  rw [measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ, hmass, tsub_self]

/-- Uniform Gaussian tail of the actual excess at every nonnegative threshold. -/
theorem gaussianExcessLaw_tail_le {r u : ℝ} (hr : 0 ≤ r) (hu : 0 ≤ u) :
    gaussianExcessLaw r (Ioi u) ≤ ENNReal.ofReal (Real.exp (-u^2/2)) := by
  rw [gaussianExcessLaw_tail r hu]
  calc
    _ ≤ (gaussianReal 0 1 (Ioi r))⁻¹ *
        (ENNReal.ofReal (Real.exp (-u^2/2)) * gaussianReal 0 1 (Ioi r)) :=
      mul_le_mul_right (gaussianReal_Ioi_shift_le hr hu) _
    _ = ENNReal.ofReal (Real.exp (-u^2/2)) := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel (gaussianReal_Ioi_pos r).ne' (measure_ne_top _ _), mul_one]

end SwingRepair
