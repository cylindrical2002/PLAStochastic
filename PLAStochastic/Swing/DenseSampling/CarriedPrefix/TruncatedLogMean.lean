import PLAStochastic.Swing.DenseSampling.CarriedPrefix.FirstOutputDuration
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The logarithmic truncated mean follows from the genuine carried tail -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A bounded nonnegative duration with a c/t tail has logarithmically large
mean. This is the actual tail integral, not a moment hypothesis. -/
theorem integral_ge_log_of_tail [IsProbabilityMeasure μ] {F : Ω → ℝ} {a H c : ℝ}
    (hFi : Integrable F μ) (hF0 : 0 ≤ᵐ[μ] F) (hFH : F ≤ᵐ[μ] fun _ => H)
    (ha : 0 < a) (haH : a ≤ H) (htail : ∀ t ∈ Icc a H, c/t ≤ μ.real {ω | t ≤ F ω}) :
    c*Real.log (H/a) ≤ ∫ ω, F ω ∂μ := by
  let p (t : ℝ) := μ.real {ω | t ≤ F ω}
  have hp0 : ∀ t, 0 ≤ p t := fun _ => ENNReal.toReal_nonneg
  have hpm : Measurable p :=
    (Antitone.measurable (f := fun t : ℝ => μ {ω | t ≤ F ω})
      (fun _ _ hst => measure_mono (fun _ hω => hst.trans hω))).ennreal_toReal
  have hpi : IntegrableOn p (Ioc 0 H) := by
    apply (integrableOn_const (μ := (volume : Measure ℝ)) (C := (1 : ℝ))
      (by simp only [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).mono' hpm.aestronglyMeasurable.restrict
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (hp0 t)]
    exact measureReal_le_one
  have hsub : Ioc a H ⊆ Ioc 0 H := fun _ ht => ⟨ha.trans ht.1, ht.2⟩
  have hgi : IntegrableOn (fun t : ℝ => c/t) (Ioc a H) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le haH).mp
    have hi := (intervalIntegrable_inv_iff.mpr (Or.inr (notMem_uIcc_of_lt ha (ha.trans_le haH)))).const_mul c
    simpa only [div_eq_mul_inv] using hi
  have hmon : (∫ t in Ioc a H, c/t) ≤ ∫ t in Ioc a H, p t :=
    integral_mono_ae hgi (hpi.mono_set hsub) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact htail t ⟨ht.1.le, ht.2⟩)
  have hlog : (∫ t in Ioc a H, c/t) = c*Real.log (H/a) := by
    rw [← intervalIntegral.integral_of_le haH]
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le haH)]
    rw [div_eq_mul_inv]
  rw [hlog] at hmon
  apply hmon.trans
  have hbudget := setIntegral_mono_set hpi (Eventually.of_forall hp0)
    (Eventually.of_forall fun t ht => hsub ht)
  rw [← hFi.integral_eq_integral_Ioc_meas_le hF0 hFH] at hbudget
  exact hbudget

/-- The coefficient is a proved positive fixed Gaussian probability. -/
def nativeCarriedLowerConstant : ℝ := Real.exp (-1)*gaussianFirstPositivePass.toReal/2

theorem nativeCarriedLowerConstant_pos : 0 < nativeCarriedLowerConstant := by
  have hp : 0 < gaussianFirstPositivePass.toReal :=
    ENNReal.toReal_pos gaussianFirstPositivePass_pos.ne' (measure_ne_top _ _)
  exact div_pos (mul_pos (Real.exp_pos _) hp) (by norm_num)

/-- The B.1 logarithmic lower bound for the actual finite carried prefix,
truncated at a deterministic cutoff. -/
theorem integral_nativeCarriedTruncatedDuration_lower {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) {h H : ℝ≥0} (hh : 0 < h) (hHs : (H : ℝ) ≤ 1/32)
    {w M : ℝ} (hM : 0 ≤ M) (hw : -M*(h : ℝ) ≤ w)
    (hMh : 2*M*(h : ℝ) ≤ Real.sqrt (h : ℝ)) (hMH : M*(H : ℝ) ≤ 1)
    (hdH : 8*(max w 0+Real.sqrt (h : ℝ)) ≤ (H : ℝ)) :
    nativeCarriedLowerConstant*(max w 0+Real.sqrt (h : ℝ))*
      Real.log ((H : ℝ)/(8*(max w 0+Real.sqrt (h : ℝ)))) ≤
      ∫ ω, nativeCarriedTruncatedDuration (fun j => B ((j : ℝ≥0)*h) ω) w 1 h H ∂μ := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let F (ω : Ω) := nativeCarriedTruncatedDuration (fun j => B ((j : ℝ≥0)*h) ω) w 1 h H
  have hF0 : 0 ≤ᵐ[μ] F := Eventually.of_forall fun ω =>
    (nativeCarriedTruncatedDuration_bounds _ w 1 h H).1
  have hFH : F ≤ᵐ[μ] fun _ => (H : ℝ) := Eventually.of_forall fun ω =>
    (nativeCarriedTruncatedDuration_bounds _ w 1 h H).2
  have hFi : Integrable F μ := by
    apply Integrable.of_bound (aemeasurable_nativeCarriedTruncatedDuration_brownian hB
      (aemeasurable_const (b := w)) 1 hh H).aestronglyMeasurable (H : ℝ)
    filter_upwards [hF0, hFH] with ω h0 hH
    rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hd : 0 < max w 0+Real.sqrt (h : ℝ) := add_pos_of_nonneg_of_pos (le_max_right _ _)
    (Real.sqrt_pos.mpr (by exact_mod_cast hh))
  apply integral_ge_log_of_tail hFi hF0 hFH (mul_pos (by norm_num) hd) hdH
  intro t ht
  have ht0 : 0 < t := (mul_pos (by norm_num : (0 : ℝ) < 8) hd).trans_le ht.1
  let T : ℝ≥0 := ⟨t, ht0.le⟩
  have htT : (T : ℝ) = t := rfl
  have hTH : T ≤ H := by exact_mod_cast ht.2
  have hb := measureReal_nativeCarriedTruncatedDuration_tail_lower hB hh
    (show 0 < T by exact_mod_cast ht0) (ht.2.trans hHs) hTH hM hw hMh
    ((mul_le_mul_of_nonneg_left ht.2 hM).trans hMH) ht.1
  rw [htT] at hb
  convert hb using 1
  · unfold nativeCarriedLowerConstant
    ring

/-- The same logarithmic estimate is stated directly for the true native
output, not merely for a geometric surrogate. -/
theorem integral_nativeCarriedNativeDuration_lower {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) {h H : ℝ≥0} (hh : 0 < h) (hHs : (H : ℝ) ≤ 1/32)
    {w M : ℝ} (hM : 0 ≤ M) (hw : -M*(h : ℝ) ≤ w)
    (hMh : 2*M*(h : ℝ) ≤ Real.sqrt (h : ℝ)) (hMH : M*(H : ℝ) ≤ 1)
    (hdH : 8*(max w 0+Real.sqrt (h : ℝ)) ≤ (H : ℝ)) :
    nativeCarriedLowerConstant*(max w 0+Real.sqrt (h : ℝ))*
      Real.log ((H : ℝ)/(8*(max w 0+Real.sqrt (h : ℝ)))) ≤
      ∫ ω, nativeCarriedNativeDuration (fun j => B ((j : ℝ≥0)*h) ω) w 1 h H ∂μ := by
  have heq : (fun ω => nativeCarriedTruncatedDuration (fun j => B ((j : ℝ≥0)*h) ω) w 1 h H) =
      (fun ω => nativeCarriedNativeDuration (fun j => B ((j : ℝ≥0)*h) ω) w 1 h H) :=
    funext fun ω => nativeCarriedTruncatedDuration_eq_native _ w (by norm_num) hh H
  have hb := integral_nativeCarriedTruncatedDuration_lower hB hh hHs hM hw hMh hMH hdH
  rwa [heq] at hb

end SwingRepair
