import PLAStochastic.Index.KEP.ReferenceScale.CertificateCoarea

/-!
# Compact logarithmic slope integrals

The exact change of variables and its norm estimate connect the true graph
coefficients to the already proved physical-slope kernel budgets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_setIntegral_logSlope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi) (G : ℝ → E) :
    (∫ s in Ioc (Real.log lo) (Real.log hi), G s) =
      ∫ a in Ioc lo hi, a⁻¹ • G (Real.log a) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioc lo hi)
    measurableSet_Ioc (fun a ha =>
      (Real.hasDerivAt_log (hlo.trans ha.1).ne').hasDerivWithinAt)
    (Real.strictMonoOn_log.injOn.mono (fun a ha => hlo.trans ha.1)) G
  rw [Real.image_log_Ioc hlo hlh] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
  rw [abs_inv, abs_of_pos (hlo.trans ha.1)]

theorem kep_setIntegral_abs_logSlope_le {G : ℝ → ℝ} (hG : Continuous G)
    {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi) :
    (∫ s in Ioc (Real.log lo) (Real.log hi), |G s|) ≤
      lo⁻¹ * ∫ a in Icc lo hi, |G (Real.log a)| := by
  rw [kep_setIntegral_logSlope hlo hlh]
  have hl : ContinuousOn Real.log (Icc lo hi) :=
    Real.continuousOn_log.mono fun a ha => (hlo.trans_le ha.1).ne'
  have hiG : IntegrableOn (fun a => |G (Real.log a)|) (Icc lo hi) :=
    (hG.abs.comp_continuousOn hl).integrableOn_compact isCompact_Icc
  have hinv : ContinuousOn (fun a : ℝ => a⁻¹) (Icc lo hi) :=
    continuousOn_id.inv₀ fun a ha => (hlo.trans_le ha.1).ne'
  have hiW : IntegrableOn (fun a => a⁻¹ * |G (Real.log a)|) (Icc lo hi) :=
    (hinv.mul (hG.abs.comp_continuousOn hl)).integrableOn_compact isCompact_Icc
  rw [← integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ ∫ a in Icc lo hi, lo⁻¹ * |G (Real.log a)| := by
      apply setIntegral_mono_on hiW (hiG.const_mul _) measurableSet_Icc
      intro a ha
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hlo ha.1) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

end

end PGM
