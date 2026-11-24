import PLAStochastic.Index.KEP.ReferenceScale.BridgeFirstAverage

/-!
# Compact logarithmic-slope absolute integrals

The integral inequalities retain actual integrability of the continuous finite
bridge terms. The product bound uses a uniform bound for only one factor.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepLogSlopeNorm (F : ℝ → ℝ) : ℝ :=
  ∫ s in Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |F s|

theorem kepLogSlopeNorm_nonneg (F : ℝ → ℝ) : 0 ≤ kepLogSlopeNorm F :=
  integral_nonneg fun _ => abs_nonneg _

theorem kepLogSlopeNorm_neg (F : ℝ → ℝ) :
    kepLogSlopeNorm (fun s => -F s) = kepLogSlopeNorm F := by
  simp only [kepLogSlopeNorm, abs_neg]

theorem kepLogSlopeNorm_const_mul (a : ℝ) (F : ℝ → ℝ) :
    kepLogSlopeNorm (fun s => a * F s) = |a| * kepLogSlopeNorm F := by
  simp only [kepLogSlopeNorm, abs_mul, integral_const_mul]

theorem kepLogSlopeNorm_add_le {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    kepLogSlopeNorm (fun s => F s + G s) ≤ kepLogSlopeNorm F + kepLogSlopeNorm G := by
  let μ := volume.restrict (Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2))
  have hi {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  unfold kepLogSlopeNorm
  rw [← integral_add (hi hF.abs) (hi hG.abs)]
  exact integral_mono_ae (hi (hF.add hG).abs) (hi (hF.abs.add hG.abs))
    (ae_of_all _ fun s => abs_add_le _ _)

theorem kepLogSlopeNorm_sub_le {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) :
    kepLogSlopeNorm (fun s => F s - G s) ≤ kepLogSlopeNorm F + kepLogSlopeNorm G := by
  simpa only [sub_eq_add_neg, Pi.neg_apply, kepLogSlopeNorm, abs_neg] using
    kepLogSlopeNorm_add_le hF hG.neg

theorem kepLogSlopeNorm_sum_le {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ S, Continuous (F i)) :
    kepLogSlopeNorm (fun s => ∑ i ∈ S, F i s) ≤ ∑ i ∈ S, kepLogSlopeNorm (F i) := by
  let μ := volume.restrict (Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2))
  have hi {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  unfold kepLogSlopeNorm
  rw [← integral_finsetSum S (fun i hiS => hi (hF i hiS).abs)]
  exact integral_mono_ae (hi (continuous_finsetSum S hF).abs)
    (hi (continuous_finsetSum S fun i hiS => (hF i hiS).abs))
    (ae_of_all _ fun s => Finset.abs_sum_le_sum_abs _ _)

theorem kepLogSlopeNorm_mul_bound {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    {A : ℝ} (hA : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |F s| ≤ A) :
    kepLogSlopeNorm (fun s => F s * G s) ≤ A * kepLogSlopeNorm G := by
  let μ := volume.restrict (Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2))
  have hi {f : ℝ → ℝ} (hf : Continuous f) : Integrable f μ :=
    hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  unfold kepLogSlopeNorm
  rw [← integral_const_mul]
  apply integral_mono_ae (hi (hF.mul hG).abs) (hi (hG.abs.const_mul A))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul_of_nonneg_right (hA s hs) (abs_nonneg _)

theorem kepLogSlopeNorm_uniform {F : ℝ → ℝ} {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |F s| ≤ A) :
    kepLogSlopeNorm F ≤ 2 * A := by
  have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict
    (Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2))) (C := A) (f := fun s => |F s|)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        simpa only [Real.norm_eq_abs, abs_abs] using hA s hs)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _)),
    measureReal_restrict_apply_univ] at hi
  exact hi.trans (by nlinarith [mul_le_mul_of_nonneg_left kep_logSlope_interval_volume hA0])

end

end PGM
