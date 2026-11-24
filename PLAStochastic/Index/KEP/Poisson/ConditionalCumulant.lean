import PLAStochastic.Index.KEP.Poisson.PositiveMoments
import PLAStochastic.Index.KEP.ConditionalExponential

/-!
# Conditional mean and cumulant bounds in the parent anchor units

The original child-law mean is dilated by the true intensity ratio. The
uniform intensity bounds pay its first moment as well as the fixed
exponential moment, giving a compensated conditional exponential budget.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem kepPoisson_fixed_scale_mean {f : ℝ → ℝ} {flo fhi L eps n m : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hm : 0 ≤ m) (j : ℕ)
    (hchild : ∀ y, Integrable (fun z : ℝ => z) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, z ∂kepPoissonLayerMeasure hf eps n y j ≤ m) (x y : ℝ) :
    Integrable (fun z : ℝ => z) (kepPoissonFixedScaleMeasure hf eps n x y j) ∧
      ∫ z, z ∂kepPoissonFixedScaleMeasure hf eps n x y j ≤ (fhi / flo) * m := by
  let c := f x / f y
  have hc : 0 ≤ c := (div_pos (hf.f_pos x) (hf.f_pos y)).le
  have hF : Measurable (fun z : ℝ => c * z) := measurable_const.mul measurable_id
  change Integrable (fun z : ℝ => z) ((kepPoissonLayerMeasure hf eps n y j).map (fun z => c * z)) ∧ _
  refine ⟨(integrable_map_measure measurable_id.aestronglyMeasurable hF.aemeasurable).mpr
    ((hchild y).1.const_mul c), ?_⟩
  change (∫ z, z ∂(kepPoissonLayerMeasure hf eps n y j).map (fun z => c * z)) ≤ _
  have hid : Measurable (fun z : ℝ => z) := measurable_id
  rw [integral_map hF.aemeasurable hid.aestronglyMeasurable, integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (hchild y).2 hc).trans
    (mul_le_mul_of_nonneg_right (hf.ratio_le x y) hm)

theorem kepPoisson_fixed_scale_ae_nonneg {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (j : ℕ)
    (hm : 0 ≤ kepReferenceSpan eps j) (x y : ℝ) :
    ∀ᵐ z ∂kepPoissonFixedScaleMeasure hf eps n x y j, 0 ≤ z := by
  apply (ae_map_iff (measurable_const.mul measurable_id).aemeasurable measurableSet_Ici).mpr
  filter_upwards [kepPoissonLayerMeasure_ae_nonneg hf hn y j hm] with z hz
  exact mul_nonneg (div_nonneg (hf.f_pos x).le (hf.f_pos y).le) hz

theorem kepPoisson_fixed_scale_compensated_exp {f : ℝ → ℝ} {flo fhi L eps n theta B t d : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (j : ℕ) (hm : 0 ≤ kepReferenceSpan eps j)
    (hmean : ∀ y, Integrable (fun z : ℝ => z) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, z ∂kepPoissonLayerMeasure hf eps n y j ≤ 2)
    (hexp : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B)
    (ht : 0 ≤ t) (hta : t ≤ (theta / (fhi / flo)) / 2)
    (hcost : 8 * B / (theta / (fhi / flo)) ^ 2 * t ≤ fhi / flo)
    (hd : 3 * (fhi / flo) * t ≤ d) (x y : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (t * z - d))
      ∂kepPoissonFixedScaleMeasure hf eps n x y j ≤ 1 := by
  have hR : 0 < fhi / flo := div_pos hf.fhi_pos hf.pos
  have hmu := kepPoisson_fixed_scale_mean hf (by norm_num : (0 : ℝ) ≤ 2) j hmean x y
  have he := kepPoisson_fixed_scale_exp_moment hf hn htheta.le j hm hexp x y
  obtain ⟨hi, hb⟩ := integral_exp_mul_le_of_mean_expMom (div_pos htheta hR)
    (kepPoisson_fixed_scale_ae_nonneg hf hn j hm x y) hmu.1 hmu.2 he.1 he.2 ht hta
  have hb' : ∫ z, Real.exp (t * z) ∂kepPoissonFixedScaleMeasure hf eps n x y j ≤ Real.exp d := by
    apply hb.trans (Real.exp_le_exp.mpr ?_)
    have hq := mul_le_mul_of_nonneg_right hcost ht
    nlinarith
  have hi' : Integrable (fun z => Real.exp (t * z - d))
      (kepPoissonFixedScaleMeasure hf eps n x y j) := by
    refine (hi.mul_const (Real.exp (-d))).congr (Filter.Eventually.of_forall fun z => ?_)
    change Real.exp (t * z) * Real.exp (-d) = Real.exp (t * z - d)
    rw [sub_eq_add_neg, Real.exp_add]
  rw [← ofReal_integral_eq_lintegral_ofReal hi'
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _), ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (∫ z, Real.exp (t * z) ∂kepPoissonFixedScaleMeasure hf eps n x y j) * Real.exp (-d) := by
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
        change Real.exp (t * z - d) = Real.exp (t * z) * Real.exp (-d)
        rw [sub_eq_add_neg, Real.exp_add])
    _ ≤ Real.exp d * Real.exp (-d) := mul_le_mul_of_nonneg_right hb' (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

end

end PGM
