import PLAStochastic.Index.KEP.ReferenceScale.KernelSecond
import PLAStochastic.Index.KEP.ReferenceScale.GammaWeighted
import PLAStochastic.ForMathlib.MeasureTheory.Integral.ReciprocalSubstitution

/-!
# Paying the actual endpoint derivative by a slope integral

The one-step derivative at a fixed band endpoint is not replaced by a
pointwise roughness bound. Reciprocal substitution pays its first derivative
L1 norm, with the physical numerator retained in the exact formula. Both
orientations of the actual residual kernel are included.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

private theorem abs_kepStepSpatialFirst_of_pos (f' : ℝ → ℝ) (β t : ℝ)
    {a : ℝ} (ha : 0 < a) :
    |kepStepSpatialFirst f' β a t| = |f' ((β - t) / a)| / a ^ 2 := by
  simp only [kepStepSpatialFirst, abs_div, abs_neg, abs_mul, abs_of_pos ha,
    pow_two]

/-- The inverse physical numerator remains explicit. -/
theorem integral_abs_kepStepSpatialFirst_slope (f' : ℝ → ℝ) {β t lo hi : ℝ}
    (hc : 0 < β - t) (hlo : 0 < lo) (hle : lo ≤ hi) :
    (∫ a in Icc lo hi, |kepStepSpatialFirst f' β a t|) =
      (∫ x in Icc ((β - t) / hi) ((β - t) / lo), |f' x|) / (β - t) := by
  calc
    _ = ∫ a in Icc lo hi, |f' ((β - t) / a)| / a ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro a ha
      exact abs_kepStepSpatialFirst_of_pos f' β t (hlo.trans_le ha.1)
    _ = _ := integral_div_sq_comp_reciprocal_Icc (fun x => |f' x|) hc hlo hle

theorem integrableOn_abs_kepStepSpatialFirst_slope {f' : ℝ → ℝ} {β t lo hi : ℝ}
    (hf' : Integrable f' volume) (hc : 0 < β - t) (hlo : 0 < lo) (hle : lo ≤ hi) :
    IntegrableOn (fun a => |kepStepSpatialFirst f' β a t|) (Icc lo hi) := by
  have h := integrableOn_div_sq_comp_reciprocal_Icc hc hlo hle hf'.abs.integrableOn
  exact h.congr_fun (fun a ha =>
    (abs_kepStepSpatialFirst_of_pos f' β t (hlo.trans_le ha.1)).symm) measurableSet_Icc

theorem integral_abs_kepStepSpatialFirst_slope_le {f' : ℝ → ℝ} {β t lo hi : ℝ}
    (hf' : Integrable f' volume) (hc : 0 < β - t) (hlo : 0 < lo) (hle : lo ≤ hi) :
    (∫ a in Icc lo hi, |kepStepSpatialFirst f' β a t|) ≤ (∫ x, |f' x|) / (β - t) := by
  rw [integral_abs_kepStepSpatialFirst_slope f' hc hlo hle]
  exact div_le_div_of_nonneg_right
    (setIntegral_le_integral hf'.abs (ae_of_all _ (fun _ => abs_nonneg _))) hc.le

private theorem kepStepSpatialFirst_slope_budget {f' : ℝ → ℝ} {β t lo hi : ℝ}
    (hf' : Integrable f' volume) (hz : ∀ x, x ≤ 0 → f' x = 0)
    (hc : 1 ≤ β - t ∨ β - t ≤ 0) (hlo : 0 < lo) (hle : lo ≤ hi) :
    IntegrableOn (fun a => |kepStepSpatialFirst f' β a t|) (Icc lo hi) ∧
      (∫ a in Icc lo hi, |kepStepSpatialFirst f' β a t|) ≤ ∫ x, |f' x| := by
  rcases hc with hc | hc
  · have hc0 : 0 < β - t := lt_of_lt_of_le zero_lt_one hc
    refine ⟨integrableOn_abs_kepStepSpatialFirst_slope hf' hc0 hlo hle,
      (integral_abs_kepStepSpatialFirst_slope_le hf' hc0 hlo hle).trans ?_⟩
    exact (div_le_iff₀ hc0).mpr (by
      have hJ : 0 ≤ ∫ x, |f' x| := integral_nonneg (fun _ => abs_nonneg _)
      nlinarith)
  · have he (a : ℝ) (ha : a ∈ Icc lo hi) : |kepStepSpatialFirst f' β a t| = 0 := by
      have ha0 := (hlo.trans_le ha.1).le
      rw [kepStepSpatialFirst, hz _ (div_nonpos_of_nonpos_of_nonneg hc ha0)]
      simp
    constructor
    · exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Icc lo hi)).congr_fun
        (fun a ha => (he a ha).symm) measurableSet_Icc
    · rw [setIntegral_eq_zero_of_forall_eq_zero he]
      exact integral_nonneg (fun _ => abs_nonneg _)

/-- The physical numerators at the two endpoints are `1`, `1-w`, and `1+w`.
For `w ≥ 2`, each is either at least one or nonpositive. -/
theorem kepStepSpatialFirst_endpoint_slope_budget {f' : ℝ → ℝ} {w y b lo hi : ℝ}
    (hf' : Integrable f' volume) (hz : ∀ x, x ≤ 0 → f' x = 0)
    (hw : 2 ≤ w) (hy : y = 0 ∨ y = w) (hb : b = 0 ∨ b = w)
    (hlo : 0 < lo) (hle : lo ≤ hi) :
    IntegrableOn (fun a => |kepStepSpatialFirst f' 1 a (y - b)|) (Icc lo hi) ∧
      (∫ a in Icc lo hi, |kepStepSpatialFirst f' 1 a (y - b)|) ≤ ∫ x, |f' x| := by
  apply kepStepSpatialFirst_slope_budget hf' hz ?_ hlo hle
  rcases hy with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | (left; linarith) | (right; linarith)

theorem abs_kepStepSpatialFirst_reverse (f' : ℝ → ℝ) (a t : ℝ) :
    |kepStepSpatialFirst f' (-1) (-a) t| = |kepStepSpatialFirst f' 1 a (-t)| := by
  have he : (-1 - t) / (-a) = (1 - (-t)) / a := by ring
  simp only [kepStepSpatialFirst, he, abs_div, abs_neg, abs_mul, abs_abs]

theorem kepStepSpatialFirst_reverse_endpoint_slope_budget {f' : ℝ → ℝ} {w y b lo hi : ℝ}
    (hf' : Integrable f' volume) (hz : ∀ x, x ≤ 0 → f' x = 0)
    (hw : 2 ≤ w) (hy : y = 0 ∨ y = w) (hb : b = 0 ∨ b = w)
    (hlo : 0 < lo) (hle : lo ≤ hi) :
    IntegrableOn (fun a => |kepStepSpatialFirst f' (-1) (-a) (y - b)|) (Icc lo hi) ∧
      (∫ a in Icc lo hi, |kepStepSpatialFirst f' (-1) (-a) (y - b)|) ≤ ∫ x, |f' x| := by
  have he : (fun a => |kepStepSpatialFirst f' (-1) (-a) (y - b)|) =
      (fun a => |kepStepSpatialFirst f' 1 a (b - y)|) := by
    funext a
    rw [abs_kepStepSpatialFirst_reverse, neg_sub]
  rw [he]
  exact kepStepSpatialFirst_endpoint_slope_budget hf' hz hw hb hy hlo hle

/-- An arbitrary bounded measurable coefficient may multiply the endpoint
term. No derivative of that coefficient is used in the slope average. -/
theorem kepStepSpatialFirst_endpoint_coefficient_budget {f' q : ℝ → ℝ}
    {w y b lo hi Q : ℝ}
    (hf' : Integrable f' volume) (hz : ∀ x, x ≤ 0 → f' x = 0)
    (hw : 2 ≤ w) (hy : y = 0 ∨ y = w) (hb : b = 0 ∨ b = w)
    (hlo : 0 < lo) (hle : lo ≤ hi) (hq : Measurable q)
    (hQ : 0 ≤ Q) (hqQ : ∀ a ∈ Icc lo hi, |q a| ≤ Q) :
    IntegrableOn (fun a => |q a| * |kepStepSpatialFirst f' 1 a (y - b)|) (Icc lo hi) ∧
      (∫ a in Icc lo hi, |q a| * |kepStepSpatialFirst f' 1 a (y - b)|) ≤
        Q * (∫ x, |f' x|) := by
  obtain ⟨hint, hJ⟩ := kepStepSpatialFirst_endpoint_slope_budget hf' hz hw hy hb hlo hle
  have hdom : IntegrableOn (fun a => Q * |kepStepSpatialFirst f' 1 a (y - b)|)
      (Icc lo hi) := hint.const_mul Q
  have hmul : IntegrableOn (fun a => |q a| * |kepStepSpatialFirst f' 1 a (y - b)|)
      (Icc lo hi) := by
    refine hdom.mono' (hq.abs.aestronglyMeasurable.mul hint.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    exact mul_le_mul_of_nonneg_right (hqQ a ha) (abs_nonneg _)
  refine ⟨hmul, ?_⟩
  calc
    _ ≤ ∫ a in Icc lo hi, Q * |kepStepSpatialFirst f' 1 a (y - b)| := by
      apply integral_mono_ae hmul hdom
      filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
      exact mul_le_mul_of_nonneg_right (hqQ a ha) (abs_nonneg _)
    _ = Q * (∫ a in Icc lo hi, |kepStepSpatialFirst f' 1 a (y - b)|) :=
      integral_const_mul _ _
    _ ≤ Q * (∫ x, |f' x|) := mul_le_mul_of_nonneg_left hJ hQ

/-- The hypotheses on the physical input are discharged for every actual
positive reference layer. This covers both residual orientations. -/
theorem kepReference_endpoint_slope_budget {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {w y b lo hi σ : ℝ} (hw : 2 ≤ w) (hy : y = 0 ∨ y = w)
    (hb : b = 0 ∨ b = w) (hlo : 0 < lo) (hle : lo ≤ hi) (hσ : σ = 1 ∨ σ = -1) :
    let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
    IntegrableOn (fun a => |kepStepSpatialFirst f' σ (σ * a) (y - b)|) (Icc lo hi) ∧
      (∫ a in Icc lo hi, |kepStepSpatialFirst f' σ (σ * a) (y - b)|) ≤ ∫ x, |f' x| := by
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  have hfinite := kepReferenceDensity_classical heps hj
  have hi : Integrable f' volume := hfinite.2.2.2.2.1
  have hm := kepReferenceSpan_pos heps j
  have hz (x : ℝ) (hx : x ≤ 0) : f' x = 0 := by
    have hmx := mul_nonpos_of_nonneg_of_nonpos hm.le hx
    dsimp [f', gammaScaledFirst, gammaMixtureFirst]
    rw [gammaMixtureDensity_succ_of_nonpos _ 1 hmx,
      gammaMixtureDensity_succ_of_nonpos _ 2 hmx, sub_self, mul_zero]
  rcases hσ with rfl | rfl
  · simpa only [one_mul] using
      kepStepSpatialFirst_endpoint_slope_budget hi hz hw hy hb hlo hle
  · simpa only [neg_one_mul] using
      kepStepSpatialFirst_reverse_endpoint_slope_budget hi hz hw hy hb hlo hle

end

end PGM
