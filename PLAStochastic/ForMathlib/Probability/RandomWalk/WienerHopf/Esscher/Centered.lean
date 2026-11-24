import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Esscher.Class

/-!
# Recentring a tilted step law

The drifted class can be fed back to the existing centred step-class API by
subtracting its actual mean. Constants are explicit; no small-drift claim is
implicit in the operation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PGM.WienerHopf

namespace IsDriftedStepLaw

variable {ρ : Measure ℝ} {f : ℝ → ℝ} {D θ μ v : ℝ}

theorem integrable_id (h : IsDriftedStepLaw ρ f D θ μ v) :
    Integrable (fun y : ℝ => y) ρ := by
  have := h.isProbabilityMeasure
  refine ((integrable_const 1).add h.integrable_sq).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  dsimp only [Pi.add_apply]
  nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 1)]

theorem centered (h : IsDriftedStepLaw ρ f D θ μ v) (hD : 0 ≤ D) (hθ : 0 ≤ θ) :
    IsStepLaw (driftStep ρ (-μ)) (fun y => f (y + μ))
      (D * Real.exp (θ * |μ|)) θ (2 * v + 2 * μ ^ 2) := by
  have := h.isProbabilityMeasure
  have hf := h.measurable
  have hsqi : Integrable (fun y : ℝ => (y + -μ) ^ 2) ρ := by
    refine ((h.integrable_sq.const_mul 2).add (integrable_const (2 * μ ^ 2))).mono'
      (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (y + μ)]
  refine ⟨inferInstance, ?_, by fun_prop, fun y => h.nonneg _, ?_, ?_, ?_, ?_⟩
  · have hT : Measurable fun y : ℝ => y + -μ := by fun_prop
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    have hfE := h.measurable.ennreal_ofReal
    have hfE' : Measurable fun y => ENNReal.ofReal (f (y + μ)) := by fun_prop
    have hgT : Measurable fun y : ℝ => g (y + -μ) := hg.comp hT
    rw [driftStep, lintegral_map hg hT, h.eq_withDensity,
      lintegral_withDensity_eq_lintegral_mul _ hfE hgT,
      lintegral_withDensity_eq_lintegral_mul _ hfE' hg]
    simp only [Pi.mul_apply]
    rw [← lintegral_add_right_eq_self (fun y => ENNReal.ofReal (f (y + μ)) * g y) (-μ)]
    simp only [neg_add_cancel_right]
  · intro y
    calc
      f (y + μ) ≤ D * Real.exp (-θ * |y + μ|) := h.le_exp _
      _ ≤ D * Real.exp (θ * |μ| - θ * |y|) := by
        gcongr
        have hh : |y| ≤ |y + μ| + |μ| := by
          simpa only [add_assoc, add_neg_cancel, add_zero, abs_neg] using abs_add_le (y + μ) (-μ)
        nlinarith
      _ = D * Real.exp (θ * |μ|) * Real.exp (-θ * |y|) := by
        rw [show θ * |μ| - θ * |y| = θ * |μ| + -θ * |y| by ring,
          Real.exp_add, mul_assoc]
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hsqi
  · rw [driftStep, integral_map (by fun_prop) (by fun_prop),
      integral_add h.integrable_id (integrable_const (-μ)), h.integral_id]
    simp
  · rw [driftStep, integral_map (by fun_prop) (by fun_prop)]
    calc
      (∫ y, (y + -μ) ^ 2 ∂ρ) ≤ ∫ y, 2 * y ^ 2 + 2 * μ ^ 2 ∂ρ := by
        exact integral_mono hsqi
          ((h.integrable_sq.const_mul 2).add (integrable_const (2 * μ ^ 2)))
          (fun y => by dsimp only; nlinarith [sq_nonneg (y + μ)])
      _ = 2 * (∫ y, y ^ 2 ∂ρ) + 2 * μ ^ 2 := by
        rw [integral_add (h.integrable_sq.const_mul 2) (integrable_const (2 * μ ^ 2)),
          integral_const_mul]
        simp
      _ ≤ 2 * v + 2 * μ ^ 2 := by linarith [h.integral_sq_le]

end IsDriftedStepLaw

end PGM.WienerHopf
