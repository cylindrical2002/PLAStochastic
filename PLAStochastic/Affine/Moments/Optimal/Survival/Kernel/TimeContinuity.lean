import PLAStochastic.Affine.Moments.Optimal.Survival.Kernel.MiddleKernel
import PLAStochastic.Affine.Moments.Optimal.Survival.Kernel.EdgeMeasure

/-! # A continuous finite-measure representation for the three-piece kernel -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalSurvivalEdgeProduct (a b : ℝ) : Measure (ℝ × ℝ) :=
  (optimalSurvivalEdgeMeasure a).prod (optimalSurvivalEdgeMeasure (1-b))

theorem isFiniteMeasure_optimalSurvivalEdgeProduct {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
    IsFiniteMeasure (optimalSurvivalEdgeProduct a b) := by
  have := isFiniteMeasure_optimalSurvivalEdgeMeasure ha
  have hb' : 1-b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
  have := isFiniteMeasure_optimalSurvivalEdgeMeasure hb'
  unfold optimalSurvivalEdgeProduct
  infer_instance

theorem optimalSurvivalEdgeProduct_univ_le_four {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
    optimalSurvivalEdgeProduct a b univ ≤ 4 := by
  have hb' : 1-b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.2], by linarith [hb.1]⟩
  have := isFiniteMeasure_optimalSurvivalEdgeMeasure ha
  have := isFiniteMeasure_optimalSurvivalEdgeMeasure hb'
  rw [optimalSurvivalEdgeProduct, ← univ_prod_univ, Measure.prod_prod]
  exact (mul_le_mul' (optimalSurvivalEdgeMeasure_univ_le_two ha)
    (optimalSurvivalEdgeMeasure_univ_le_two hb')).trans_eq (by norm_num)

def optimalSurvivalTimeIntegral (a b T : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, optimalSurvivalMiddleKernel (T-p.1-p.2) ∂optimalSurvivalEdgeProduct a b

theorem integrable_optimalSurvivalTimeIntegrand {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (T : ℝ) :
    Integrable (fun p : ℝ × ℝ => optimalSurvivalMiddleKernel (T-p.1-p.2))
      (optimalSurvivalEdgeProduct a b) := by
  have := isFiniteMeasure_optimalSurvivalEdgeProduct ha hb
  obtain ⟨M,hM⟩ := bddAbove_norm_optimalSurvivalMiddleKernel
  exact (integrable_const M).mono'
    (continuous_optimalSurvivalMiddleKernel.comp (by fun_prop)).measurable.aestronglyMeasurable
    (Eventually.of_forall fun p => hM (mem_range_self (T-p.1-p.2)))

/-- Dominated convergence uses only finite edge masses and the bounded continuous
middle factor; no half-line pointwise exit estimate is assumed. -/
theorem continuous_optimalSurvivalTimeIntegral {a b : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) :
    Continuous (optimalSurvivalTimeIntegral a b) := by
  have := isFiniteMeasure_optimalSurvivalEdgeProduct ha hb
  obtain ⟨M,hM⟩ := bddAbove_norm_optimalSurvivalMiddleKernel
  apply continuous_of_dominated (bound := fun _ => M)
  · intro T
    exact ((continuous_optimalSurvivalMiddleKernel.comp (by fun_prop)).measurable).aestronglyMeasurable
  · intro T
    exact Eventually.of_forall fun p => hM (mem_range_self (T-p.1-p.2))
  · exact integrable_const M
  · exact Eventually.of_forall fun p => continuous_optimalSurvivalMiddleKernel.comp (by fun_prop)

/-- A single finite bound works for all starting and terminal locations. -/
theorem exists_bound_optimalSurvivalTimeIntegral :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1, ∀ T : ℝ,
      ‖optimalSurvivalTimeIntegral a b T‖ ≤ M := by
  obtain ⟨M,hM⟩ := bddAbove_norm_optimalSurvivalMiddleKernel
  have hM0 : 0 ≤ M := (norm_nonneg (optimalSurvivalMiddleKernel 0)).trans (hM (mem_range_self 0))
  refine ⟨4*M, by positivity, ?_⟩
  intro a ha b hb T
  have := isFiniteMeasure_optimalSurvivalEdgeProduct ha hb
  have hh := norm_integral_le_of_norm_le_const (μ := optimalSurvivalEdgeProduct a b)
    (f := fun p : ℝ × ℝ => optimalSurvivalMiddleKernel (T-p.1-p.2))
    (Eventually.of_forall fun p => hM (mem_range_self (T-p.1-p.2)))
  have hm : (optimalSurvivalEdgeProduct a b).real univ ≤ 4 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by
      simpa using optimalSurvivalEdgeProduct_univ_le_four ha hb)
  exact hh.trans (by nlinarith)

end BrownianAffine
