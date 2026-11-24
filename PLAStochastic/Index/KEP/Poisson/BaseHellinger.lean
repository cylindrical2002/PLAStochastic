import PLAStochastic.Index.KEP.Poisson.BaseGapQuadratic
import PLAStochastic.ForMathlib.Probability.Hellinger.ExponentialTransportBudget
import PLAStochastic.ForMathlib.Probability.Hellinger.MeasureMetric

/-!
# Unconditional Hellinger entry for the actual nonhomogeneous Poisson base gap

The true inverse intensity transformation pays both displacement and Jacobian
errors. Its Hellinger distance from Exp(1) is of inverse intensity order, with
one constant for every physical anchor. The same base law has a fixed uniform
exponential moment; no base comparison premise remains.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepPoissonBaseMeasure_hellinger_le {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) :
    measureHellinger (kepPoissonBaseMeasure hf n x) (expMeasure 1) ≤
      (L / flo ^ 2) * Real.sqrt (exponentialTransportIntegral (flo / fhi)) / n := by
  let e := kepPoissonGapOrderIso hf hn x
  let d := kepPoissonGapDerivative hf n x
  let q := kepPoissonInverseGapDensity hf hn x
  have he0 : e 0 = 0 := by
    change n * f x * (kepPoissonArrival hf n x 0 - x) = 0
    rw [kepPoissonArrival_zero, sub_self, mul_zero]
  have ha : 0 < flo / fhi := div_pos hf.pos hf.fhi_pos
  have ha1 : flo / fhi ≤ 1 := (div_le_one hf.fhi_pos).mpr hf.flo_le_fhi
  have hB : 0 ≤ L / flo ^ 2 := div_nonneg hf.lip_nonneg (sq_nonneg _)
  have hbudget : positiveExpDensity.hellinger q ≤
      (L / flo ^ 2) * Real.sqrt (exponentialTransportIntegral (flo / fhi)) / n := by
    exact hellinger_positiveExp_pullback_le e d
      (kepPoissonNormalizedGap_hasDerivAt hf hn x)
      (kepPoissonGapDerivative_measurable hf n x) (kepPoissonGapDerivative_pos hf n x)
      he0 ha ha1 hB hn (fun t ht => (kepPoissonNormalizedGap_bracket hf hn ht x).1)
      (fun t ht => kepPoissonNormalizedGap_sub_bound hf hn ht x)
      (fun t ht => kepPoissonGapDerivative_sub_one_bound hf hn ht x)
  have hpsi := measurable_kepPoissonNormalizedGap hf n x
  have htime : Measurable (kepPoissonNormalizedTime hf n x) := e.symm.continuous.measurable
  have hefun : kepPoissonNormalizedGap hf n x ∘ kepPoissonNormalizedTime hf n x = id :=
    funext (kepPoissonNormalizedGap_time hf hn x)
  have hmap : q.toMeasure.map (kepPoissonNormalizedGap hf n x) = expMeasure 1 := by
    rw [kepPoissonInverseGapDensity_toMeasure, Measure.map_map hpsi htime, hefun, Measure.map_id]
  have h := measureHellinger_map_le_density positiveExpDensity q hpsi
  have hactual : measureHellinger (kepPoissonBaseMeasure hf n x) (expMeasure 1) ≤
      positiveExpDensity.hellinger q := by
    simpa only [positiveExpDensity_toMeasure, hmap, kepPoissonBaseMeasure] using h
  exact hactual.trans hbudget

theorem kepPoisson_base_uniform_budgets {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) :
    ∃ theta K : ℝ, 0 < theta ∧ 0 < K ∧ ∀ n : ℝ, 0 < n → ∀ x : ℝ,
      measureHellinger (kepPoissonBaseMeasure hf n x) (expMeasure 1) ≤ K / n ∧
      Integrable (fun z => Real.exp (theta * z)) (kepPoissonBaseMeasure hf n x) ∧
      (∫ z, Real.exp (theta * z) ∂kepPoissonBaseMeasure hf n x) ≤ 2 := by
  let theta := flo / (2 * fhi)
  let B := (L / flo ^ 2) * Real.sqrt (exponentialTransportIntegral (flo / fhi))
  have htheta : 0 < theta := div_pos hf.pos (mul_pos (by norm_num) hf.fhi_pos)
  have hB : 0 ≤ B := mul_nonneg (div_nonneg hf.lip_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨theta, B + 1, htheta, by linarith only [hB], ?_⟩
  intro n hn x
  refine ⟨(kepPoissonBaseMeasure_hellinger_le hf hn x).trans
    (div_le_div_of_nonneg_right (by dsimp [B]; linarith) hn.le), ?_⟩
  exact kepPoissonBaseMeasure_exponential_moment hf hn htheta.le le_rfl x

end

end PGM
