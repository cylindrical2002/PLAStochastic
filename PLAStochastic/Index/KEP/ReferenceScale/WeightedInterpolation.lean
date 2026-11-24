import PLAStochastic.Index.KEP.ReferenceScale.GammaWeighted
import PLAStochastic.ForMathlib.Probability.Hellinger.WeightedDerivativeInterpolation

/-!
# Fixed-weight first-derivative interpolation on the actual orbit

The exponent and interpolation constant are chosen before epsilon and the layer.
The second norm is the actual weighted Gamma derivative norm. Its finiteness is
unconditional, while its layer-uniform polynomial budget still requires the
full greedy-output recurrence.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

def kepReferenceWeightedSecondNorm (theta eps : ℝ) (j : ℕ) : ℝ :=
  ∫ t, Real.exp (theta * t) *
    |gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t|

theorem kepReferenceWeightedSecondNorm_nonneg (theta eps : ℝ) (j : ℕ) :
    0 ≤ kepReferenceWeightedSecondNorm theta eps j := integral_nonneg fun _ => by positivity

theorem kepReferenceWeightedFirstNorm_le_of_regular {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    {D theta0 vlo vhi theta : ℝ} (htheta0 : 0 < theta0) (hvlo : 0 < vlo)
    (hreg : RegLaw D theta0 vlo vhi (kepReferenceLaw eps j))
    (htheta : 0 ≤ theta) (htheta_le : theta ≤ theta0 / 2) (htheta_small : theta ≤ 1 / 2) :
    (∫ t, Real.exp (theta * t) *
      |gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j) t|) ≤
      (2 * (1 + 4 * theta) * ((2 + theta + theta ^ 2) * (2 * D / theta0) + 1)) *
        Real.sqrt (1 + kepReferenceWeightedSecondNorm theta eps j) := by
  let p := kepReferenceDensity heps hj
  let Z := ∫ t, Real.exp (theta * t) * p.density t
  have hEM := (hreg.expMom htheta0).mono (hreg.momClass htheta0 hvlo).pos
    htheta htheta_le le_rfl
  have hiLaw : Integrable (fun t => Real.exp (theta * t)) p.toMeasure := by
    rw [kepReferenceDensity_toMeasure heps hj]
    exact hEM.integrable
  have hi : Integrable (fun t => Real.exp (theta * t) * p.density t) volume := by
    simpa only [mul_comm] using (p.integrable_toMeasure_iff _).mp hiLaw
  have hZ1 : 1 ≤ Z := by
    rw [← p.integral_eq_one]
    apply integral_mono p.integrable hi
    intro t
    change p.density t ≤ Real.exp (theta * t) * p.density t
    by_cases ht : 0 ≤ t
    · exact le_mul_of_one_le_left (p.nonneg t) (Real.one_le_exp (mul_nonneg htheta ht))
    · have hz := (kepReferenceDensity_classical heps hj).1 t (le_of_lt (lt_of_not_ge ht))
      change (kepReferenceDensity heps hj).density t ≤ _
      rw [hz, mul_zero]
  have hZpos : 0 < Z := by linarith
  have hZ : Z ≤ 2 * D / theta0 := by
    have he := p.integral_toMeasure (fun t => Real.exp (theta * t))
    rw [kepReferenceDensity_toMeasure heps hj] at he
    have hb := hEM.le
    rw [he] at hb
    simpa only [mul_comm] using hb
  obtain ⟨hi', hi'', -, -⟩ := kepReferenceDensity_weighted_of_regular heps hj
    htheta0 hvlo hreg htheta htheta_le htheta_small
  have hc := kepReferenceDensity_classical heps hj
  have hb := p.weighted_integral_abs_derivative_le_sqrt htheta hZpos rfl
    (continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt)
    hc.2.2.2.1 hc.2.1 hc.2.2.1 hi hi' hi''
  apply hb.trans
  have hD0 := hreg.D_nonneg
  dsimp only [kepReferenceWeightedSecondNorm]
  gcongr

theorem kepReference_weighted_first_interpolation :
    ∃ theta K eps0 : ℝ, 0 < theta ∧ 0 < K ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ j, 1 ≤ j →
        Integrable (fun t => Real.exp (theta * t) *
          gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j) t) volume ∧
        Integrable (fun t => Real.exp (theta * t) *
          gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t) volume ∧
        (∫ t, Real.exp (theta * t) *
          |gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j) t|) ≤
            K * Real.sqrt (1 + kepReferenceWeightedSecondNorm theta eps j) := by
  obtain ⟨D, theta0, vlo, vhi, e0, hD, ht0, hvlo, -, hreg⟩ := kepReferenceLaw_regular
  let theta := min (theta0 / 2) (1 / 2)
  let K := 2 * (1 + 4 * theta) * ((2 + theta + theta ^ 2) * (2 * D / theta0) + 1)
  have ht : 0 < theta := lt_min (by positivity) (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨theta, K, max kepReferenceClassicalThreshold e0, ht, hK, le_max_left _ _, ?_⟩
  intro eps he j hj
  have heps : kepReferenceClassicalThreshold ≤ eps := (le_max_left _ _).trans he
  have hr : e0 ≤ eps := (le_max_right _ _).trans he
  have hg := hreg eps hr j
  obtain ⟨hi', hi'', -, -⟩ := kepReferenceDensity_weighted_of_regular heps hj
    ht0 hvlo hg ht.le (min_le_left _ _) (min_le_right _ _)
  exact ⟨hi', hi'', kepReferenceWeightedFirstNorm_le_of_regular heps hj ht0 hvlo hg
    ht.le (min_le_left _ _) (min_le_right _ _)⟩

end

end PGM
