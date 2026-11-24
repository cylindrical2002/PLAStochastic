import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.DirichletHeatKernel.SineMomentUniqueness

/-!
# Uniqueness of measures from positive Laplace transforms

The measures need not have finite total mass. One positive exponential weight
makes them finite, and the map `t ↦ exp (-t)` places their weighted laws in `[0,1]`.
The proved compact moment uniqueness theorem identifies these laws. Applying
`-log` and the inverse positive weight recovers the original measures.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def laplaceWeightedMeasure (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity (fun t => ENNReal.ofReal (Real.exp (-t)))

theorem isFiniteMeasure_laplaceWeightedMeasure {μ : Measure ℝ}
    (hi : Integrable (fun t : ℝ => Real.exp (-t)) μ) :
    IsFiniteMeasure (laplaceWeightedMeasure μ) := by
  apply isFiniteMeasure_withDensity
  exact (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun t => Real.exp_nonneg (-t)))).mp hi.hasFiniteIntegral |>.ne

/-- Compact polynomial moments of the weighted pushforward are positive Laplace values. -/
theorem laplaceWeightedMeasure_moment (μ : Measure ℝ) (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂(laplaceWeightedMeasure μ).map (fun t => Real.exp (-t))) =
      ∫ t : ℝ, Real.exp (-((n : ℝ) + 1) * t) ∂μ := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  unfold laplaceWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  dsimp only
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  change Real.exp (-t) * Real.exp (-t) ^ n = _
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- On the nonnegative half-line, exponentially integrable measures are determined
by their transforms at the positive integers. No finite total mass is assumed. -/
theorem measure_eq_of_integer_laplace {μ ν : Measure ℝ}
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (hiμ : Integrable (fun t : ℝ => Real.exp (-t)) μ)
    (hiν : Integrable (fun t : ℝ => Real.exp (-t)) ν)
    (hm : ∀ n : ℕ, (∫ t : ℝ, Real.exp (-((n : ℝ) + 1) * t) ∂μ) =
      ∫ t : ℝ, Real.exp (-((n : ℝ) + 1) * t) ∂ν) : μ = ν := by
  have := isFiniteMeasure_laplaceWeightedMeasure hiμ
  have := isFiniteMeasure_laplaceWeightedMeasure hiν
  have hs (ρ : Measure ℝ) (hρ : ∀ᵐ t ∂ρ, 0 ≤ t) :
      ∀ᵐ x ∂(laplaceWeightedMeasure ρ).map (fun t => Real.exp (-t)), x ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
    filter_upwards [(withDensity_absolutelyContinuous ρ
      (fun t => ENNReal.ofReal (Real.exp (-t)))).ae_le hρ] with t ht
    exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)⟩
  have hmap : (laplaceWeightedMeasure μ).map (fun t => Real.exp (-t)) =
      (laplaceWeightedMeasure ν).map (fun t => Real.exp (-t)) := by
    apply measure_eq_of_compact_moments (hs μ hμ) (hs ν hν)
    intro n
    rw [laplaceWeightedMeasure_moment, laplaceWeightedMeasure_moment, hm]
  have hrecover (ρ : Measure ℝ) :
      (ρ.map (fun t : ℝ => Real.exp (-t))).map (fun x => -Real.log x) = ρ := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, Real.log_exp, neg_neg]
    exact Measure.map_id
  have hweight : laplaceWeightedMeasure μ = laplaceWeightedMeasure ν := by
    have hh := congrArg (fun ρ : Measure ℝ => ρ.map (fun x => -Real.log x)) hmap
    simpa only [hrecover] using hh
  have hundo (ρ : Measure ℝ) :
      (laplaceWeightedMeasure ρ).withDensity
        (fun t => (ENNReal.ofReal (Real.exp (-t)))⁻¹) = ρ :=
    withDensity_inv_same (μ := ρ) (by fun_prop)
      (Eventually.of_forall (fun t => (ENNReal.ofReal_pos.mpr (Real.exp_pos (-t))).ne'))
      (Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top))
  rw [← hundo μ, ← hundo ν, hweight]

/-- Equality of every positive Laplace transform identifies the actual measures,
even when only their exponential weights are known to have finite mass. -/
theorem measure_eq_of_positive_laplace {μ ν : Measure ℝ}
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t)
    (hiμ : ∀ lam : ℝ, 0 < lam → Integrable (fun t => Real.exp (-lam * t)) μ)
    (hiν : ∀ lam : ℝ, 0 < lam → Integrable (fun t => Real.exp (-lam * t)) ν)
    (hm : ∀ lam : ℝ, 0 < lam → (∫ t, Real.exp (-lam * t) ∂μ) =
      ∫ t, Real.exp (-lam * t) ∂ν) : μ = ν := by
  apply measure_eq_of_integer_laplace hμ hν
  · simpa only [neg_one_mul] using hiμ 1 zero_lt_one
  · simpa only [neg_one_mul] using hiν 1 zero_lt_one
  · intro n
    exact hm ((n : ℝ) + 1) (by positivity)

end BrownianAffine
