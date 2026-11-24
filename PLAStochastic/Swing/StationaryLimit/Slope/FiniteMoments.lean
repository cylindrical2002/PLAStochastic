import PLAStochastic.Swing.StationaryLimit.Slope.Kernel
import PLAStochastic.Swing.Restart.Chain.FreshWalkEnvelope
import PLAStochastic.ForMathlib.Probability.Moments.IntegerGridExpTail

/-! # Finite moments of the actual limiting slope law

The fresh-walk envelope has a Gaussian tail.  A common integer exponential
tail gives its moments without assuming integrability, and the pathwise slope
bound then places the actual margin-to-slope law in the finite-first-moment
class needed for a Wasserstein coupling.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

def nativeGaussianEnvelopeExpTailConstant : ℝ :=
  (1 + nativeGaussianEnvelopeTailConstant) * Real.exp 1

lemma nativeGaussianEnvelopeExpTailConstant_nonneg :
    0 ≤ nativeGaussianEnvelopeExpTailConstant := by
  have := nativeGaussianEnvelope_tail_constant_pos
  unfold nativeGaussianEnvelopeExpTailConstant
  positivity

theorem nativeGaussianEnvelope_integer_exp_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    μ {ω | (n : ℝ) ≤ nativeGaussianEnvelope X ω} ≤
      ENNReal.ofReal (nativeGaussianEnvelopeExpTailConstant * Real.exp (-(n : ℝ))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hC : 0 ≤ nativeGaussianEnvelopeTailConstant := nativeGaussianEnvelope_tail_constant_pos.le
  have hfactor : nativeGaussianEnvelopeExpTailConstant * Real.exp (-(n : ℝ)) =
      (1+nativeGaussianEnvelopeTailConstant) * Real.exp (1-(n : ℝ)) := by
    unfold nativeGaussianEnvelopeExpTailConstant
    rw [mul_assoc, ← Real.exp_add]
    rfl
  have hreal : μ.real {ω | (n : ℝ) ≤ nativeGaussianEnvelope X ω} ≤
      nativeGaussianEnvelopeExpTailConstant * Real.exp (-(n : ℝ)) := by
    rw [hfactor]
    by_cases hn : 2 ≤ n
    · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hsub : {ω | (n : ℝ) ≤ nativeGaussianEnvelope X ω} ⊆
          {ω | (n : ℝ)-1 < nativeGaussianEnvelope X ω} := by
        intro ω hω
        change (n : ℝ) ≤ nativeGaussianEnvelope X ω at hω
        change (n : ℝ)-1 < nativeGaussianEnvelope X ω
        linarith
      have htail := nativeGaussianEnvelope_tail_bound hX hi hG
        (t := (n : ℝ)-1) (by linarith)
      have he : Real.exp (-((n : ℝ)-1)^2) ≤ Real.exp (1-(n : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg ((n : ℝ)-2)]
      exact (measureReal_mono hsub).trans (htail.trans
        ((mul_le_mul_of_nonneg_left he hC).trans
          (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)))
    · have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
      have he : 1 ≤ Real.exp (1-(n : ℝ)) := Real.one_le_exp (by linarith)
      have hprod : 1 ≤ (1+nativeGaussianEnvelopeTailConstant) * Real.exp (1-(n : ℝ)) := by
        nlinarith
      exact measureReal_le_one.trans hprod
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

theorem nativeGaussianEnvelope_integrable_pow
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (k : ℕ) :
    Integrable (fun ω => nativeGaussianEnvelope X ω ^ k) μ := by
  exact integrable_pow_of_expTail (nativeGaussianEnvelope_measurable hX)
    (ae_of_all _ (nativeGaussianEnvelope_nonneg X))
    nativeGaussianEnvelopeExpTailConstant_nonneg (by norm_num : (0 : ℝ) < 1)
    (by simpa using nativeGaussianEnvelope_integer_exp_tail hX hi hG) k

theorem nativeGaussianEnvelope_integral_pow_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (k : ℕ) :
    (∫ ω, nativeGaussianEnvelope X ω ^ k ∂μ) ≤
      nativeGaussianEnvelopeExpTailConstant * expTailMomentSum 1 k := by
  exact integral_pow_le_of_expTail (nativeGaussianEnvelope_measurable hX)
    (ae_of_all _ (nativeGaussianEnvelope_nonneg X))
    nativeGaussianEnvelopeExpTailConstant_nonneg (by norm_num : (0 : ℝ) < 1)
    (by simpa using nativeGaussianEnvelope_integer_exp_tail hX hi hG) k

omit [MeasurableSpace Ω] in
theorem swingLimitingSlope_le_envelope
    (r : ℝ) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ nativeGaussianEnvelope X ω * ((n : ℝ)+1)) :
    swingLimitingSlope X r ω ≤ |r| + nativeGaussianEnvelope X ω := by
  apply ciSup_le
  intro n
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
  have hr : -r ≤ |r| := neg_le_abs r
  have hw : cumulativeSamples X n ω ≤ |cumulativeSamples X n ω| := le_abs_self _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [hW n, abs_nonneg r]

theorem swingLimitingSlope_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    Integrable (swingLimitingSlope X r) μ := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have henv : Integrable (nativeGaussianEnvelope X) μ := by
    simpa only [pow_one] using nativeGaussianEnvelope_integrable_pow hX hi hG 1
  apply ((integrable_const |r|).add henv).mono'
    (swingLimitingSlope_measurable hX r).aestronglyMeasurable
  filter_upwards [nativeGaussianEnvelope_bounds_ae hX hi hG,
    swingLimitingSlope_pos_ae hX hi hG r] with ω hW hpos
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  exact swingLimitingSlope_le_envelope r ω hW

theorem swingSlopeKernel_first_moment_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    Integrable (fun a : ℝ => a) (swingSlopeKernel X μ r) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [swingSlopeKernel_eq_law hX r, swingLimitingSlopeLaw]
  exact (integrable_map_measure aestronglyMeasurable_id
    (swingLimitingSlope_measurable hX r).aemeasurable).mpr
      (swingLimitingSlope_integrable hX hi hG r)

theorem swingLimitingSlope_lipschitz_reward_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (r : ℝ) :
    Integrable (fun ω => f (swingLimitingSlope X r ω)) μ := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA := swingLimitingSlope_integrable hX hi hG r
  apply ((integrable_const |f 0|).add (hA.norm.const_mul (L : ℝ))).mono'
    (hf.continuous.measurable.comp (swingLimitingSlope_measurable hX r)).aestronglyMeasurable
  apply ae_of_all
  intro ω
  have hd := hf.dist_le_mul (swingLimitingSlope X r ω) 0
  simp only [Real.dist_eq, sub_zero] at hd
  have ht := abs_add_le (f (swingLimitingSlope X r ω)-f 0) (f 0)
  simp only [sub_add_cancel] at ht
  change |f (swingLimitingSlope X r ω)| ≤ |f 0| + (L : ℝ) * |swingLimitingSlope X r ω|
  linarith

/-- No moment premise remains for Lipschitz test functions: the original
Gaussian model supplies the first moment of the actual slope kernel. -/
theorem swingSlopeKernel_lipschitz_reward
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (fun r => ∫ a, f a ∂swingSlopeKernel X μ r) := by
  exact swingSlopeKernel_lipschitz_test hX hi hG hf
    (swingLimitingSlope_lipschitz_reward_integrable hX hi hG hf)

end SwingRepair
