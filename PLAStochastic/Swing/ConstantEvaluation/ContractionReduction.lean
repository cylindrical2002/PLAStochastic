import PLAStochastic.Swing.ConstantEvaluation.SlopeKernelReduction
import PLAStochastic.Swing.Ladder.Renewal.ResidualLifeUniform
import Mathlib.MeasureTheory.Integral.Layercake

/-! # The slope-chain contraction from the overshoot-side inputs

Theorem I.1 obtains the `W₁`-contraction of `T = 𝖠 ∘ 𝖡` from two facts about
the reflected equilibrium overshoot law `𝖡(a) = Law(a - O_a)`:

* `𝖡(a)` increases in stochastic order with `a` (`OvershootStochasticMonotone`);
* its mean `β(a) = 𝔼_{𝖡(a)} R` is `q`-Lipschitz (`OvershootMeanLipschitz`,
  `q = 3/4` in the paper);

together with the already formalized order reversal and `1`-Lipschitz coupling
of the slope stage `𝖠`.  This file proves that implication and the companion
statement `OrderReversing T`.  It also proves unconditionally that `𝖡(a)` has a
first moment for `a > 0`, that the slope stage maps Lipschitz test functions on
`(0,∞)` to globally Lipschitz functions, and that stochastic order plus a mean
gap controls every Lipschitz observable (`abs_integral_sub_le_of_stochasticallyLE`,
the ordered-coupling inequality in observable form).

The two overshoot-side inputs themselves are the fluctuation-theory facts of
Appendix I (Spitzer/Baxter series for `p_a` and `𝔼M_a`, Sparre Andersen); they
remain hypotheses here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace SwingRepair
open LeadingCoefficient
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### Stochastic order in observable form -/

/-- `ν₁ ≤_st ν₂`: monotone integrable observables have ordered means. -/
def StochasticallyLE (ν₁ ν₂ : Measure ℝ) : Prop :=
  ∀ g : ℝ → ℝ, Measurable g → Monotone g → Integrable g ν₁ → Integrable g ν₂ →
    ∫ x, g x ∂ν₁ ≤ ∫ x, g x ∂ν₂

/-- **Ordered coupling, observable form.**  If `ν₁ ≤_st ν₂` and both have first
moments, every `L`-Lipschitz observable moves by at most `L` times the gap of
the means.  (For ordered laws the `W₁` distance *is* the mean gap; only the
upper bound is needed.) -/
theorem abs_integral_sub_le_of_stochasticallyLE {ν₁ ν₂ : Measure ℝ}
    (h : StochasticallyLE ν₁ ν₂)
    (h₁ : Integrable (fun x : ℝ => x) ν₁) (h₂ : Integrable (fun x : ℝ => x) ν₂)
    {L : ℝ≥0} {g : ℝ → ℝ} (hg : LipschitzWith L g) (hgm : Measurable g)
    (hg₁ : Integrable g ν₁) (hg₂ : Integrable g ν₂) :
    |(∫ x, g x ∂ν₂) - ∫ x, g x ∂ν₁| ≤ (L : ℝ) * ((∫ x, x ∂ν₂) - ∫ x, x ∂ν₁) := by
  have hmono₁ : Monotone fun x => g x + (L : ℝ) * x := by
    intro x y hxy
    have hd := hg.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith : x - y ≤ 0)] at hd
    have := le_abs_self (g x - g y)
    simp only
    linarith
  have hmono₂ : Monotone fun x => (L : ℝ) * x - g x := by
    intro x y hxy
    have hd := hg.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith : x - y ≤ 0)] at hd
    have := neg_abs_le (g x - g y)
    simp only
    linarith
  have hm₁ : Measurable fun x => g x + (L : ℝ) * x := hgm.add (measurable_id.const_mul _)
  have hm₂ : Measurable fun x => (L : ℝ) * x - g x := (measurable_id.const_mul _).sub hgm
  have hi₁ : ∫ x, (g x + (L : ℝ) * x) ∂ν₁ ≤ ∫ x, (g x + (L : ℝ) * x) ∂ν₂ :=
    h _ hm₁ hmono₁ (hg₁.add (h₁.const_mul _)) (hg₂.add (h₂.const_mul _))
  have hi₂ : ∫ x, ((L : ℝ) * x - g x) ∂ν₁ ≤ ∫ x, ((L : ℝ) * x - g x) ∂ν₂ :=
    h _ hm₂ hmono₂ ((h₁.const_mul _).sub hg₁) ((h₂.const_mul _).sub hg₂)
  rw [integral_add hg₁ (h₁.const_mul _), integral_add hg₂ (h₂.const_mul _),
    integral_const_mul, integral_const_mul] at hi₁
  rw [integral_sub (h₁.const_mul _) hg₁, integral_sub (h₂.const_mul _) hg₂,
    integral_const_mul, integral_const_mul] at hi₂
  rw [abs_le]
  constructor <;> linarith

/-! ### The overshoot-side inputs -/

/-- `β(a) = 𝔼_{𝖡(a)} R`, the mean of the reflected equilibrium overshoot. -/
def overshootMean (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  ∫ r, r ∂swingOvershootMeasure X μ a

/-- `𝖡(a)` increases in stochastic order with the drift. -/
def OvershootStochasticMonotone (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ⦃a c : ℝ⦄, 0 < a → a ≤ c →
    StochasticallyLE (swingOvershootMeasure X μ a) (swingOvershootMeasure X μ c)

/-- `β(c) - β(a) ≤ q (c - a)` for `0 < a ≤ c`. -/
def OvershootMeanLipschitz (X : ℕ → Ω → ℝ) (μ : Measure Ω) (q : ℝ) : Prop :=
  ∀ ⦃a c : ℝ⦄, 0 < a → a ≤ c → overshootMean X μ c - overshootMean X μ a ≤ q * (c - a)

/-! ### The first moment of `𝖡(a)` -/

/-- `∫⁻ o dO_a = 𝔼H_a² / (2𝔼H_a)` in `ℝ≥0∞`; only finiteness is used. -/
theorem lintegral_equilibriumOvershootLaw_id_lt_top
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    (∫⁻ o, ENNReal.ofReal o ∂equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)) < ⊤ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set ν := gaussianAscendingLadderLaw X μ a with hν
  have hνprob : IsProbabilityMeasure ν := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hmean0 : ladderMeanENN ν ≠ 0 := gaussianAscendingLadderLaw_mean_ne_zero hX hG ha le_rfl
  have hmeantop : ladderMeanENN ν ≠ ⊤ :=
    gaussianAscendingLadderLaw_mean_ne_top hX hi hG ha le_rfl le_rfl
  have hsq : Integrable (fun x : ℝ => x ^ 2) ν :=
    gaussianAscendingLadderLaw_sq_integrable hX hi hG ha le_rfl le_rfl
  have hdens : Measurable fun o : ℝ => ν (Ioi o) / ladderMeanENN ν :=
    (measurable_ladderTail ν).div_const _
  rw [equilibriumOvershootLaw, lintegral_withDensity_eq_lintegral_mul _ hdens
    ENNReal.measurable_ofReal]
  -- pass to `Ioi 0` and pull out the mean
  have hIci : (volume.restrict (Ici (0 : ℝ))) = volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  rw [hIci]
  have hrew : (fun o : ℝ => ν (Ioi o) / ladderMeanENN ν * ENNReal.ofReal o) =
      fun o : ℝ => (ladderMeanENN ν)⁻¹ * (ν {x : ℝ | o < x} * ENNReal.ofReal o) := by
    funext o
    rw [div_eq_mul_inv]
    have : Ioi o = {x : ℝ | o < x} := rfl
    rw [this]
    ring
  have hf : Measurable fun o : ℝ => ν {x : ℝ | o < x} * ENNReal.ofReal o :=
    (measurable_ladderTail ν).mul ENNReal.measurable_ofReal
  simp_rw [Pi.mul_apply]
  rw [show (fun o : ℝ => ν (Ioi o) / ladderMeanENN ν * ENNReal.ofReal o) =
      fun o : ℝ => (ladderMeanENN ν)⁻¹ * (ν {x : ℝ | o < x} * ENNReal.ofReal o) from hrew,
    lintegral_const_mul _ hf]
  -- layer cake with `g t = t`
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul ν (f := fun x : ℝ => x)
    (g := fun t : ℝ => t) (gaussianAscendingLadderLaw_nonneg_ae hX a)
    aemeasurable_id (fun t _ => continuous_id.intervalIntegrable 0 t)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => le_of_lt ht)
  rw [← hlayer]
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hmean0)) ?_
  have hint : (fun x : ℝ => ENNReal.ofReal (∫ t in (0 : ℝ)..x, t)) =
      fun x : ℝ => ENNReal.ofReal (x ^ 2 / 2) := by
    funext x
    rw [integral_id]
    simp
  rw [hint]
  have hsq' : Integrable (fun x : ℝ => x ^ 2 / 2) ν := hsq.div_const 2
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hsq'.hasFiniteIntegral

/-- `𝖡(a)` has a first moment for every positive drift. -/
theorem swingOvershootMeasure_integrable_id
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    Integrable (fun r : ℝ => r) (swingOvershootMeasure X μ a) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set O := equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a) with hO
  have hOprob : IsProbabilityMeasure O := gaussianAscendingLadderEquilibrium_isProbability hX hi hG ha
  have hOid : Integrable (fun o : ℝ => o) O := by
    have hnn : ∀ᵐ o ∂O, 0 ≤ o := by
      have h0 : O (Iio 0) = 0 := by
        rw [hO, equilibriumOvershootLaw_apply _ measurableSet_Iio]
        have : Iio (0 : ℝ) ∩ Ici 0 = ∅ := by
          ext x; simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_empty_iff_false, iff_false,
            not_and, not_le]; intro h; exact h
        rw [this, Measure.restrict_empty, lintegral_zero_measure]
      rw [ae_iff]
      convert h0 using 2
      ext o
      simp [not_le]
    refine ⟨aestronglyMeasurable_id, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lintegral_equilibriumOvershootLaw_id_lt_top hX hi hG ha
  rw [swingOvershootMeasure]
  refine (integrable_map_measure (g := fun r : ℝ => r) aestronglyMeasurable_id
    (measurable_const_sub_self a).aemeasurable).mpr ?_
  exact (integrable_const a).sub hOid

theorem swingOvershootMeasure_integrable_abs
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    Integrable (fun r : ℝ => |r|) (swingOvershootMeasure X μ a) :=
  (swingOvershootMeasure_integrable_id hX hi hG ha).abs

/-- A globally Lipschitz function is integrable against a finite measure with a
first moment. -/
theorem integrable_of_lipschitzWith_of_moment {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun r : ℝ => r) ν) {L : ℝ≥0} {g : ℝ → ℝ} (hg : LipschitzWith L g)
    (hgm : Measurable g) : Integrable g ν := by
  refine ((integrable_const |g 0|).add (hν.abs.const_mul (L : ℝ))).mono'
    hgm.aestronglyMeasurable ?_
  filter_upwards with r
  have hd := hg.dist_le_mul r 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at hd
  rw [Real.norm_eq_abs]
  calc |g r| = |(g r - g 0) + g 0| := by ring_nf
    _ ≤ |g r - g 0| + |g 0| := abs_add_le _ _
    _ ≤ (L : ℝ) * |r| + |g 0| := by linarith
    _ = |g 0| + (L : ℝ) * |r| := by ring

/-! ### The slope stage on test functions -/

/-- Test functions Lipschitz on `(0,∞)` are integrable against every `𝖠(r)`. -/
theorem swingSlopeKernel_integrable_test
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : SlopeEvaluation.IsTest (Ioi 0) L f) (r : ℝ) :
    Integrable f (swingSlopeKernel X μ r) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  have : IsProbabilityMeasure (swingSlopeKernel X μ r) := IsMarkovKernel.isProbabilityMeasure r
  refine SlopeEvaluation.IsTest.integrable_of_moment (S := Ioi 0) ?_
    (swingSlopeKernel_first_moment_integrable hX hi hG r) hf (a₀ := 1) (Set.mem_Ioi.mpr one_pos)
  rw [compl_Ioi]
  exact swingSlopeKernel_Iic_zero hX hi hG r

theorem swingSlopeKernel_integrable_test_comp
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : SlopeEvaluation.IsTest (Ioi 0) L f) (r : ℝ) :
    Integrable (fun ω => f (swingLimitingSlope X r ω)) μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have h := swingSlopeKernel_integrable_test hX hi hG hf r
  rw [swingSlopeKernel_eq_law hX r, swingLimitingSlopeLaw,
    integrable_map_measure hf.meas.aestronglyMeasurable
      (swingLimitingSlope_measurable hX r).aemeasurable] at h
  exact h

/-- The slope stage maps a test function Lipschitz on `(0,∞)` to a globally
`L`-Lipschitz function of the margin (common-path coupling). -/
theorem swingSlopeKernel_integral_lipschitz_test
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : SlopeEvaluation.IsTest (Ioi 0) L f) :
    LipschitzWith L (fun r => ∫ a, f a ∂swingSlopeKernel X μ r) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  apply LipschitzWith.of_dist_le_mul
  intro r c
  rw [swingSlopeKernel_integral hX r hf.meas, swingSlopeKernel_integral hX c hf.meas]
  have hr := swingSlopeKernel_integrable_test_comp hX hi hG hf r
  have hc := swingSlopeKernel_integrable_test_comp hX hi hG hf c
  rw [Real.dist_eq, Real.dist_eq, ← integral_sub hr hc]
  have hbound : ∀ᵐ ω ∂μ,
      |f (swingLimitingSlope X r ω) - f (swingLimitingSlope X c ω)| ≤ (L : ℝ) * |r - c| := by
    filter_upwards [swingLimitingSlope_regular_ae hX hi hG, swingLimitingSlope_pos_ae hX hi hG r,
      swingLimitingSlope_pos_ae hX hi hG c] with ω hω hr hc
    have hfirst := hf.lip.dist_le_mul _ (show swingLimitingSlope X r ω ∈ Ioi 0 from hr)
      _ (show swingLimitingSlope X c ω ∈ Ioi 0 from hc)
    have hsecond := hω.1.dist_le_mul r c
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hfirst hsecond
    exact hfirst.trans (mul_le_mul_of_nonneg_left hsecond L.coe_nonneg)
  calc |∫ ω, f (swingLimitingSlope X r ω) - f (swingLimitingSlope X c ω) ∂μ|
      ≤ ∫ ω, |f (swingLimitingSlope X r ω) - f (swingLimitingSlope X c ω)| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun ω => f (swingLimitingSlope X r ω) - f (swingLimitingSlope X c ω))
    _ ≤ ∫ _ω, (L : ℝ) * |r - c| ∂μ := integral_mono_ae (hr.sub hc).norm (integrable_const _) hbound
    _ = (L : ℝ) * |r - c| := by simp

/-- The slope stage reverses order: a test function monotone on `(0,∞)` gives an
antitone function of the margin. -/
theorem swingSlopeKernel_integral_antitone_test
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : SlopeEvaluation.IsTest (Ioi 0) L f)
    (hmono : MonotoneOn f (Ioi 0)) :
    Antitone (fun r => ∫ a, f a ∂swingSlopeKernel X μ r) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  intro r c hrc
  simp only
  rw [swingSlopeKernel_integral hX r hf.meas, swingSlopeKernel_integral hX c hf.meas]
  refine integral_mono_ae (swingSlopeKernel_integrable_test_comp hX hi hG hf c)
    (swingSlopeKernel_integrable_test_comp hX hi hG hf r) ?_
  filter_upwards [swingLimitingSlope_regular_ae hX hi hG, swingLimitingSlope_pos_ae hX hi hG r,
    swingLimitingSlope_pos_ae hX hi hG c] with ω hω hr hc
  exact hmono hc hr (hω.2 hrc)

/-- The bound `∫‖f‖ d𝖠(r) ≤ |f 1| + L (1 + |r| + 𝔼 env)` for a test function. -/
theorem swingSlopeKernel_integral_norm_test_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : SlopeEvaluation.IsTest (Ioi 0) L f) (r : ℝ) :
    (∫ a, ‖f a‖ ∂swingSlopeKernel X μ r) ≤
      |f 1| + (L : ℝ) * (1 + (|r| + ∫ ω, nativeGaussianEnvelope X ω ∂μ)) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  have : IsProbabilityMeasure (swingSlopeKernel X μ r) := IsMarkovKernel.isProbabilityMeasure r
  have hint := swingSlopeKernel_integrable_test hX hi hG hf r
  have habs := swingSlopeKernel_first_moment_integrable hX hi hG r
  have hL : Integrable (fun a : ℝ => (L : ℝ) * (1 + |a|)) (swingSlopeKernel X μ r) :=
    ((integrable_const (1 : ℝ)).add habs.abs).const_mul _
  have hLf : Integrable (fun a : ℝ => |f 1| + (L : ℝ) * (1 + |a|)) (swingSlopeKernel X μ r) :=
    (integrable_const _).add hL
  have h1 : (∫ a, ‖f a‖ ∂swingSlopeKernel X μ r) ≤
      ∫ a, (|f 1| + (L : ℝ) * (1 + |a|)) ∂swingSlopeKernel X μ r := by
    refine integral_mono_ae hint.norm hLf ?_
    filter_upwards [SlopeEvaluation.ae_mem_of_compl_eq_zero
      (S := Ioi 0) (lam := swingSlopeKernel X μ r)
      (by rw [compl_Ioi]; exact swingSlopeKernel_Iic_zero hX hi hG r)] with a ha
    have hd := hf.lip.dist_le_mul a ha 1 (Set.mem_Ioi.mpr one_pos)
    rw [Real.dist_eq, Real.dist_eq] at hd
    rw [Real.norm_eq_abs]
    have h2 : |a - 1| ≤ |a| + 1 := by
      calc |a - 1| ≤ |a| + |(1 : ℝ)| := abs_sub _ _
        _ = |a| + 1 := by simp
    calc |f a| = |(f a - f 1) + f 1| := by ring_nf
      _ ≤ |f a - f 1| + |f 1| := abs_add_le _ _
      _ ≤ (L : ℝ) * |a - 1| + |f 1| := by linarith
      _ ≤ (L : ℝ) * (1 + |a|) + |f 1| := by
          have := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
          linarith
      _ = |f 1| + (L : ℝ) * (1 + |a|) := by ring
  have h2 : (∫ a, (|f 1| + (L : ℝ) * (1 + |a|)) ∂swingSlopeKernel X μ r) =
      |f 1| + (L : ℝ) * (1 + ∫ a, |a| ∂swingSlopeKernel X μ r) := by
    rw [integral_add (integrable_const _) hL, integral_const, probReal_univ, one_smul,
      integral_const_mul, integral_add (integrable_const (1 : ℝ)) habs.abs, integral_const,
      probReal_univ, one_smul]
  have h3 := swingSlopeKernel_integral_abs_le hX hi hG r
  have h4 : (L : ℝ) * (1 + ∫ a, |a| ∂swingSlopeKernel X μ r) ≤
      (L : ℝ) * (1 + (|r| + ∫ ω, nativeGaussianEnvelope X ω ∂μ)) :=
    mul_le_mul_of_nonneg_left (by linarith) L.coe_nonneg
  linarith

/-! ### The slope chain on test functions -/

theorem swingSlopeChainKernel_integrable_test [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : SlopeEvaluation.IsTest (Ioi 0) L f) :
    Integrable f (swingSlopeChainKernel X μ a) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  have hB : IsProbabilityMeasure (swingOvershootMeasure X μ a) :=
    swingOvershootMeasure_isProbability hX hi hG ha
  rw [swingSlopeChainKernel_apply hX a]
  rw [Measure.integrable_comp_iff hf.meas.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun r => swingSlopeKernel_integrable_test hX hi hG hf r, ?_⟩
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ => ‖f p.2‖) :=
    ((hf.meas.comp measurable_snd).norm).stronglyMeasurable
  have hmeas : Measurable fun r => ∫ b, ‖f b‖ ∂swingSlopeKernel X μ r :=
    (hsm.integral_kernel_prod_right' (κ := swingSlopeKernel X μ)).measurable
  refine ((integrable_const (|f 1| + (L : ℝ) * (1 + ∫ ω, nativeGaussianEnvelope X ω ∂μ))).add
    ((swingOvershootMeasure_integrable_abs hX hi hG ha).const_mul (L : ℝ))).mono'
    hmeas.aestronglyMeasurable ?_
  filter_upwards with r
  have h0 : 0 ≤ ∫ b, ‖f b‖ ∂swingSlopeKernel X μ r := integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have := swingSlopeKernel_integral_norm_test_le hX hi hG hf r
  show _ ≤ (|f 1| + (L : ℝ) * (1 + ∫ ω, nativeGaussianEnvelope X ω ∂μ)) + (L : ℝ) * |r|
  linarith

/-- `Tf(a) = ∫ (𝖠f)(r) 𝖡(a,dr)` for integrable `f`. -/
theorem swingSlopeChainKernel_integral_eq [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) {a : ℝ}
    {f : ℝ → ℝ} (hint : Integrable f (swingSlopeChainKernel X μ a)) :
    (∫ b, f b ∂swingSlopeChainKernel X μ a) =
      ∫ r, (∫ b, f b ∂swingSlopeKernel X μ r) ∂swingOvershootMeasure X μ a := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  have hBfin : IsFiniteMeasure (swingOvershootMeasure X μ a) :=
    ⟨lt_of_le_of_lt (swingOvershootMeasure_univ_le_one hX hi a) ENNReal.one_lt_top⟩
  rw [swingSlopeChainKernel_apply hX a] at hint ⊢
  rw [Measure.comp_eq_comp_const_apply] at hint ⊢
  rw [Kernel.integral_comp hint]
  simp only [Kernel.const_apply]

/-- **Contraction of the slope chain from the overshoot-side inputs.** -/
theorem contraction_of_overshoot_inputs [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {q : ℝ≥0}
    (hmono : OvershootStochasticMonotone X μ) (hlip : OvershootMeanLipschitz X μ q) :
    SlopeEvaluation.Contraction (swingSlopeChainKernel X μ) (Ioi 0) q where
  prob a ha := swingSlopeChainKernel_isProbability hX hi hG ha
  supp a _ := by
    rw [compl_Ioi]
    exact swingSlopeChainKernel_Iic_zero hX hi hG a
  integrable L f hf a ha := swingSlopeChainKernel_integrable_test hX hi hG ha hf
  lip L f hf := by
    have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
    have hA := swingSlopeKernel_isMarkov (μ := μ) hX
    set g : ℝ → ℝ := fun r => ∫ b, f b ∂swingSlopeKernel X μ r with hgdef
    have hg : LipschitzWith L g := swingSlopeKernel_integral_lipschitz_test hX hi hG hf
    have hgm : Measurable g := SlopeEvaluation.act_measurable (T := swingSlopeKernel X μ) hf.meas
    -- the key estimate for `a ≤ c`
    have key : ∀ {a c : ℝ}, 0 < a → a ≤ c →
        |SlopeEvaluation.act (swingSlopeChainKernel X μ) f c -
          SlopeEvaluation.act (swingSlopeChainKernel X μ) f a| ≤ (q : ℝ) * L * (c - a) := by
      intro a c ha hac
      have hc : 0 < c := lt_of_lt_of_le ha hac
      have hBa : IsProbabilityMeasure (swingOvershootMeasure X μ a) :=
        swingOvershootMeasure_isProbability hX hi hG ha
      have hBc : IsProbabilityMeasure (swingOvershootMeasure X μ c) :=
        swingOvershootMeasure_isProbability hX hi hG hc
      have hma := swingOvershootMeasure_integrable_id hX hi hG ha
      have hmc := swingOvershootMeasure_integrable_id hX hi hG hc
      unfold SlopeEvaluation.act
      rw [swingSlopeChainKernel_integral_eq hX hi (swingSlopeChainKernel_integrable_test hX hi hG hc hf),
        swingSlopeChainKernel_integral_eq hX hi (swingSlopeChainKernel_integrable_test hX hi hG ha hf)]
      have hbound := abs_integral_sub_le_of_stochasticallyLE (hmono ha hac) hma hmc hg hgm
        (integrable_of_lipschitzWith_of_moment hma hg hgm)
        (integrable_of_lipschitzWith_of_moment hmc hg hgm)
      have hβ := hlip ha hac
      unfold overshootMean at hβ
      calc |(∫ r, g r ∂swingOvershootMeasure X μ c) - ∫ r, g r ∂swingOvershootMeasure X μ a|
          ≤ (L : ℝ) * ((∫ r, r ∂swingOvershootMeasure X μ c) -
              ∫ r, r ∂swingOvershootMeasure X μ a) := hbound
        _ ≤ (L : ℝ) * ((q : ℝ) * (c - a)) := mul_le_mul_of_nonneg_left hβ L.coe_nonneg
        _ = (q : ℝ) * L * (c - a) := by ring
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha c hc
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mul]
    rcases le_total a c with hac | hca
    · have := key ha hac
      rw [abs_sub_comm, abs_of_nonpos (by linarith : a - c ≤ 0)]
      linarith
    · have := key hc hca
      rw [abs_of_nonneg (by linarith : 0 ≤ a - c)]
      linarith

/-- **Order reversal of the slope chain from the overshoot-side monotonicity.** -/
theorem orderReversing_of_overshoot_monotone [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hmono : OvershootStochasticMonotone X μ) :
    SlopeEvaluation.OrderReversing (swingSlopeChainKernel X μ) (Ioi 0) where
  anti L f hf hfmono := by
    have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
    have hA := swingSlopeKernel_isMarkov (μ := μ) hX
    set g : ℝ → ℝ := fun r => ∫ b, f b ∂swingSlopeKernel X μ r with hgdef
    have hg : LipschitzWith L g := swingSlopeKernel_integral_lipschitz_test hX hi hG hf
    have hgm : Measurable g := SlopeEvaluation.act_measurable (T := swingSlopeKernel X μ) hf.meas
    have hganti : Antitone g := swingSlopeKernel_integral_antitone_test hX hi hG hf hfmono
    intro a ha c hc hac
    have hBa : IsProbabilityMeasure (swingOvershootMeasure X μ a) :=
      swingOvershootMeasure_isProbability hX hi hG ha
    have hBc : IsProbabilityMeasure (swingOvershootMeasure X μ c) :=
      swingOvershootMeasure_isProbability hX hi hG hc
    have hma := swingOvershootMeasure_integrable_id hX hi hG ha
    have hmc := swingOvershootMeasure_integrable_id hX hi hG hc
    have hga := integrable_of_lipschitzWith_of_moment hma hg hgm
    have hgc := integrable_of_lipschitzWith_of_moment hmc hg hgm
    show SlopeEvaluation.act (swingSlopeChainKernel X μ) f c ≤
      SlopeEvaluation.act (swingSlopeChainKernel X μ) f a
    unfold SlopeEvaluation.act
    rw [swingSlopeChainKernel_integral_eq hX hi (swingSlopeChainKernel_integrable_test hX hi hG hc hf),
      swingSlopeChainKernel_integral_eq hX hi (swingSlopeChainKernel_integrable_test hX hi hG ha hf)]
    have := hmono ha hac (fun r => -g r) hgm.neg (fun x y hxy => by
      simp only [neg_le_neg_iff]; exact hganti hxy) hga.neg hgc.neg
    rw [integral_neg, integral_neg] at this
    linarith

end SwingRepair
