import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.ExplicitGamma
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.ConcreteBounds
import PLAStochastic.Swing.StationaryLimit.MarginKernel.WeakFeller
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.ContractionEvaluation

/-! # Reduction of `γ_Swing` to the positive-slope kernel

Appendix I (`sec:newconstant`) factors the limiting margin kernel
`K = 𝖡 ∘ 𝖠` (margin → slope → margin) and studies the slope chain
`T = 𝖠 ∘ 𝖡` (slope → margin → slope), the stationary slope law `λ = ν_∞𝖠`
and the slope reward `h = 𝖡v`, `v(r) = 4V(r)𝟙_{r>0}`.  This file proves the
reduction identities of that appendix (`eq:newconstantslopereward` and
`λT = λ`) directly from the kernel algebra:

* `T(a)` is a probability measure for `a > 0`, carried by `(0, ∞)`;
* `λ` is a probability measure carried by `(0, ∞)` and `λT = λ` whenever
  `νK = ν`;
* `γ(ν) = ∫ v dν = ∫ h dλ` (Tonelli, entirely in `ℝ≥0∞`).

The contraction of `T` and the Lipschitz bound of `h` (the fluctuation-theory
half of Theorem I.1) are **not** proved here; `slope_evaluation_bound_of_contraction`
records exactly what they would deliver through `SlopeEvaluationAbstract`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace SwingRepair
open LeadingCoefficient
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `T = 𝖠 ∘ 𝖡`: the slope-to-slope kernel of Appendix I. -/
def swingSlopeChainKernel (X : ℕ → Ω → ℝ) (μ : Measure Ω) [SFinite μ] : Kernel ℝ ℝ :=
  swingSlopeKernel X μ ∘ₖ swingOvershootKernel X μ

/-- `λ = ν𝖠`: the slope law induced by a margin law. -/
def slopeStationaryLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (ν : Measure ℝ) : Measure ℝ :=
  swingSlopeKernel X μ ∘ₘ ν

/-- `h = 𝖡v`: the conditional reward at a given slope, `eq:newconstantslopereward`. -/
def slopeReward (X : ℕ → Ω → ℝ) (μ : Measure Ω) : ℝ → ℝ :=
  swingOvershootReward X μ (marginLeadingReward X μ)

/-! ### The slope chain -/

theorem swingSlopeChainKernel_apply [SFinite μ] (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    swingSlopeChainKernel X μ a = swingSlopeKernel X μ ∘ₘ swingOvershootMeasure X μ a := by
  rw [swingSlopeChainKernel, Kernel.comp_apply, swingOvershootKernel_apply hX a]

theorem swingSlopeChainKernel_isProbability [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (swingSlopeChainKernel X μ a) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hB := swingOvershootMeasure_isProbability hX hi hG ha
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  refine ⟨?_⟩
  rw [swingSlopeChainKernel_apply hX a, Measure.comp_apply_univ]
  exact measure_univ

theorem swingSlopeKernel_Iic_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    swingSlopeKernel X μ r (Iic 0) = 0 := by
  have h := swingSlopeKernel_positive_ae hX hi hG r
  rw [ae_iff] at h
  convert h using 2
  ext a
  simp [not_lt]

theorem swingSlopeChainKernel_Iic_zero [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) :
    swingSlopeChainKernel X μ a (Iic 0) = 0 := by
  rw [swingSlopeChainKernel_apply hX a, Measure.bind_apply measurableSet_Iic (Kernel.aemeasurable _)]
  simp [swingSlopeKernel_Iic_zero hX hi hG]

theorem swingSlopeChainKernel_isFiniteKernel [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) :
    IsFiniteKernel (swingSlopeChainKernel X μ) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hB := swingOvershootKernel_isFinite hX hi
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  exact Kernel.IsFiniteKernel.comp _ _

/-! ### The stationary slope law -/

theorem slopeStationaryLaw_isProbability [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (slopeStationaryLaw X μ ν) := by
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  refine ⟨?_⟩
  rw [slopeStationaryLaw, Measure.comp_apply_univ]
  exact measure_univ

theorem slopeStationaryLaw_Iic_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (ν : Measure ℝ) :
    slopeStationaryLaw X μ ν (Iic 0) = 0 := by
  rw [slopeStationaryLaw, Measure.bind_apply measurableSet_Iic (Kernel.aemeasurable _)]
  simp [swingSlopeKernel_Iic_zero hX hi hG]

/-- The first absolute moment of the slope kernel is at most `|r|` plus the
mean Gaussian envelope. -/
theorem swingSlopeKernel_integral_abs_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    (∫ a, |a| ∂swingSlopeKernel X μ r) ≤ |r| + ∫ ω, nativeGaussianEnvelope X ω ∂μ := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [swingSlopeKernel_integral hX r (measurable_id.abs (f := fun a : ℝ => a))]
  have henv : Integrable (nativeGaussianEnvelope X) μ := by
    simpa only [pow_one] using nativeGaussianEnvelope_integrable_pow hX hi hG 1
  have hle : (∫ ω, |swingLimitingSlope X r ω| ∂μ) ≤ ∫ ω, (|r| + nativeGaussianEnvelope X ω) ∂μ := by
    refine integral_mono_ae (swingLimitingSlope_integrable hX hi hG r).abs
      ((integrable_const _).add henv) ?_
    filter_upwards [nativeGaussianEnvelope_bounds_ae hX hi hG,
      swingLimitingSlope_pos_ae hX hi hG r] with ω hW hpos
    rw [abs_of_pos hpos]
    exact swingLimitingSlope_le_envelope r ω hW
  rw [integral_add (integrable_const _) henv, integral_const, probReal_univ, one_smul] at hle
  exact hle

/-- `λ` has a first moment whenever `ν` has one. -/
theorem slopeStationaryLaw_first_moment_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν) :
    Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ ν) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  rw [slopeStationaryLaw]
  have hmeas : AEStronglyMeasurable (fun b : ℝ => b) (swingSlopeKernel X μ ∘ₘ ν) :=
    aestronglyMeasurable_id
  rw [Measure.integrable_comp_iff hmeas]
  refine ⟨ae_of_all _ fun r => swingSlopeKernel_first_moment_integrable hX hi hG r, ?_⟩
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ => ‖p.2‖) :=
    (measurable_snd.norm).stronglyMeasurable
  have hmeas' : Measurable fun r => ∫ a, ‖a‖ ∂swingSlopeKernel X μ r :=
    (hsm.integral_kernel_prod_right' (κ := swingSlopeKernel X μ)).measurable
  refine ((integrable_const (∫ ω, nativeGaussianEnvelope X ω ∂μ)).add hνabs).mono'
    hmeas'.aestronglyMeasurable ?_
  filter_upwards with r
  have h0 : 0 ≤ ∫ a, ‖a‖ ∂swingSlopeKernel X μ r := integral_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have := swingSlopeKernel_integral_abs_le hX hi hG r
  have heq : (∫ a, ‖a‖ ∂swingSlopeKernel X μ r) = ∫ a, |a| ∂swingSlopeKernel X μ r := by
    congr 1
  rw [heq]
  show _ ≤ (∫ ω, nativeGaussianEnvelope X ω ∂μ) + |r|
  linarith

/-- `λT = λ` follows from `νK = ν` by associativity: `T ∘ 𝖠 = 𝖠 ∘ K`. -/
theorem slopeStationaryLaw_invariant [SFinite μ] {ν : Measure ℝ}
    (hν : Kernel.Invariant (swingMarginKernel X μ) ν) :
    swingSlopeChainKernel X μ ∘ₘ slopeStationaryLaw X μ ν = slopeStationaryLaw X μ ν := by
  rw [slopeStationaryLaw, Measure.comp_assoc, swingSlopeChainKernel, Kernel.comp_assoc,
    ← swingMarginKernel, ← Measure.comp_assoc, hν.def]

/-! ### The slope reward -/

theorem marginLeadingReward_measurable'
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Measurable (marginLeadingReward X μ) :=
  marginLeadingReward_measurable_actual hX hi hG

theorem slopeReward_measurable [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Measurable (slopeReward X μ) :=
  swingOvershootReward_measurable hX hi (marginLeadingReward_measurable' hX hi hG)

/-- The reflected equilibrium overshoot never exceeds the drift. -/
theorem swingOvershootMeasure_Ioi_self (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) :
    swingOvershootMeasure X μ a (Ioi a) = 0 := by
  rw [swingOvershootMeasure_apply X μ a measurableSet_Ioi]
  have hempty : ((fun o : ℝ => a - o) ⁻¹' Ioi a) ∩ Ici (0 : ℝ) = ∅ := by
    ext o
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_Ici, mem_empty_iff_false, iff_false,
      not_and, not_le]
    intro h
    linarith
  rw [hempty, Measure.restrict_empty, lintegral_zero_measure]

/-- The reward `v` is bounded by `4(max a 0 + C₂)` almost everywhere under `𝖡(a)`. -/
theorem marginLeadingReward_ae_le_swingOvershootMeasure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) :
    ∀ᵐ r ∂swingOvershootMeasure X μ a,
      marginLeadingReward X μ r ≤ 4 * (max a 0 + gaussianExcessExpMomentBound 2) := by
  have h0 : ∀ᵐ r ∂swingOvershootMeasure X μ a, r ≤ a := by
    rw [ae_iff]
    convert swingOvershootMeasure_Ioi_self X μ a using 2
    ext r
    simp [not_le]
  filter_upwards [h0] with r hr
  refine (marginLeadingReward_le_linear hX hi hG).trans ?_
  have : max r 0 ≤ max a 0 := max_le_max hr le_rfl
  linarith

theorem marginLeadingReward_integrable_swingOvershootMeasure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) :
    Integrable (marginLeadingReward X μ) (swingOvershootMeasure X μ a) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hfin : IsFiniteMeasure (swingOvershootMeasure X μ a) :=
    ⟨lt_of_le_of_lt (swingOvershootMeasure_univ_le_one hX hi a) ENNReal.one_lt_top⟩
  refine (integrable_const (4 * (max a 0 + gaussianExcessExpMomentBound 2))).mono'
    (marginLeadingReward_measurable' hX hi hG).aestronglyMeasurable ?_
  filter_upwards [marginLeadingReward_ae_le_swingOvershootMeasure hX hi hG a] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (marginLeadingReward_nonneg hX hi hG)]
  exact hr

theorem slopeReward_nonneg
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) :
    0 ≤ slopeReward X μ a :=
  integral_nonneg fun _ => marginLeadingReward_nonneg hX hi hG

/-- `h(a)` as an `ℝ≥0∞`-integral. -/
theorem ofReal_slopeReward
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) :
    ENNReal.ofReal (slopeReward X μ a) =
      ∫⁻ r, ENNReal.ofReal (marginLeadingReward X μ r) ∂swingOvershootMeasure X μ a :=
  ofReal_integral_eq_lintegral_ofReal
    (marginLeadingReward_integrable_swingOvershootMeasure hX hi hG a)
    (ae_of_all _ fun _ => marginLeadingReward_nonneg hX hi hG)

/-! ### `γ = ∫ h dλ` -/

/-- **`eq:newconstantslopereward`.**  For an invariant probability `ν` of the
margin kernel, `γ(ν) = ∫ v dν = ∫ h dλ` with `λ = ν𝖠`. -/
theorem stationaryLeadingCoefficient_eq_slopeReward_integral [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} (hν : Kernel.Invariant (swingMarginKernel X μ) ν) :
    stationaryLeadingCoefficient X μ ν =
      ∫ a, slopeReward X μ a ∂slopeStationaryLaw X μ ν := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set v := marginLeadingReward X μ with hvdef
  have hvmeas : Measurable v := marginLeadingReward_measurable' hX hi hG
  have hvnn : ∀ r, 0 ≤ v r := fun r => marginLeadingReward_nonneg hX hi hG
  have hhmeas : Measurable (slopeReward X μ) := slopeReward_measurable hX hi hG
  have hhnn : ∀ a, 0 ≤ slopeReward X μ a := slopeReward_nonneg hX hi hG
  -- both sides as `toReal` of `ℝ≥0∞`-integrals
  have hL : stationaryLeadingCoefficient X μ ν = (∫⁻ r, ENNReal.ofReal (v r) ∂ν).toReal := by
    rw [stationaryLeadingCoefficient]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hvnn) hvmeas.aestronglyMeasurable
  have hR : (∫ a, slopeReward X μ a ∂slopeStationaryLaw X μ ν) =
      (∫⁻ a, ENNReal.ofReal (slopeReward X μ a) ∂slopeStationaryLaw X μ ν).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hhnn) hhmeas.aestronglyMeasurable
  rw [hL, hR]
  congr 1
  -- the inner reward as a kernel integral
  have hinner : (fun a => ENNReal.ofReal (slopeReward X μ a)) =
      fun a => ∫⁻ r, ENNReal.ofReal (v r) ∂swingOvershootKernel X μ a := by
    funext a
    rw [ofReal_slopeReward hX hi hG a, swingOvershootKernel_apply hX a]
  have hg : Measurable fun x => ENNReal.ofReal (v x) := hvmeas.ennreal_ofReal
  have hinner_meas : Measurable fun a => ∫⁻ r, ENNReal.ofReal (v r) ∂swingOvershootKernel X μ a :=
    hg.lintegral_kernel
  rw [hinner, slopeStationaryLaw,
    Measure.lintegral_bind (Kernel.aemeasurable _) hinner_meas.aemeasurable]
  -- fold `∫_𝖠 ∫_𝖡 = ∫_K`
  have hK : ∀ r, (∫⁻ a, ∫⁻ x, ENNReal.ofReal (v x) ∂swingOvershootKernel X μ a
      ∂swingSlopeKernel X μ r) = ∫⁻ x, ENNReal.ofReal (v x) ∂swingMarginKernel X μ r := by
    intro r
    rw [swingMarginKernel, Kernel.lintegral_comp _ _ _ hg]
  simp_rw [hK]
  rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]
  rw [hν.def]

/-! ### The conditional evaluation bound -/

/-- **Theorem I.1, evaluation bound, conditional form.**  If the slope chain
`T` is an observable `W₁`-contraction on `(0,∞)` with rate `q` and the slope
reward `h` is `L`-Lipschitz there, then for every invariant probability `ν` of
`K` with a first moment on the slope side and every starting slope `a₀ > 0`,
`|(T^m h)(a₀) - γ| ≤ q^m L ∫ |b - a₀| dλ(b)`.  With `q = 3/4`, `L = L_h`
and `∫ b dλ ≤ M₀` this is `eq:constantevaluation` at `a₀`; the contraction and
the Lipschitz constant are the unproved fluctuation-theory inputs. -/
theorem slope_evaluation_bound_of_contraction [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {q : ℝ≥0} (hcon : SlopeEvaluation.Contraction (swingSlopeChainKernel X μ) (Ioi 0) q)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (swingMarginKernel X μ) ν)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ ν))
    {L : ℝ≥0} (hL : LipschitzOnWith L (slopeReward X μ) (Ioi 0))
    {a₀ : ℝ} (ha₀ : 0 < a₀) (m : ℕ) :
    |(SlopeEvaluation.act (swingSlopeChainKernel X μ))^[m] (slopeReward X μ) a₀ -
        stationaryLeadingCoefficient X μ ν| ≤
      (q : ℝ) ^ m * L * ∫ b, |b - a₀| ∂slopeStationaryLaw X μ ν := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hT : IsFiniteKernel (swingSlopeChainKernel X μ) := swingSlopeChainKernel_isFiniteKernel hX hi
  have hlam : IsProbabilityMeasure (slopeStationaryLaw X μ ν) :=
    slopeStationaryLaw_isProbability hX ν
  have hsupp : slopeStationaryLaw X μ ν (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]
    exact slopeStationaryLaw_Iic_zero hX hi hG ν
  rw [stationaryLeadingCoefficient_eq_slopeReward_integral hX hi hG hν]
  exact SlopeEvaluation.abs_iterate_sub_integral_le hcon (slopeStationaryLaw_invariant hν) hsupp
    hmom ⟨slopeReward_measurable hX hi hG, hL⟩ ha₀ m

end SwingRepair
