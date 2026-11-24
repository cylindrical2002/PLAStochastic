import PLAStochastic.Swing.ConstantEvaluation.RewardLipschitz
import PLAStochastic.Swing.ConstantEvaluation.ContractionReduction
import PLAStochastic.Swing.ConstantEvaluation.RenewalPotentialMonotone
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.OvershootMeanIdentity

/-! # Theorem I.1 (`thm:constantcontraction`), assembled for the Gaussian input (roadmap 1.6)

All fluctuation-theory inputs of Appendix I are now theorems:

* `𝖡(a)` increases in stochastic order (`overshootStochasticMonotone_gaussian`);
* `β(c) - β(a) ≤ (3/4)(c - a)` (`overshootMeanLipschitz_gaussian`);
* `h = 𝖡v` is `L_h`-Lipschitz on `(0, ∞)` (`slopeReward_lipschitzOnWith`) and monotone
  (`slopeReward_monotoneOn`, from the monotone renewal potential).

This file instantiates the abstract contraction-and-evaluation theorem
(`SlopeEvaluationAbstract`) with `T = 𝖠𝖡`, `S = (0, ∞)`, `q = 3/4`, `L = L_h`:

* `slopeChain_contraction`: `W₁(T(a,·), T(c,·)) ≤ (3/4)|a - c|` in observable form
  (`eq:constantcontraction`);
* `slopeChain_orderReversing`: `T` reverses stochastic order;
* `slope_evaluation_bound`: `|(T^m h)(a₀) - γ_Swing| ≤ (3/4)^m L_h ∫ |b - a₀| dλ(b)` for every
  invariant margin law `ν` with a first moment and every `a₀ > 0`
  (`eq:constantevaluation` at `a₀`, with the explicit `λ`-moment in place of `M₀`);
* `slope_evaluation_bound_moment`: the same with `∫ |b - a₀| dλ ≤ ∫ b dλ + a₀`;
* `slope_iterates_bracket_monotone`: even iterates `T^{2m}h` are monotone and odd iterates
  antitone on `(0, ∞)` (the bracket structure);
* `slope_iterate_width`: `|(T^{m+1}h)(a₀) - (T^m h)(a₀)| ≤ (3/4)^m L_h ∫ |b - a₀| dT(a₀)(b)`.

What is *not* here: the continuous extension of `T, h` to the boundary slope `0`
(which the paper uses to evaluate at `q_m = (T^m h)(0)` and to obtain
`q_{2m} ↑ γ`, `q_{2m+1} ↓ γ`), and the numerical constant `M₀ = ρ_S + g_*`
(which needs the small-drift expansion of `𝔼M_a`).  Both are recorded as open in
the roadmap.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open Fluctuation LeadingCoefficient SlopeEvaluation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- **`eq:constantcontraction`**, observable form: `T = 𝖠𝖡` is a `W₁`-contraction on `(0, ∞)`
with rate `3/4`. -/
theorem slopeChain_contraction [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Contraction (swingSlopeChainKernel X μ) (Ioi 0) (3 / 4 : ℝ≥0) := by
  refine contraction_of_overshoot_inputs hX hi hG (overshootStochasticMonotone_gaussian hX hi hG) ?_
  have h := overshootMeanLipschitz_gaussian hX hi hG
  convert h using 2
  norm_num

/-- `T` reverses stochastic order on `(0, ∞)`. -/
theorem slopeChain_orderReversing [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    OrderReversing (swingSlopeChainKernel X μ) (Ioi 0) :=
  orderReversing_of_overshoot_monotone hX hi hG (overshootStochasticMonotone_gaussian hX hi hG)

/-- The Lipschitz constant `L_h` of the slope reward, for the library's linear bound on `v`. -/
def slopeRewardLipschitz : ℝ≥0 := slopeRewardLipschitzConst (gaussianExcessExpMomentBound 2)

/-- `h` is an `L_h`-Lipschitz test function on `(0, ∞)`. -/
theorem slopeReward_isTest [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsTest (Ioi 0) slopeRewardLipschitz (slopeReward X μ) :=
  ⟨slopeReward_measurable hX hi hG, slopeReward_lipschitzOnWith hX hi hG⟩

/-- **`h` is monotone on `(0, ∞)`**: `𝖡` increases in stochastic order and `v` is monotone. -/
theorem slopeReward_monotoneOn (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    MonotoneOn (slopeReward X μ) (Ioi 0) := by
  intro a ha c _ hac
  exact overshootStochasticMonotone_gaussian hX hi hG ha hac (marginLeadingReward X μ)
    (marginLeadingReward_measurable' hX hi hG) (marginLeadingReward_monotone hX hi hG)
    (marginLeadingReward_integrable_swingOvershootMeasure hX hi hG a)
    (marginLeadingReward_integrable_swingOvershootMeasure hX hi hG c)

/-- **Theorem I.1, evaluation bound (`eq:constantevaluation` at `a₀ > 0`).**
For every invariant probability `ν` of the margin kernel whose slope law
`λ = ν𝖠` has a first moment, and every `a₀ > 0`,
`|(T^m h)(a₀) - γ_Swing| ≤ (3/4)^m L_h ∫ |b - a₀| dλ(b)`. -/
theorem slope_evaluation_bound [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : Kernel.Invariant (swingMarginKernel X μ) ν)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ ν))
    {a₀ : ℝ} (ha₀ : 0 < a₀) (m : ℕ) :
    |(act (swingSlopeChainKernel X μ))^[m] (slopeReward X μ) a₀ -
        stationaryLeadingCoefficient X μ ν| ≤
      (3 / 4 : ℝ) ^ m * slopeRewardLipschitz * ∫ b, |b - a₀| ∂slopeStationaryLaw X μ ν := by
  have h := slope_evaluation_bound_of_contraction hX hi hG (slopeChain_contraction hX hi hG) hν hmom
    (slopeReward_lipschitzOnWith hX hi hG) ha₀ m
  convert h using 3
  · norm_num
  · rfl

/-- `λ` is carried by `(0, ∞)`, so `∫ |b - a₀| dλ ≤ ∫ b dλ + a₀`. -/
theorem slopeStationaryLaw_integral_abs_sub_le (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ ν)) {a₀ : ℝ} (ha₀ : 0 ≤ a₀) :
    (∫ b, |b - a₀| ∂slopeStationaryLaw X μ ν) ≤ (∫ b, b ∂slopeStationaryLaw X μ ν) + a₀ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hlam : IsProbabilityMeasure (slopeStationaryLaw X μ ν) := slopeStationaryLaw_isProbability hX ν
  have hsupp : slopeStationaryLaw X μ ν (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG ν
  have hle : (∫ b, |b - a₀| ∂slopeStationaryLaw X μ ν) ≤ ∫ b, (b + a₀) ∂slopeStationaryLaw X μ ν := by
    refine integral_mono_ae (hmom.sub (integrable_const _)).abs (hmom.add (integrable_const _)) ?_
    filter_upwards [ae_mem_of_compl_eq_zero hsupp] with b hb
    have hb' : 0 < b := hb
    rw [abs_le]
    constructor <;> linarith
  rwa [integral_add hmom (integrable_const _), integral_const, probReal_univ, one_smul] at hle

/-- **`eq:constantevaluation` with the explicit slope moment**:
`|(T^m h)(a₀) - γ_Swing| ≤ (3/4)^m L_h (∫ b dλ + a₀)`. -/
theorem slope_evaluation_bound_moment [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : Kernel.Invariant (swingMarginKernel X μ) ν)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ ν))
    {a₀ : ℝ} (ha₀ : 0 < a₀) (m : ℕ) :
    |(act (swingSlopeChainKernel X μ))^[m] (slopeReward X μ) a₀ -
        stationaryLeadingCoefficient X μ ν| ≤
      (3 / 4 : ℝ) ^ m * slopeRewardLipschitz * ((∫ b, b ∂slopeStationaryLaw X μ ν) + a₀) := by
  refine (slope_evaluation_bound hX hi hG hν hmom ha₀ m).trans ?_
  gcongr
  exact slopeStationaryLaw_integral_abs_sub_le hX hi hG hmom ha₀.le

/-- **The brackets, function form**: even iterates of `h` are monotone and odd iterates
antitone on `(0, ∞)`. -/
theorem slope_iterates_bracket_monotone [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (m : ℕ) :
    MonotoneOn ((act (swingSlopeChainKernel X μ))^[2 * m] (slopeReward X μ)) (Ioi 0) ∧
      AntitoneOn ((act (swingSlopeChainKernel X μ))^[2 * m + 1] (slopeReward X μ)) (Ioi 0) := by
  have hT : IsFiniteKernel (swingSlopeChainKernel X μ) := swingSlopeChainKernel_isFiniteKernel hX hi
  exact OrderReversing.iterate_even (slopeChain_contraction hX hi hG)
    (slopeChain_orderReversing hX hi hG) (slopeReward_isTest hX hi hG)
    (slopeReward_monotoneOn hX hi hG) m

/-- Two steps of `T` from `a₀` do not decrease `h`: `(T²h)(a₀) ≥ h(b)` whenever `b ≤ a₀`... in the
form `h(a₀) ≤ (T²h)(a₀)` requires `a₀ = min S`; on `(0, ∞)` we record the width of the
adjacent bracket instead:
`|(T^{m+1}h)(a₀) - (T^m h)(a₀)| ≤ (3/4)^m L_h ∫ |b - a₀| dT(a₀)(b)`. -/
theorem slope_iterate_width [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a₀ : ℝ} (ha₀ : 0 < a₀)
    (m : ℕ) :
    |(act (swingSlopeChainKernel X μ))^[m + 1] (slopeReward X μ) a₀ -
        (act (swingSlopeChainKernel X μ))^[m] (slopeReward X μ) a₀| ≤
      (3 / 4 : ℝ) ^ m * slopeRewardLipschitz * ∫ b, |b - a₀| ∂swingSlopeChainKernel X μ a₀ := by
  have hT : IsFiniteKernel (swingSlopeChainKernel X μ) := swingSlopeChainKernel_isFiniteKernel hX hi
  have hid : IsTest (Ioi 0) 1 (fun b : ℝ => b) :=
    ⟨measurable_id, (LipschitzWith.id (α := ℝ)).lipschitzOnWith (s := Ioi (0 : ℝ))⟩
  have hmomx : Integrable (fun b : ℝ => b) (swingSlopeChainKernel X μ a₀) :=
    swingSlopeChainKernel_integrable_test hX hi hG ha₀ hid
  have h := abs_iterate_succ_sub_iterate_le (slopeChain_contraction hX hi hG)
    (slopeReward_isTest hX hi hG) ha₀ hmomx m
  convert h using 3
  norm_num

end SwingRepair
