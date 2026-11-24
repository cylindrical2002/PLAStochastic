import PLAStochastic.Swing.ConstantEvaluation.GaussianEvaluation
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.WeakPropagation
import PLAStochastic.Swing.StationaryLimit.MarginKernel.InvariantExistence

/-! # The slope algebra of the transient coefficients

`eq:transient-slopecoefficient` and the two estimates that follow it in the proof
of Theorem 4.4.  For an arbitrary entrance law `ρ` (a subsequential limit of the
first-restart margin laws), the transient coefficient after `m+1` transitions of
the margin kernel is

`∫ v d(ρ K^{m+1}) = ∫ (T^m h) dᾱ,   ᾱ = ρ𝖠`,

because `K = 𝖡𝖠`, `T = 𝖠𝖡` and `h = 𝖡v`.  Two consequences:

* **the geometric bound**: the `W₁`-contraction of `T` on `(0,∞)` and the
  Lipschitz bound of `h` give
  `|∫ v d(ρK^{m+1}) - γ| ≤ (3/4)^m L_h (∫ b dλ + ∫ a dᾱ)`, and the slope moment
  `∫ a dᾱ ≤ ∫ |r| dρ + E G` is controlled by the first moment of `ρ`;
* **the positive lower bound**: one transition of `K` charges every interval,
  so `K^{m+1}ψ > 0` everywhere for a bump `ψ` under `v/4`; `K^{m+1}ψ` is
  continuous and therefore bounded below on `[-M, M]`, which carries at least
  half the mass of every `ρ` with `∫ |r| dρ ≤ M₁` when `M = 2M₁ + 1`.

The abstract part is stated for an arbitrary contraction in the sense of
`SlopeEvaluationAbstract`; the concrete part specialises to Swing.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SlopeEvaluation

variable {T : Kernel ℝ ℝ} {S : Set ℝ} {q : ℝ≥0}

theorem act_nonneg {f : ℝ → ℝ} (hf : ∀ b, 0 ≤ f b) (a : ℝ) : 0 ≤ act T f a :=
  integral_nonneg hf

theorem iterate_act_nonneg {f : ℝ → ℝ} (hf : ∀ b, 0 ≤ f b) (m : ℕ) :
    ∀ a, 0 ≤ (act T)^[m] f a := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
    intro a
    rw [Function.iterate_succ_apply']
    exact act_nonneg ih a

/-- A transition of `T` preserves concentration on `S`. -/
theorem comp_compl_eq_zero [IsSFiniteKernel T] (h : Contraction T S q) (hS : MeasurableSet S)
    {σ : Measure ℝ} (hσ : σ Sᶜ = 0) : (T ∘ₘ σ) Sᶜ = 0 := by
  rw [Measure.bind_apply hS.compl (Kernel.aemeasurable _)]
  have hae : (fun a => T a Sᶜ) =ᵐ[σ] fun _ => (0 : ℝ≥0∞) := by
    filter_upwards [ae_mem_of_compl_eq_zero hσ] with a ha
    exact h.supp a ha
  rw [lintegral_congr_ae hae, lintegral_zero]

/-- `∫ f d(T^m σ) = ∫ (T^m f) dσ` for a nonnegative test function, in `ℝ≥0∞`. -/
theorem lintegral_iterate_comp [IsSFiniteKernel T] (h : Contraction T S q) (hS : MeasurableSet S)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f) (hf0 : ∀ b, 0 ≤ f b) (m : ℕ) :
    ∀ σ : Measure ℝ, σ Sᶜ = 0 →
      ∫⁻ b, ENNReal.ofReal (f b) ∂((fun ν : Measure ℝ => T ∘ₘ ν)^[m] σ) =
        ∫⁻ a, ENNReal.ofReal ((act T)^[m] f a) ∂σ := by
  induction m with
  | zero => intro σ _; rfl
  | succ m ih =>
    intro σ hσ
    rw [Function.iterate_succ_apply, ih (T ∘ₘ σ) (comp_compl_eq_zero h hS hσ),
      Function.iterate_succ_apply']
    have hg : IsTest S (q ^ m * L) ((act T)^[m] f) := hf.iterate h m
    have hgmeas : Measurable fun a => ENNReal.ofReal ((act T)^[m] f a) := hg.meas.ennreal_ofReal
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) hgmeas.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_mem_of_compl_eq_zero hσ] with a ha
    rw [act, ofReal_integral_eq_lintegral_ofReal (h.integrable _ _ hg a ha)
      (ae_of_all _ (iterate_act_nonneg hf0 m))]

/-- **The geometric bound for an arbitrary entrance law.**  If `λ` is an invariant
probability concentrated on `S` with a first moment and `α` is any probability
concentrated on `S` with a first moment, then
`|∫ (T^m f) dα - ∫ f dλ| ≤ q^m L (∫ |b| dλ + ∫ |a| dα)`. -/
theorem abs_integral_iterate_sub_integral_le [IsSFiniteKernel T] (h : Contraction T S q)
    {lam : Measure ℝ} [IsProbabilityMeasure lam] (hlam : T ∘ₘ lam = lam) (hsupp : lam Sᶜ = 0)
    (hmom : Integrable (fun b : ℝ => b) lam)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαsupp : α Sᶜ = 0)
    (hαmom : Integrable (fun a : ℝ => a) α)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f) (m : ℕ) :
    |(∫ a, (act T)^[m] f a ∂α) - ∫ b, f b ∂lam| ≤
      (q : ℝ) ^ m * L * ((∫ b, |b| ∂lam) + ∫ a, |a| ∂α) := by
  obtain ⟨a₀, ha₀⟩ := (ae_mem_of_compl_eq_zero hαsupp).exists
  set g := (act T)^[m] f with hg
  have hgtest : IsTest S (q ^ m * L) g := hf.iterate h m
  have hgint : Integrable g α := hgtest.integrable_of_moment hαsupp hαmom ha₀
  have hlamabs : Integrable (fun b : ℝ => |b|) lam := hmom.abs
  have hαabs : Integrable (fun a : ℝ => |a|) α := hαmom.abs
  set c := ∫ b, f b ∂lam with hc
  have hq : 0 ≤ (q : ℝ) ^ m * L := by positivity
  have hpt : ∀ a ∈ S, |g a - c| ≤ (q : ℝ) ^ m * L * ((∫ b, |b| ∂lam) + |a|) := by
    intro a ha
    refine (abs_iterate_sub_integral_le h hlam hsupp hmom hf ha m).trans ?_
    apply mul_le_mul_of_nonneg_left _ hq
    calc (∫ b, |b - a| ∂lam) ≤ ∫ b, (|b| + |a|) ∂lam :=
          integral_mono (hmom.sub (integrable_const a)).abs (hlamabs.add (integrable_const _))
            (fun b => abs_sub b a)
      _ = (∫ b, |b| ∂lam) + |a| := by
          rw [integral_add hlamabs (integrable_const _), integral_const, probReal_univ, one_smul]
  have h1 : (∫ a, g a ∂α) - c = ∫ a, (g a - c) ∂α := by
    rw [integral_sub hgint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [h1]
  calc |∫ a, (g a - c) ∂α| ≤ ∫ a, |g a - c| ∂α := abs_integral_le_integral_abs
    _ ≤ ∫ a, (q : ℝ) ^ m * L * ((∫ b, |b| ∂lam) + |a|) ∂α := by
        refine integral_mono_ae (hgint.sub (integrable_const _)).abs
          (((integrable_const _).add hαabs).const_mul _) ?_
        filter_upwards [ae_mem_of_compl_eq_zero hαsupp] with a ha
        exact hpt a ha
    _ = (q : ℝ) ^ m * L * ((∫ b, |b| ∂lam) + ∫ a, |a| ∂α) := by
        rw [integral_const_mul, integral_add (integrable_const _) hαabs, integral_const,
          probReal_univ, one_smul]

end SlopeEvaluation

open SlopeEvaluation LeadingCoefficient KernelLimit

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### `ρ K^{m+1} = (ρ𝖠 T^m) 𝖡` -/

theorem swingMarginKernel_iterate_comp_eq [SFinite μ] (ρ : Measure ℝ) (m : ℕ) :
    (fun ν : Measure ℝ => swingMarginKernel X μ ∘ₘ ν)^[m+1] ρ =
      swingOvershootKernel X μ ∘ₘ
        ((fun ν : Measure ℝ => swingSlopeChainKernel X μ ∘ₘ ν)^[m]
          (swingSlopeKernel X μ ∘ₘ ρ)) := by
  induction m with
  | zero =>
    show swingMarginKernel X μ ∘ₘ ρ = swingOvershootKernel X μ ∘ₘ (swingSlopeKernel X μ ∘ₘ ρ)
    rw [swingMarginKernel, Measure.comp_assoc]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', swingMarginKernel,
      swingSlopeChainKernel, ← Measure.comp_assoc, ← Measure.comp_assoc]

/-- `∫ v d(σ𝖡) = ∫ h dσ` in `ℝ≥0∞`. -/
theorem lintegral_marginLeadingReward_overshoot_comp [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (σ : Measure ℝ) :
    ∫⁻ r, ENNReal.ofReal (marginLeadingReward X μ r) ∂(swingOvershootKernel X μ ∘ₘ σ) =
      ∫⁻ a, ENNReal.ofReal (slopeReward X μ a) ∂σ := by
  have hg : Measurable fun x => ENNReal.ofReal (marginLeadingReward X μ x) :=
    (marginLeadingReward_measurable' hX hi hG).ennreal_ofReal
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [ofReal_slopeReward hX hi hG a, swingOvershootKernel_apply hX a]

/-- **`eq:transient-slopecoefficient`.**  `∫ v d(ρ K^{m+1}) = ∫ (T^m h) d(ρ𝖠)`. -/
theorem integral_marginLeadingReward_iterate_eq [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (ρ : Measure ℝ) (m : ℕ) :
    (∫ r, marginLeadingReward X μ r ∂((fun ν : Measure ℝ => swingMarginKernel X μ ∘ₘ ν)^[m+1] ρ)) =
      ∫ a, (act (swingSlopeChainKernel X μ))^[m] (slopeReward X μ) a ∂(slopeStationaryLaw X μ ρ) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hT : IsFiniteKernel (swingSlopeChainKernel X μ) := swingSlopeChainKernel_isFiniteKernel hX hi
  have hcon := slopeChain_contraction hX hi hG
  have htest := slopeReward_isTest hX hi hG
  have hα : slopeStationaryLaw X μ ρ (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]
    exact slopeStationaryLaw_Iic_zero hX hi hG ρ
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun r => marginLeadingReward_nonneg hX hi hG)
      (marginLeadingReward_measurable' hX hi hG).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (iterate_act_nonneg (slopeReward_nonneg hX hi hG) m))
      (htest.iterate hcon m).meas.aestronglyMeasurable]
  congr 1
  rw [swingMarginKernel_iterate_comp_eq, lintegral_marginLeadingReward_overshoot_comp hX hi hG]
  exact lintegral_iterate_comp hcon measurableSet_Ioi htest (slopeReward_nonneg hX hi hG) m _ hα

/-! ### The slope moment of an entrance law -/

/-- `∫ |a| d(ρ𝖠) ≤ ∫ |r| dρ + E G`. -/
theorem slopeStationaryLaw_integral_abs_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρabs : Integrable (fun r : ℝ => |r|) ρ) :
    (∫ a, |a| ∂slopeStationaryLaw X μ ρ) ≤
      (∫ r, |r| ∂ρ) + ∫ ω, nativeGaussianEnvelope X ω ∂μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hA := swingSlopeKernel_isMarkov (μ := μ) hX
  have hαmom : Integrable (fun a : ℝ => a) (slopeStationaryLaw X μ ρ) :=
    slopeStationaryLaw_first_moment_integrable hX hi hG hρabs
  rw [slopeStationaryLaw, integral_comp_eq hαmom.abs]
  calc (∫ r, (∫ a, |a| ∂swingSlopeKernel X μ r) ∂ρ)
      ≤ ∫ r, (|r| + ∫ ω, nativeGaussianEnvelope X ω ∂μ) ∂ρ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun r => integral_nonneg fun _ => abs_nonneg _)
          (hρabs.add (integrable_const _)) (ae_of_all _ fun r => ?_)
        exact swingSlopeKernel_integral_abs_le hX hi hG r
    _ = (∫ r, |r| ∂ρ) + ∫ ω, nativeGaussianEnvelope X ω ∂μ := by
        rw [integral_add hρabs (integrable_const _), integral_const, probReal_univ, one_smul]

/-! ### The geometric bound -/

/-- **`eq:transient-geometric-bound`, subsequential form.**  For the invariant law
`νinf` (with slope law `λ`) and any entrance law `ρ` with `∫ |r| dρ ≤ M₁`,

`|∫ v d(ρK^{m+1}) - γ| ≤ (3/4)^m L_h (∫ b dλ + M₁ + E G)`. -/
theorem transient_coefficient_geometric_bound [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {νinf : Measure ℝ} [IsProbabilityMeasure νinf]
    (hinv : Kernel.Invariant (swingMarginKernel X μ) νinf)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ νinf))
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρabs : Integrable (fun r : ℝ => |r|) ρ)
    {M₁ : ℝ} (hM₁ : (∫ r, |r| ∂ρ) ≤ M₁) (m : ℕ) :
    |(∫ r, marginLeadingReward X μ r ∂((fun ν : Measure ℝ => swingMarginKernel X μ ∘ₘ ν)^[m+1] ρ)) -
        stationaryLeadingCoefficient X μ νinf| ≤
      (3 / 4 : ℝ) ^ m * slopeRewardLipschitz *
        ((∫ b, b ∂slopeStationaryLaw X μ νinf) + (M₁ + ∫ ω, nativeGaussianEnvelope X ω ∂μ)) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hT : IsFiniteKernel (swingSlopeChainKernel X μ) := swingSlopeChainKernel_isFiniteKernel hX hi
  have hlamP : IsProbabilityMeasure (slopeStationaryLaw X μ νinf) :=
    slopeStationaryLaw_isProbability hX νinf
  have hαP : IsProbabilityMeasure (slopeStationaryLaw X μ ρ) := slopeStationaryLaw_isProbability hX ρ
  have hlamsupp : slopeStationaryLaw X μ νinf (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG νinf
  have hαsupp : slopeStationaryLaw X μ ρ (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG ρ
  have hαmom : Integrable (fun a : ℝ => a) (slopeStationaryLaw X μ ρ) :=
    slopeStationaryLaw_first_moment_integrable hX hi hG hρabs
  rw [integral_marginLeadingReward_iterate_eq hX hi hG ρ m,
    stationaryLeadingCoefficient_eq_slopeReward_integral hX hi hG hinv]
  have hb := abs_integral_iterate_sub_integral_le (slopeChain_contraction hX hi hG)
    (slopeStationaryLaw_invariant hinv) hlamsupp hmom hαsupp hαmom (slopeReward_isTest hX hi hG) m
  have hq : ((3 / 4 : ℝ≥0) : ℝ) = 3 / 4 := by norm_num
  rw [hq] at hb
  refine hb.trans ?_
  have hlam_abs : (∫ b, |b| ∂slopeStationaryLaw X μ νinf) = ∫ b, b ∂slopeStationaryLaw X μ νinf := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_of_compl_eq_zero hlamsupp] with b hb
    exact abs_of_pos hb
  have hα_abs : (∫ a, |a| ∂slopeStationaryLaw X μ ρ) ≤ M₁ + ∫ ω, nativeGaussianEnvelope X ω ∂μ :=
    (slopeStationaryLaw_integral_abs_le hX hi hG hρabs).trans (by linarith)
  rw [hlam_abs]
  gcongr

/-! ### The bump under `v/4` -/

/-- A bump equal to `1` at `3/2`, positive exactly on `(1, 2)`. -/
def unitBump (r : ℝ) : ℝ := clamp01 (1 - 2 * |r - 3 / 2|)

theorem unitBump_nonneg (r : ℝ) : 0 ≤ unitBump r := clamp01_nonneg _

theorem unitBump_le_one (r : ℝ) : unitBump r ≤ 1 := clamp01_le_one _

theorem unitBump_abs_le (r : ℝ) : |unitBump r| ≤ 1 := by
  rw [abs_of_nonneg (unitBump_nonneg r)]
  exact unitBump_le_one r

theorem continuous_unitBump : Continuous unitBump :=
  continuous_clamp01.comp (continuous_const.sub ((continuous_id.sub continuous_const).abs.const_mul 2))

theorem unitBump_pos_of_mem {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) : 0 < unitBump r := by
  have h : |r - 3 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  unfold unitBump clamp01
  exact lt_min one_pos (lt_max_of_lt_right (by linarith))

theorem unitBump_eq_zero_of_not_mem {r : ℝ} (hr : r ∉ Ioo (1 : ℝ) 2) : unitBump r = 0 := by
  apply clamp01_eq_zero
  have h : 1 / 2 ≤ |r - 3 / 2| := by
    by_contra hlt
    rw [not_le, abs_lt] at hlt
    exact hr ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
  linarith

/-- `4ψ ≤ v` pointwise. -/
theorem four_mul_unitBump_le_marginLeadingReward (hi : iIndepFun X μ) (r : ℝ) :
    4 * unitBump r ≤ marginLeadingReward X μ r := by
  by_cases hr : r ∈ Ioo (1 : ℝ) 2
  · have hpos : 0 < r := by linarith [hr.1]
    unfold marginLeadingReward
    rw [if_pos hpos]
    have hV := le_gaussianRenewalPotential hi r
    have hψ := unitBump_le_one r
    linarith [hr.1]
  · rw [unitBump_eq_zero_of_not_mem hr, mul_zero]
    unfold marginLeadingReward
    split_ifs with hpos
    · have := le_gaussianRenewalPotential hi r
      linarith
    · exact le_rfl

/-! ### The Feller property for bounded continuous functions -/

/-- `K(r)` as a probability measure. -/
def swingMarginProb [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) : ProbabilityMeasure ℝ :=
  ⟨swingMarginKernel X μ r, (swingMarginKernel_isMarkov hX hi hG).isProbabilityMeasure r⟩

@[simp] theorem swingMarginProb_coe [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    (swingMarginProb hX hi hG r : Measure ℝ) = swingMarginKernel X μ r := rfl

/-- `r ↦ K(r)` is continuous for the weak topology. -/
theorem swingMarginKernel_prob_continuous [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Continuous (swingMarginProb hX hi hG) := by
  rw [continuous_iff_continuousAt]
  intro r
  rw [ContinuousAt, MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto]
  intro f hfbdd hflip
  obtain ⟨D, hD⟩ := hfbdd
  obtain ⟨Lnn, hL⟩ := hflip
  have hf : IsBddLip f (Lnn : ℝ) (|f 0| + D) := by
    refine ⟨hL.continuous.measurable, fun x y => ?_, fun x => ?_⟩
    · have := hL.dist_le_mul x y
      rwa [Real.dist_eq, Real.dist_eq] at this
    · have := hD x 0
      rw [Real.dist_eq] at this
      calc |f x| = |(f x - f 0) + f 0| := by ring_nf
        _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
        _ ≤ |f 0| + D := by linarith
  exact (swingMarginKernel_bddLip_continuous hX hi hG f _ _ hf).continuousAt

/-- `K` maps bounded continuous functions to bounded continuous functions. -/
theorem swingMarginKernel_integral_continuous_of_bdd [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {g : ℝ → ℝ} {B : ℝ} (hg : Continuous g) (hgB : ∀ x, |g x| ≤ B) :
    Continuous (act (swingMarginKernel X μ) g) := by
  have hKp := swingMarginKernel_prob_continuous hX hi hG
  rw [continuous_iff_continuousAt]
  intro r
  have := tendsto_integral_of_tendsto (hKp.tendsto r) g B hg hgB
  simp only [swingMarginProb_coe] at this
  exact this

theorem iterate_act_swingMarginKernel_bdd_continuous [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {g : ℝ → ℝ} {B : ℝ} (hg : Continuous g) (hgB : ∀ x, |g x| ≤ B) (m : ℕ) :
    Continuous ((act (swingMarginKernel X μ))^[m] g) ∧
      ∀ x, |(act (swingMarginKernel X μ))^[m] g x| ≤ B := by
  have _ : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  induction m with
  | zero => exact ⟨hg, hgB⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨swingMarginKernel_integral_continuous_of_bdd hX hi hG ih.1 ih.2,
      fun x => abs_kernel_integral_le ih.1.measurable ih.2 x⟩

/-! ### Strict positivity of `K^{m+1} ψ` -/

theorem swingMarginKernel_Ioo_pos [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    0 < swingMarginKernel X μ r (Ioo 1 2) := by
  rw [pos_iff_ne_zero]
  intro h0
  have := volume_absolutelyContinuous_swingMarginKernel hX hi hG r h0
  rw [Real.volume_Ioo] at this
  norm_num at this

theorem iterate_act_unitBump_pos [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (m : ℕ) (r : ℝ) :
    0 < (act (swingMarginKernel X μ))^[m+1] unitBump r := by
  have _ : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  induction m generalizing r with
  | zero =>
    rw [Function.iterate_one, act, integral_pos_iff_support_of_nonneg unitBump_nonneg
      (integrable_of_abs_le continuous_unitBump.measurable unitBump_abs_le)]
    refine lt_of_lt_of_le (swingMarginKernel_Ioo_pos hX hi hG r) (measure_mono ?_)
    intro x hx
    exact (unitBump_pos_of_mem hx).ne'
  | succ m ih =>
    have hbc := iterate_act_swingMarginKernel_bdd_continuous hX hi hG continuous_unitBump
      unitBump_abs_le (m+1)
    rw [Function.iterate_succ_apply', act, integral_pos_iff_support_of_nonneg
      (fun x => (ih x).le) (integrable_of_abs_le hbc.1.measurable hbc.2)]
    have hsupp : Function.support ((act (swingMarginKernel X μ))^[m+1] unitBump) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (ih x).ne'
    rw [hsupp, measure_univ]
    exact zero_lt_one

/-! ### `∫ f d(ρK^m) = ∫ K^m f dρ` for bounded measurable `f` -/

theorem iterate_act_measurable {K : Kernel ℝ ℝ} [IsSFiniteKernel K]
    {f : ℝ → ℝ} (hf : Measurable f) (m : ℕ) : Measurable ((act K)^[m] f) := by
  induction m with
  | zero => exact hf
  | succ k ihk =>
    rw [Function.iterate_succ_apply']
    exact act_measurable ihk

theorem iterate_act_abs_le {K : Kernel ℝ ℝ} [IsMarkovKernel K]
    {f : ℝ → ℝ} {B : ℝ} (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) (m : ℕ) :
    ∀ x, |(act K)^[m] f x| ≤ B := by
  induction m with
  | zero => exact hfB
  | succ k ihk =>
    intro x
    rw [Function.iterate_succ_apply']
    exact abs_kernel_integral_le (iterate_act_measurable hf k) ihk x

theorem isProbabilityMeasure_iterate_comp {K : Kernel ℝ ℝ} [IsMarkovKernel K] (m : ℕ) :
    ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      IsProbabilityMeasure ((fun ν : Measure ℝ => K ∘ₘ ν)^[m] σ) := by
  induction m with
  | zero => intro σ hσ; exact hσ
  | succ k ihk =>
    intro σ hσ
    rw [Function.iterate_succ_apply]
    exact ihk (K ∘ₘ σ) inferInstance

theorem integral_iterate_comp_eq_of_bdd {K : Kernel ℝ ℝ} [IsMarkovKernel K]
    {f : ℝ → ℝ} {B : ℝ} (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) (m : ℕ) :
    ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∫ x, f x ∂((fun ν : Measure ℝ => K ∘ₘ ν)^[m] σ)) = ∫ x, (act K)^[m] f x ∂σ := by
  induction m with
  | zero => intro σ _; rfl
  | succ m ih =>
    intro σ hσ
    have : IsProbabilityMeasure (K ∘ₘ σ) := inferInstance
    rw [Function.iterate_succ_apply, ih (K ∘ₘ σ) inferInstance, Function.iterate_succ_apply']
    rw [integral_comp_eq (integrable_of_abs_le (iterate_act_measurable hf m)
      (iterate_act_abs_le hf hfB m))]
    rfl

/-! ### The uniform positive lower bound -/

/-- **The positive logarithmic contribution, uniformly over entrance laws.**
For every `m` and `M₁ ≥ 0` there is `c > 0` such that
`c ≤ ∫ v d(ρK^{m+1})` for every probability `ρ` with `∫ |r| dρ ≤ M₁` under which
`v` is integrable after the `m+1` transitions. -/
theorem exists_transient_coefficient_lower_bound [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M₁ : ℝ} (hM₁ : 0 ≤ M₁) (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : Measure ℝ, IsProbabilityMeasure ρ →
      Integrable (fun r : ℝ => |r|) ρ → (∫ r, |r| ∂ρ) ≤ M₁ →
      Integrable (marginLeadingReward X μ)
        ((fun ν : Measure ℝ => swingMarginKernel X μ ∘ₘ ν)^[m+1] ρ) →
      c ≤ ∫ r, marginLeadingReward X μ r ∂
        ((fun ν : Measure ℝ => swingMarginKernel X μ ∘ₘ ν)^[m+1] ρ) := by
  have _ : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  set K := swingMarginKernel X μ with hKdef
  set g := (act K)^[m+1] unitBump with hgdef
  obtain ⟨hgcont, hgB⟩ := iterate_act_swingMarginKernel_bdd_continuous hX hi hG
    continuous_unitBump unitBump_abs_le (m+1)
  have hgpos : ∀ r, 0 < g r := iterate_act_unitBump_pos hX hi hG m
  set M : ℝ := 2 * M₁ + 1 with hMdef
  have hMpos : 0 < M := by positivity
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by linarith))
    hgcont.continuousOn (s := Icc (-M) M)
  set c₀ := g r₀ with hc₀
  have hc₀pos : 0 < c₀ := hgpos r₀
  refine ⟨2 * c₀, by positivity, ?_⟩
  intro ρ hρ hρabs hρM hint
  have hS : MeasurableSet (Icc (-M) M) := measurableSet_Icc
  -- the mass of `[-M, M]`
  have hmass : 1 / 2 ≤ ρ.real (Icc (-M) M) := by
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := ρ) (f := fun r : ℝ => |r|)
      (ae_of_all _ fun r => abs_nonneg r) hρabs M
    have hsub : (Icc (-M) M)ᶜ ⊆ {x : ℝ | M ≤ |x|} := by
      intro x hx
      rw [mem_compl_iff, mem_Icc] at hx
      show M ≤ |x|
      by_contra hlt
      rw [not_le, abs_lt] at hlt
      exact hx ⟨hlt.1.le, hlt.2.le⟩
    have hcompl : ρ.real (Icc (-M) M)ᶜ ≤ M₁ / M := by
      have h1 : ρ.real (Icc (-M) M)ᶜ ≤ ρ.real {x : ℝ | M ≤ |x|} :=
        measureReal_mono hsub
      have h2 : ρ.real {x : ℝ | M ≤ |x|} ≤ M₁ / M := by
        rw [le_div_iff₀ hMpos]
        linarith
      linarith
    have hhalf : M₁ / M ≤ 1 / 2 := by
      rw [div_le_iff₀ hMpos]
      linarith
    rw [measureReal_compl hS, probReal_univ] at hcompl
    linarith
  -- pass from `v` to `4ψ` and to `K^{m+1}ψ`
  have h4 : (∫ r, 4 * unitBump r ∂((fun ν : Measure ℝ => K ∘ₘ ν)^[m+1] ρ)) ≤
      ∫ r, marginLeadingReward X μ r ∂((fun ν : Measure ℝ => K ∘ₘ ν)^[m+1] ρ) := by
    have : IsProbabilityMeasure ((fun ν : Measure ℝ => K ∘ₘ ν)^[m+1] ρ) :=
      isProbabilityMeasure_iterate_comp (m+1) ρ hρ
    refine integral_mono_of_nonneg (ae_of_all _ fun r => by
        have := unitBump_nonneg r; positivity) hint (ae_of_all _ fun r => ?_)
    exact four_mul_unitBump_le_marginLeadingReward hi r
  have hψ : (∫ r, 4 * unitBump r ∂((fun ν : Measure ℝ => K ∘ₘ ν)^[m+1] ρ)) = 4 * ∫ r, g r ∂ρ := by
    rw [integral_const_mul, integral_iterate_comp_eq_of_bdd continuous_unitBump.measurable
      unitBump_abs_le (m+1) ρ hρ]
  -- lower bound of `∫ g dρ` by the minimum on `[-M, M]`
  have hgint : Integrable g ρ := integrable_of_abs_le hgcont.measurable hgB
  have hind : Integrable ((Icc (-M) M).indicator fun _ => c₀) ρ :=
    (integrable_const c₀).indicator hS
  have hglow : c₀ * ρ.real (Icc (-M) M) ≤ ∫ r, g r ∂ρ := by
    have h1 : (∫ r, (Icc (-M) M).indicator (fun _ => c₀) r ∂ρ) = c₀ * ρ.real (Icc (-M) M) := by
      rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm]
    rw [← h1]
    refine integral_mono hind hgint fun r => ?_
    by_cases hr : r ∈ Icc (-M) M
    · rw [indicator_of_mem hr]
      exact hmin hr
    · rw [indicator_of_notMem hr]
      exact (hgpos r).le
  calc 2 * c₀ = 4 * (c₀ * (1 / 2)) := by ring
    _ ≤ 4 * (c₀ * ρ.real (Icc (-M) M)) := by gcongr
    _ ≤ 4 * ∫ r, g r ∂ρ := by gcongr
    _ = ∫ r, 4 * unitBump r ∂((fun ν : Measure ℝ => K ∘ₘ ν)^[m+1] ρ) := hψ.symm
    _ ≤ _ := h4

end SwingRepair
