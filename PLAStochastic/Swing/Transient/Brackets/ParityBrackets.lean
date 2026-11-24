import PLAStochastic.Swing.Transient.Brackets.SlopeTestOrder
import PLAStochastic.ForMathlib.MeasureTheory.Measure.WassersteinOne

/-! # Parity brackets for the real-segment coefficients (S-BRACKET)

Let `α` be a probability law on `(0, ∞)` with a first moment and `T(0, ·) ≤ α` in the
test order `SlopeTestLE`, and let `c_m = ∫ T^m h dα` (`slopeIterateCoefficient`).  With
`γ = γ_Swing = ∫ h dλ`, `λ = ν_∞𝖠`, for an invariant probability `ν_∞` (`νst` in the
statements) of the margin kernel whose slope law has a first moment:

* `slopeIterateCoefficient_even_succ_le`: `c_{2m+2} ≤ c_{2m}`;
* `slopeIterateCoefficient_odd_le_succ`: `c_{2m+1} ≤ c_{2m+3}`;
* `slopeIterateCoefficient_tendsto`: `c_m → γ`;
* `stationaryLeadingCoefficient_le_even`, `odd_le_stationaryLeadingCoefficient`:
  `c_{2m+1} ≤ γ ≤ c_{2m}`;
* `abs_slopeIterateCoefficient_sub_le`: `|c_m - γ| ≤ L_h W₁(α, λ) (3/4)^m`, with
  `W₁(α, λ) < ∞` (`wassersteinOne_slope_lt_top`).

The monotonicity argument: `αT² ≤ T(0, ·) ≤ α` (`slopeTestLE_comp_zero` and the hypothesis),
`T^{2m}h` is a monotone Lipschitz test and `T^{2m+1}h` an antitone one, and
`∫ T^{k+2}h dα = ∫ T^k h d(αT²)`.  The limit is the `3/4` contraction of `T`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open SlopeEvaluation LeadingCoefficient
set_option backward.isDefEq.respectTransparency false

theorem SlopeEvaluation.IsTest.neg {S : Set ℝ} {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest S L f) :
    IsTest S L (fun x => -f x) :=
  ⟨hf.meas.neg, fun x hx y hy => by simpa only [edist_neg_neg] using hf.lip hx hy⟩

theorem SlopeEvaluation.act_neg (T : Kernel ℝ ℝ) (f : ℝ → ℝ) :
    act T (fun x => -f x) = fun a => -act T f a := by
  funext a
  exact integral_neg _

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The coefficient sequence `c_m = ∫ (T^m h) dα` of an entrance slope law `α`. -/
def slopeIterateCoefficient (X : ℕ → Ω → ℝ) (μ : Measure Ω) [SFinite μ] (α : Measure ℝ)
    (m : ℕ) : ℝ :=
  ∫ a, (act (swingSlopeChainKernel X μ))^[m] (slopeReward X μ) a ∂α

/-- Two steps from a law above the boundary row decrease every monotone test:
`∫ T²f dα ≤ ∫ f dα` when `T(0, ·) ≤ α`. -/
theorem integral_act_act_le_of_slopeTestLE_zero [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαS : α (Ioi 0)ᶜ = 0)
    (hαm : Integrable (fun a : ℝ => a) α)
    (hα0 : SlopeTestLE (swingSlopeChainKernel X μ 0) α)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : IsTest (Ioi 0) L f) (hmono : MonotoneOn f (Ioi 0)) :
    ∫ a, act (swingSlopeChainKernel X μ) (act (swingSlopeChainKernel X μ) f) a ∂α ≤
      ∫ a, f a ∂α := by
  have := swingSlopeChainKernel_isSFiniteKernel hX hi
  have hc := slopeChain_contraction hX hi hG
  set T := swingSlopeChainKernel X μ with hT
  have hTα := comp_isProbability hc hαS
  have hTαS : (T ∘ₘ α) (Ioi 0)ᶜ = 0 := comp_compl_eq_zero hc measurableSet_Ioi hαS
  have hTαm : Integrable (fun b : ℝ => b) (T ∘ₘ α) := comp_integrable_id hc hαS hαm
  rw [← integral_comp_eq_act hc hαS hαm (hf.map hc), ← integral_comp_eq_act hc hTαS hTαm hf]
  exact ((slopeTestLE_comp_zero hX hi hG hTαS hTαm).trans hα0) L f hf hmono

theorem slopeIterate_add_two_apply (F : (ℝ → ℝ) → ℝ → ℝ) (f : ℝ → ℝ) (k : ℕ) :
    F^[k + 2] f = F (F (F^[k] f)) := by
  rw [show k + 2 = (k + 1) + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_succ_apply']

/-- **Even coefficients decrease**: `c_{2m+2} ≤ c_{2m}`. -/
theorem slopeIterateCoefficient_even_succ_le [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαS : α (Ioi 0)ᶜ = 0)
    (hαm : Integrable (fun a : ℝ => a) α)
    (hα0 : SlopeTestLE (swingSlopeChainKernel X μ 0) α) (m : ℕ) :
    slopeIterateCoefficient X μ α (2 * m + 2) ≤ slopeIterateCoefficient X μ α (2 * m) := by
  have := swingSlopeChainKernel_isSFiniteKernel hX hi
  have hc := slopeChain_contraction hX hi hG
  unfold slopeIterateCoefficient
  rw [slopeIterate_add_two_apply]
  exact integral_act_act_le_of_slopeTestLE_zero hX hi hG hαS hαm hα0
    ((slopeReward_isTest hX hi hG).iterate hc (2 * m))
    (slope_iterates_bracket_monotone hX hi hG m).1

/-- **Odd coefficients increase**: `c_{2m+1} ≤ c_{2m+3}`. -/
theorem slopeIterateCoefficient_odd_le_succ [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαS : α (Ioi 0)ᶜ = 0)
    (hαm : Integrable (fun a : ℝ => a) α)
    (hα0 : SlopeTestLE (swingSlopeChainKernel X μ 0) α) (m : ℕ) :
    slopeIterateCoefficient X μ α (2 * m + 1) ≤ slopeIterateCoefficient X μ α (2 * m + 3) := by
  have := swingSlopeChainKernel_isSFiniteKernel hX hi
  have hc := slopeChain_contraction hX hi hG
  set T := swingSlopeChainKernel X μ with hT
  set f := (act T)^[2 * m + 1] (slopeReward X μ) with hfdef
  have hf : IsTest (Ioi 0) _ f := (slopeReward_isTest hX hi hG).iterate hc (2 * m + 1)
  have hanti : AntitoneOn f (Ioi 0) := (slope_iterates_bracket_monotone hX hi hG m).2
  have hmono : MonotoneOn (fun x => -f x) (Ioi 0) :=
    fun x hx y hy hxy => neg_le_neg (hanti hx hy hxy)
  have h := integral_act_act_le_of_slopeTestLE_zero hX hi hG hαS hαm hα0 hf.neg hmono
  rw [act_neg, act_neg, integral_neg, integral_neg, neg_le_neg_iff] at h
  unfold slopeIterateCoefficient
  rw [show 2 * m + 3 = (2 * m + 1) + 2 from rfl, slopeIterate_add_two_apply]
  exact h

/-! ### The limit -/

/-- **`c_m → γ_Swing`.** -/
theorem slopeIterateCoefficient_tendsto [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαS : α (Ioi 0)ᶜ = 0)
    (hαm : Integrable (fun a : ℝ => a) α)
    {νst : Measure ℝ} [IsProbabilityMeasure νst]
    (hinv : Kernel.Invariant (swingMarginKernel X μ) νst)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ νst)) :
    Tendsto (slopeIterateCoefficient X μ α) atTop
      (𝓝 (stationaryLeadingCoefficient X μ νst)) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have := swingSlopeChainKernel_isSFiniteKernel hX hi
  have hc := slopeChain_contraction hX hi hG
  have hlam : IsProbabilityMeasure (slopeStationaryLaw X μ νst) :=
    slopeStationaryLaw_isProbability hX νst
  have hlamS : slopeStationaryLaw X μ νst (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG νst
  rw [stationaryLeadingCoefficient_eq_slopeReward_integral hX hi hG hinv]
  set K : ℝ := (slopeRewardLipschitz : ℝ) *
    ((∫ b, |b| ∂slopeStationaryLaw X μ νst) + ∫ a, |a| ∂α) with hK
  have hbound : ∀ m, |slopeIterateCoefficient X μ α m -
      ∫ b, slopeReward X μ b ∂slopeStationaryLaw X μ νst| ≤ (3 / 4 : ℝ) ^ m * K := by
    intro m
    have h := abs_integral_iterate_sub_integral_le hc (slopeStationaryLaw_invariant hinv) hlamS
      hmom hαS hαm (slopeReward_isTest hX hi hG) m
    have e : ((3 / 4 : ℝ≥0) : ℝ) = 3 / 4 := by norm_num
    rw [e] at h
    unfold slopeIterateCoefficient
    rw [hK, ← mul_assoc]
    exact h
  have hgeo : Tendsto (fun m : ℕ => (3 / 4 : ℝ) ^ m * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).mul_const K
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun m => norm_nonneg _) (fun m => by rw [Real.norm_eq_abs]; exact hbound m)
    hgeo

/-- **`γ_Swing ≤ c_{2m}`.** -/
theorem stationaryLeadingCoefficient_le_even [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαS : α (Ioi 0)ᶜ = 0)
    (hαm : Integrable (fun a : ℝ => a) α)
    (hα0 : SlopeTestLE (swingSlopeChainKernel X μ 0) α)
    {νst : Measure ℝ} [IsProbabilityMeasure νst]
    (hinv : Kernel.Invariant (swingMarginKernel X μ) νst)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ νst)) (m : ℕ) :
    stationaryLeadingCoefficient X μ νst ≤ slopeIterateCoefficient X μ α (2 * m) := by
  have hanti : Antitone (fun m => slopeIterateCoefficient X μ α (2 * m)) := by
    refine antitone_nat_of_succ_le fun m => ?_
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    exact slopeIterateCoefficient_even_succ_le hX hi hG hαS hαm hα0 m
  have hsub : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    (show StrictMono (fun m : ℕ => 2 * m) from fun a b h => by simp only; omega).tendsto_atTop
  exact hanti.le_of_tendsto
    ((slopeIterateCoefficient_tendsto hX hi hG hαS hαm hinv hmom).comp hsub) m

/-- **`c_{2m+1} ≤ γ_Swing`.** -/
theorem odd_le_stationaryLeadingCoefficient [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαS : α (Ioi 0)ᶜ = 0)
    (hαm : Integrable (fun a : ℝ => a) α)
    (hα0 : SlopeTestLE (swingSlopeChainKernel X μ 0) α)
    {νst : Measure ℝ} [IsProbabilityMeasure νst]
    (hinv : Kernel.Invariant (swingMarginKernel X μ) νst)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ νst)) (m : ℕ) :
    slopeIterateCoefficient X μ α (2 * m + 1) ≤ stationaryLeadingCoefficient X μ νst := by
  have hmono : Monotone (fun m => slopeIterateCoefficient X μ α (2 * m + 1)) := by
    refine monotone_nat_of_le_succ fun m => ?_
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring]
    exact slopeIterateCoefficient_odd_le_succ hX hi hG hαS hαm hα0 m
  have hsub : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
    (show StrictMono (fun m : ℕ => 2 * m + 1) from fun a b h => by simp only; omega).tendsto_atTop
  exact hmono.ge_of_tendsto
    ((slopeIterateCoefficient_tendsto hX hi hG hαS hαm hinv hmom).comp hsub) m

/-- **Parity brackets (S-BRACKET, order part).**  For an entrance slope law `α` on `(0, ∞)`
with a first moment and `T(0, ·) ≤ α`: the even coefficients decrease and the odd ones
increase to the common limit `γ_Swing`, which they bracket. -/
theorem slopeIterateCoefficient_parity_brackets [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαS : α (Ioi 0)ᶜ = 0)
    (hαm : Integrable (fun a : ℝ => a) α)
    (hα0 : SlopeTestLE (swingSlopeChainKernel X μ 0) α)
    {νst : Measure ℝ} [IsProbabilityMeasure νst]
    (hinv : Kernel.Invariant (swingMarginKernel X μ) νst)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ νst)) :
    (∀ m, slopeIterateCoefficient X μ α (2 * m + 2) ≤ slopeIterateCoefficient X μ α (2 * m)) ∧
    (∀ m, slopeIterateCoefficient X μ α (2 * m + 1) ≤
      slopeIterateCoefficient X μ α (2 * m + 3)) ∧
    Tendsto (slopeIterateCoefficient X μ α) atTop (𝓝 (stationaryLeadingCoefficient X μ νst)) ∧
    (∀ m, stationaryLeadingCoefficient X μ νst ≤ slopeIterateCoefficient X μ α (2 * m)) ∧
    (∀ m, slopeIterateCoefficient X μ α (2 * m + 1) ≤ stationaryLeadingCoefficient X μ νst) :=
  ⟨slopeIterateCoefficient_even_succ_le hX hi hG hαS hαm hα0,
    slopeIterateCoefficient_odd_le_succ hX hi hG hαS hαm hα0,
    slopeIterateCoefficient_tendsto hX hi hG hαS hαm hinv hmom,
    stationaryLeadingCoefficient_le_even hX hi hG hαS hαm hα0 hinv hmom,
    odd_le_stationaryLeadingCoefficient hX hi hG hαS hαm hα0 hinv hmom⟩

/-! ### The `W₁` error bound -/

/-- `W₁(α, λ) < ∞` for an entrance law with a first moment. -/
theorem wassersteinOne_slope_lt_top (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαm : Integrable (fun a : ℝ => a) α)
    {νst : Measure ℝ} [IsProbabilityMeasure νst]
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ νst)) :
    wassersteinOne α (slopeStationaryLaw X μ νst) < ⊤ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hlam : IsProbabilityMeasure (slopeStationaryLaw X μ νst) :=
    slopeStationaryLaw_isProbability hX νst
  exact wassersteinOne_lt_top hαm hmom

/-- **S-BRACKET error bound**: `|c_m - γ_Swing| ≤ L_h · W₁(α, λ) · (3/4)^m` for every
probability entrance law `α` on `(0, ∞)` with a first moment (no order hypothesis needed). -/
theorem abs_slopeIterateCoefficient_sub_le [SFinite μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {α : Measure ℝ} [IsProbabilityMeasure α] (hαS : α (Ioi 0)ᶜ = 0)
    (hαm : Integrable (fun a : ℝ => a) α)
    {νst : Measure ℝ} [IsProbabilityMeasure νst]
    (hinv : Kernel.Invariant (swingMarginKernel X μ) νst)
    (hmom : Integrable (fun b : ℝ => b) (slopeStationaryLaw X μ νst)) (m : ℕ) :
    |slopeIterateCoefficient X μ α m - stationaryLeadingCoefficient X μ νst| ≤
      slopeRewardLipschitz * (wassersteinOne α (slopeStationaryLaw X μ νst)).toReal *
        (3 / 4 : ℝ) ^ m := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have := swingSlopeChainKernel_isSFiniteKernel hX hi
  have hc := slopeChain_contraction hX hi hG
  have hlam : IsProbabilityMeasure (slopeStationaryLaw X μ νst) :=
    slopeStationaryLaw_isProbability hX νst
  have hlamS : slopeStationaryLaw X μ νst (Ioi 0)ᶜ = 0 := by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG νst
  have hh := slopeReward_isTest hX hi hG
  have hf := hh.iterate hc m
  have h1 : (1 : ℝ) ∈ Ioi 0 := mem_Ioi.mpr one_pos
  rw [stationaryLeadingCoefficient_eq_slopeReward_integral hX hi hG hinv,
    ← integral_iterate_eq_of_invariant hc (slopeStationaryLaw_invariant hinv) hlamS hmom hh h1 m]
  have h := abs_integral_sub_le_wassersteinOne hαS hlamS hf.lip hf.meas
    (hf.integrable_of_moment hαS hαm h1) (hf.integrable_of_moment hlamS hmom h1)
    (wassersteinOne_slope_lt_top hX hi hαm hmom).ne
  unfold slopeIterateCoefficient
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end SwingRepair
