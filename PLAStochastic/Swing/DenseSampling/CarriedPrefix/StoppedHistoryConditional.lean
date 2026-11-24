import PLAStochastic.Swing.DenseSampling.CarriedPrefix.SmallStateRatio
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Carried estimates conditional on the complete stopped Brownian history

The conditional expectation is taken with respect to the actual stopped
sigma-algebra. The carry and inherited sign are measurable for that history;
only the fresh increments are independent of it, by the proved strong Markov
property. All stopping times in this module are everywhere finite.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- A bounded functional of the full history and an independent future has
conditional expectation equal to its fixed-history integral. -/
theorem condExp_history_independent_integral {Ω β : Type*}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace β] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Y : Ω → β} (hY : AEMeasurable Y μ)
    (hi : Indep (MeasurableSpace.comap Y inferInstance) m μ)
    {F : Ω × β → ℝ} (hF : @Measurable _ _ (m.prod inferInstance) _ F)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ p, |F p| ≤ C) :
    μ[(fun ω => F (ω,Y ω)) | m] =ᵐ[μ]
      fun ω => ∫ y, F (ω,y) ∂(@Measure.map Ω β mΩ inferInstance Y μ) := by
  have hX : @AEMeasurable Ω Ω m mΩ id μ :=
    ⟨id, (show @Measurable Ω Ω mΩ m id from fun s hs => hm s hs), EventuallyEq.rfl⟩
  have hXY : @IndepFun Ω Ω β mΩ m inferInstance id Y μ := by
    change Indep (MeasurableSpace.comap id m) _ μ
    simpa only [MeasurableSpace.comap_id] using hi.symm
  have hfun : AEMeasurable (fun ω => F (ω,Y ω)) μ :=
    hF.comp_aemeasurable (hX.prodMk hY)
  have hfi : Integrable (fun ω => F (ω,Y ω)) μ :=
    Integrable.of_bound hfun.aestronglyMeasurable C
      (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hbound (ω,Y ω)))
  have hgm : StronglyMeasurable[m] (fun ω => ∫ y, F (ω,y) ∂(@Measure.map Ω β mΩ inferInstance Y μ)) :=
    hF.stronglyMeasurable.integral_prod_right'
  let : IsProbabilityMeasure (@Measure.map Ω β mΩ inferInstance Y μ) := Measure.isProbabilityMeasure_map hY
  have hgb (ω : Ω) : ‖∫ y, F (ω,y) ∂(@Measure.map Ω β mΩ inferInstance Y μ)‖ ≤ C := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const (f := fun y => F (ω,y))
      (ae_of_all (@Measure.map Ω β mΩ inferInstance Y μ) (fun y => by simpa only [Real.norm_eq_abs] using hbound (ω,y)))
  have hgi : Integrable (fun ω => ∫ y, F (ω,y) ∂(@Measure.map Ω β mΩ inferInstance Y μ)) μ :=
    Integrable.of_bound (hgm.mono hm).aestronglyMeasurable C (ae_of_all _ hgb)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hfi
    (fun _ _ _ => hgi.restrict) ?_ hgm.aestronglyMeasurable).symm
  intro s hs _
  have hguard := @IndepFun.integral_state_guard_eq Ω Ω β mΩ m inferInstance μ _ id Y
    hX hY hXY s hs F hF C hC hbound
  have hgm' : @Measurable Ω ℝ m _ (fun ω => ∫ y, F (ω,y) ∂(@Measure.map Ω β mΩ inferInstance Y μ)) := hgm.measurable
  rw [← integral_indicator hs, integral_map hX (hgm'.indicator hs).aestronglyMeasurable] at hguard
  simp only [id_eq] at hguard
  change (∫ ω, s.indicator (fun ω => F (ω,Y ω)) ω ∂μ) = _ at hguard
  rw [integral_indicator (hm s hs), integral_indicator (hm s hs)] at hguard
  exact hguard.symm

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The complete stopped history can be retained as the state space. The fresh
sample law is derived by strong Markov, even at a random observation clock. -/
theorem condExp_brownianRestart_history (hB : IsBrownianReal B μ) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0))) (t : ℕ → ℝ≥0)
    {F : Ω × (ℕ → ℝ) → ℝ}
    (hF : @Measurable _ _ (hτ.measurableSpace.prod inferInstance) _ F)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ p, |F p| ≤ C) :
    μ[(fun ω => F (ω,fun j => brownianRestart B τ (t j) ω)) | hτ.measurableSpace] =ᵐ[μ]
      fun ω => ∫ η, F (ω,fun j => B (t j) η) ∂μ := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hrestart := isBrownianReal_brownianRestart hB hτ
  have hY := aemeasurable_pi_lambda _ (fun j => hrestart.aemeasurable (t j))
  have hi := @brownianRestart_grid_indep_state Ω Ω mΩ hτ.measurableSpace μ B hB τ hτ
    id measurable_id t
  have hi' : Indep (MeasurableSpace.comap (fun ω j => brownianRestart B τ (t j) ω)
      inferInstance) hτ.measurableSpace μ := by
    change Indep (MeasurableSpace.comap id hτ.measurableSpace) _ μ at hi
    simpa only [MeasurableSpace.comap_id] using hi.symm
  have hc := condExp_history_independent_integral hτ.measurableSpace_le hY hi' hF hC hbound
  have hlaw := identDistrib_brownianSamples hrestart hB t
  filter_upwards [hc] with ω hω
  rw [hω, hlaw.map_eq]
  exact integral_map (aemeasurable_pi_lambda _ (fun j => hB.aemeasurable (t j)))
    (hF.comp measurable_prodMk_left).aestronglyMeasurable

/-- Conditional probability of the genuine bounded-slope carried fit. -/
theorem condExp_nativeCarriedLongIndicator_stopping (hB : IsBrownianReal B μ)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {W S : Ω → ℝ} (hW : Measurable[hτ.measurableSpace] W)
    (hS : Measurable[hτ.measurableSpace] S) (M : ℝ) {h : ℝ≥0} (hh : 0 < h) (N : ℕ) :
    μ[(fun ω => nativeCarriedLongIndicator
      (fun j => nativePolarity (S ω)*brownianRestart B τ ((j : ℝ≥0)*h) ω)
      (W ω) M h N) | hτ.measurableSpace] =ᵐ[μ]
      fun ω => ∫ η, nativeCarriedLongIndicator
        (fun j => nativePolarity (S ω)*B ((j : ℝ≥0)*h) η) (W ω) M h N ∂μ := by
  apply condExp_brownianRestart_history hB hτ (fun j => (j : ℝ≥0)*h)
    (F := fun p => nativeCarriedLongIndicator (fun j => nativePolarity (S p.1)*p.2 j) (W p.1) M h N) (C := 1)
  · let : MeasurableSpace Ω := hτ.measurableSpace
    apply measurable_nativeCarriedLongIndicator _ (hW.comp measurable_fst) _ M
      (by exact_mod_cast hh) N
    intro j
    exact (measurable_nativePolarity.comp (hS.comp measurable_fst)).mul
      ((measurable_pi_apply j).comp measurable_snd)
  · norm_num
  · intro p
    have hb := nativeCarriedLongIndicator_bounds
      (fun j => nativePolarity (S p.1)*p.2 j) (W p.1) M h N
    rw [abs_of_nonneg hb.1]
    exact hb.2

/-- Conditional mean of the actual carried duration, truncated at H. -/
theorem condExp_nativeCarriedTruncatedDuration_stopping (hB : IsBrownianReal B μ)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {W S : Ω → ℝ} (hW : Measurable[hτ.measurableSpace] W)
    (hS : Measurable[hτ.measurableSpace] S) {h : ℝ≥0} (hh : 0 < h) (H : ℝ≥0) :
    μ[(fun ω => nativeCarriedTruncatedDuration
      (fun j => nativePolarity (S ω)*brownianRestart B τ ((j : ℝ≥0)*h) ω)
      (W ω) 1 h H) | hτ.measurableSpace] =ᵐ[μ]
      fun ω => ∫ η, nativeCarriedTruncatedDuration
        (fun j => nativePolarity (S ω)*B ((j : ℝ≥0)*h) η) (W ω) 1 h H ∂μ := by
  apply condExp_brownianRestart_history hB hτ (fun j => (j : ℝ≥0)*h)
    (F := fun p => nativeCarriedTruncatedDuration (fun j => nativePolarity (S p.1)*p.2 j) (W p.1) 1 h H) (C := H)
  · let : MeasurableSpace Ω := hτ.measurableSpace
    apply measurable_nativeCarriedTruncatedDuration _ (hW.comp measurable_fst) _ 1 hh H
    intro j
    exact (measurable_nativePolarity.comp (hS.comp measurable_fst)).mul
      ((measurable_pi_apply j).comp measurable_snd)
  · exact H.coe_nonneg
  · intro p
    have hb := nativeCarriedTruncatedDuration_bounds
      (fun j => nativePolarity (S p.1)*p.2 j) (W p.1) 1 h H
    rw [abs_of_nonneg hb.1]
    exact hb.2

/-- Lemma B.1 with separate conditional probability and conditional mean, at
any finite stopping time and for every carry and sign in its complete history.
The positive upper constant is chosen before the stopping clock and state. -/
theorem exists_native_carried_stopping_conditional_bounds (hB : IsBrownianReal B μ)
    {M : ℝ} (hM : 0 ≤ M) {q : ℝ≥0} (hq : 0 < q) :
    ∃ A : ℝ, 0 < A ∧ ∀ h H : ℝ≥0, 0 < h → (h : ℝ) ≤ 1 →
      (H : ℝ) ≤ 1/32 → 2*M*(h : ℝ) ≤ Real.sqrt (h : ℝ) → M*(H : ℝ) ≤ 1 →
    ∀ τ : Ω → ℝ≥0, ∀ hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0)),
    ∀ W S : Ω → ℝ, Measurable[hτ.measurableSpace] W → Measurable[hτ.measurableSpace] S →
    ∀ N : ℕ, q ≤ (N : ℝ≥0)*h → ∀ T : ℝ, (N : ℝ)*(h : ℝ) ≤ T →
    ∀ᵐ ω ∂μ, -M*(h : ℝ) ≤ W ω →
      8*(max (W ω) 0+Real.sqrt (h : ℝ)) ≤ (H : ℝ) →
      (μ[(fun η => nativeCarriedLongIndicator
        (fun j => nativePolarity (S η)*brownianRestart B τ ((j : ℝ≥0)*h) η)
        (W η) M h N) | hτ.measurableSpace] ω ≤
          A*(max (W ω) 0+Real.sqrt (h : ℝ)+brownianGridLogRadius h)+2*T*(h : ℝ)^3) ∧
      (nativeCarriedLowerConstant*(max (W ω) 0+Real.sqrt (h : ℝ))*
          Real.log ((H : ℝ)/(8*(max (W ω) 0+Real.sqrt (h : ℝ)))) ≤
        μ[(fun η => nativeCarriedTruncatedDuration
          (fun j => nativePolarity (S η)*brownianRestart B τ ((j : ℝ≥0)*h) η)
          (W η) 1 h H) | hτ.measurableSpace] ω) := by
  obtain ⟨A, hA, hu⟩ := exists_native_carried_survival_upper_logRadius hB hM hq
  refine ⟨A, hA, ?_⟩
  intro h H hh hh1 hHs hMh hMH τ hτ W S hW hS N hN T hNT
  filter_upwards [condExp_nativeCarriedLongIndicator_stopping hB hτ hW hS M hh N,
    condExp_nativeCarriedTruncatedDuration_stopping hB hτ hW hS hh H] with ω hL hD
  intro hw hdH
  rw [hL, hD]
  have hC := isBrownianReal_nativePolarity_mul hB (S ω)
  constructor
  · have hlaw := identDistrib_brownianSamples hC hB (fun j => (j : ℝ≥0)*h)
    have hφ := measurable_nativeCarriedLongIndicator (fun j (D : ℕ → ℝ) => D j)
      (measurable_const (a := W ω)) (fun j => measurable_pi_apply j) M
      (by exact_mod_cast hh) N
    have he := (hlaw.comp hφ).integral_eq
    dsimp only [Function.comp_def] at he
    exact he.le.trans ((integral_nativeCarriedLongIndicator_eq_measure hB (W ω) M hh N).le.trans
      (hu (W ω) 1 h hh hh1 hw N hN T hNT))
  · exact integral_nativeCarriedTruncatedDuration_lower hC hh hHs hM hw hMh hMH hdH

/-- At every finite random observation clock, the conditional long-tail to
conditional-duration ratio vanishes uniformly over the entire small state
layer. No ratio convergence or conditional-law premise is assumed. -/
theorem exists_native_carried_stopping_small_state_comparison (hB : IsBrownianReal B μ)
    {M : ℝ} (hM : 0 ≤ M) {q H : ℝ≥0} (hq : 0 < q) (hH : 0 < H)
    (hHs : (H : ℝ) ≤ 1/32) (hMH : M*(H : ℝ) ≤ 1) {β : ℝ} (hβ : 0 < β) :
    ∃ γ h₀ : ℝ, 0 < γ ∧ 0 < h₀ ∧ ∀ h : ℝ≥0, 0 < h → (h : ℝ) ≤ h₀ →
    ∀ τ : Ω → ℝ≥0, ∀ hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0)),
    ∀ W S : Ω → ℝ, Measurable[hτ.measurableSpace] W → Measurable[hτ.measurableSpace] S →
    ∀ N : ℕ, q ≤ (N : ℝ≥0)*h → ∀ T : ℝ, (N : ℝ)*(h : ℝ) ≤ T →
    ∀ᵐ ω ∂μ, -M*(h : ℝ) ≤ W ω → W ω ≤ 2*γ →
      μ[(fun η => nativeCarriedLongIndicator
        (fun j => nativePolarity (S η)*brownianRestart B τ ((j : ℝ≥0)*h) η)
        (W η) M h N) | hτ.measurableSpace] ω ≤
      β*(μ[(fun η => nativeCarriedTruncatedDuration
        (fun j => nativePolarity (S η)*brownianRestart B τ ((j : ℝ≥0)*h) η)
        (W η) 1 h H) | hτ.measurableSpace] ω)+2*T*(h : ℝ)^3 := by
  obtain ⟨A, hA, hb⟩ := exists_native_carried_stopping_conditional_bounds hB hM hq
  obtain ⟨δ, a, hδ, hδH, ha, _, hr⟩ := exists_carried_ratio_mesh_cutoff
    (show (0 : ℝ) < H by exact_mod_cast hH) hA nativeCarriedLowerConstant_pos hβ
  obtain ⟨γ, h₀, hγ, hh₀, hh₀a, hh₀1, hs⟩ := exists_carried_small_state_cutoff hM hδ ha
  refine ⟨γ, h₀, hγ, hh₀, ?_⟩
  intro h hh hhh τ hτ W S hW hS N hN T hNT
  have hsmall := hs h (by exact_mod_cast hh) hhh
  filter_upwards [hb h H hh (hhh.trans hh₀1) hHs hsmall.1 hMH τ hτ W S hW hS N hN T hNT]
    with ω hω
  intro hw hwγ
  have hdδ := hsmall.2 (W ω) hwγ
  have hdH : 8*(max (W ω) 0+Real.sqrt (h : ℝ)) ≤ (H : ℝ) :=
    (mul_le_mul_of_nonneg_left hdδ (by norm_num)).trans hδH.le
  have hbounds := hω hw hdH
  have hratio := hr h (by exact_mod_cast hh) (hhh.trans hh₀a)
    (max (W ω) 0+Real.sqrt (h : ℝ)) (le_add_of_nonneg_left (le_max_right _ _)) hdδ
  exact hbounds.1.trans (by nlinarith [mul_le_mul_of_nonneg_left hbounds.2 hβ.le])

end SwingRepair
