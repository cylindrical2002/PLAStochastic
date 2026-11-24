import PLAStochastic.Swing.DenseSampling.CarriedPrefix.CarryCoordinates
import PLAStochastic.Brownian.Markov.IndependentState

/-! # Conditional carried-tail versus duration comparison -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def nativeCarriedLongIndicator (D : ℕ → ℝ) (w M h : ℝ) (N : ℕ) : ℝ :=
  if nativeBoundedCarriedFit D w 1 M h N then 1 else 0

theorem nativeCarriedLongIndicator_bounds (D : ℕ → ℝ) (w M h : ℝ) (N : ℕ) :
    0 ≤ nativeCarriedLongIndicator D w M h N ∧ nativeCarriedLongIndicator D w M h N ≤ 1 := by
  unfold nativeCarriedLongIndicator
  split_ifs <;> norm_num

theorem measurable_nativeCarriedLongIndicator {Ω : Type*} [MeasurableSpace Ω]
    (D : ℕ → Ω → ℝ) {W : Ω → ℝ} (hW : Measurable W) (hD : ∀ j, Measurable (D j))
    (M : ℝ) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    Measurable (fun ω => nativeCarriedLongIndicator (fun j => D j ω) (W ω) M h N) :=
  measurable_const.ite (measurableSet_nativeBoundedCarriedFit D hW hD 1 M hh N) measurable_const

theorem measurable_nativeCarriedTruncatedDuration {Ω : Type*} [MeasurableSpace Ω]
    (D : ℕ → Ω → ℝ) {W : Ω → ℝ} (hW : Measurable W) (hD : ∀ j, Measurable (D j))
    (ε : ℝ) {h : ℝ≥0} (hh : 0 < h) (H : ℝ≥0) :
    Measurable (fun ω => nativeCarriedTruncatedDuration (fun j => D j ω) (W ω) ε h H) :=
  measurable_const.min (measurable_nativeCarriedFiniteDuration D hW hD ε
    (by exact_mod_cast hh) (⌈H/h⌉₊+1))

theorem integral_nativeCarriedLongIndicator_eq_measure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (w M : ℝ) {h : ℝ≥0} (hh : 0 < h) (N : ℕ) :
    (∫ ω, nativeCarriedLongIndicator (fun j => B ((j : ℝ≥0)*h) ω) w M h N ∂μ) =
      μ.real (nativeCarriedBoundedFitEvent B w 1 M h N) := by
  have hm := nullMeasurableSet_nativeBoundedCarriedFit_brownian hB (aemeasurable_const (b := w)) 1 M hh N
  have heq : (fun ω => nativeCarriedLongIndicator (fun j => B ((j : ℝ≥0)*h) ω) w M h N) =
      (nativeCarriedBoundedFitEvent B w 1 M h N).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rfl
  change NullMeasurableSet (nativeCarriedBoundedFitEvent B w 1 M h N) μ at hm
  rw [heq]
  change (∫ ω, (nativeCarriedBoundedFitEvent B w 1 M h N).indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
  rw [integral_indicator₀ hm, setIntegral_const, smul_eq_mul, mul_one]

/-- The tail constant is uniform over all Brownian processes on the same space,
so in particular over every deterministic time shift and inherited sign. -/
theorem exists_native_carried_fixed_comparison {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {M : ℝ} (hM : 0 ≤ M) {q : ℝ≥0} (hq : 0 < q) : ∃ A : ℝ, 0 < A ∧
    ∀ C : ℝ≥0 → Ω → ℝ, IsBrownianReal C μ → ∀ w : ℝ, ∀ h H : ℝ≥0,
      0 < h → (h : ℝ) ≤ 1 → (H : ℝ) ≤ 1/32 → -M*(h : ℝ) ≤ w →
      2*M*(h : ℝ) ≤ Real.sqrt (h : ℝ) → M*(H : ℝ) ≤ 1 →
      8*(max w 0+Real.sqrt (h : ℝ)) ≤ (H : ℝ) →
      ∀ N : ℕ, q ≤ (N : ℝ≥0)*h → ∀ T β : ℝ, (N : ℝ)*(h : ℝ) ≤ T → 0 ≤ β →
      A*(max w 0+Real.sqrt (h : ℝ)+brownianGridLogRadius h) ≤
        β*(nativeCarriedLowerConstant*(max w 0+Real.sqrt (h : ℝ))*
          Real.log ((H : ℝ)/(8*(max w 0+Real.sqrt (h : ℝ))))) →
      (∫ ω, nativeCarriedLongIndicator (fun j => C ((j : ℝ≥0)*h) ω) w M h N ∂μ) ≤
        β*(∫ ω, nativeCarriedTruncatedDuration (fun j => C ((j : ℝ≥0)*h) ω) w 1 h H ∂μ)+
          2*T*(h : ℝ)^3 := by
  obtain ⟨A, hA, hu⟩ := exists_native_carried_survival_upper_logRadius hB hM hq
  refine ⟨A, hA, ?_⟩
  intro C hC w h H hh hh1 hHs hw hMh hMH hdH N hN T β hNT hβ hratio
  have hlaw := identDistrib_brownianSamples hC hB (fun j => (j : ℝ≥0)*h)
  have hφ := measurable_nativeCarriedLongIndicator (fun j (D : ℕ → ℝ) => D j)
    (measurable_const (a := w)) (fun j => measurable_pi_apply j) M (by exact_mod_cast hh) N
  have hi := (hlaw.comp hφ).integral_eq
  dsimp only [Function.comp_def] at hi
  have hupper := hi.le.trans ((integral_nativeCarriedLongIndicator_eq_measure hB w M hh N).le.trans
    (hu w 1 h hh hh1 hw N hN T hNT))
  have hlower := integral_nativeCarriedTruncatedDuration_lower hC hh hHs hM hw hMh hMH hdH
  exact hupper.trans (by nlinarith [mul_le_mul_of_nonneg_left hlower hβ])

/-- The fixed-state comparison is transferred to a causal, history-selected
carry and sign. The only remaining ratio premise is a deterministic scalar
inequality; all probability and mean terms are the actual Brownian quantities. -/
theorem exists_native_carried_state_guard_comparison {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) {M : ℝ} (hM : 0 ≤ M) {q : ℝ≥0} (hq : 0 < q) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ≥0 → Ω → ℝ, IsBrownianReal C μ →
    ∀ h H : ℝ≥0, 0 < h → (h : ℝ) ≤ 1 → (H : ℝ) ≤ 1/32 →
    2*M*(h : ℝ) ≤ Real.sqrt (h : ℝ) → M*(H : ℝ) ≤ 1 →
    ∀ X : Ω → α, AEMeasurable X μ → IndepFun X (fun ω (j : ℕ) => C ((j : ℝ≥0)*h) ω) μ →
    ∀ W S : α → ℝ, Measurable W → Measurable S → ∀ U : Set α, MeasurableSet U →
    (∀ x ∈ U, -M*(h : ℝ) ≤ W x ∧ 8*(max (W x) 0+Real.sqrt (h : ℝ)) ≤ (H : ℝ)) →
    ∀ N : ℕ, q ≤ (N : ℝ≥0)*h → ∀ T β : ℝ, (N : ℝ)*(h : ℝ) ≤ T → 0 ≤ β →
    (∀ x ∈ U, A*(max (W x) 0+Real.sqrt (h : ℝ)+brownianGridLogRadius h) ≤
      β*(nativeCarriedLowerConstant*(max (W x) 0+Real.sqrt (h : ℝ))*
        Real.log ((H : ℝ)/(8*(max (W x) 0+Real.sqrt (h : ℝ)))))) →
    (∫ ω, if X ω ∈ U then nativeCarriedLongIndicator
      (fun j => nativePolarity (S (X ω))*C ((j : ℝ≥0)*h) ω) (W (X ω)) M h N else 0 ∂μ) ≤
      β*(∫ ω, if X ω ∈ U then nativeCarriedTruncatedDuration
        (fun j => nativePolarity (S (X ω))*C ((j : ℝ≥0)*h) ω) (W (X ω)) 1 h H else 0 ∂μ)+
        (2*T*(h : ℝ)^3)*μ.real (X ⁻¹' U) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨A, hA, hfixed⟩ := exists_native_carried_fixed_comparison hB hM hq
  refine ⟨A, hA, ?_⟩
  intro C hC h H hh hh1 hHs hMh hMH X hX hi W S hW hS U hU hstate N hN T β hNT hβ hratio
  let Y (ω : Ω) (j : ℕ) := C ((j : ℝ≥0)*h) ω
  let F (p : α × (ℕ → ℝ)) := nativeCarriedLongIndicator
    (fun j => nativePolarity (S p.1)*p.2 j) (W p.1) M h N
  let G (p : α × (ℕ → ℝ)) := nativeCarriedTruncatedDuration
    (fun j => nativePolarity (S p.1)*p.2 j) (W p.1) 1 h H
  have hD (j : ℕ) : Measurable (fun p : α × (ℕ → ℝ) => nativePolarity (S p.1)*p.2 j) :=
    (measurable_nativePolarity.comp (hS.comp measurable_fst)).mul
      ((measurable_pi_apply j).comp measurable_snd)
  have hFm : Measurable F := measurable_nativeCarriedLongIndicator _ (hW.comp measurable_fst)
    hD M (by exact_mod_cast hh) N
  have hGm : Measurable G := measurable_nativeCarriedTruncatedDuration _ (hW.comp measurable_fst)
    hD 1 hh H
  have hY : AEMeasurable Y μ := aemeasurable_pi_lambda _ (fun j => hC.aemeasurable _)
  have hFb (p : α × (ℕ → ℝ)) : |F p| ≤ 1 := by
    have hb := nativeCarriedLongIndicator_bounds (fun j => nativePolarity (S p.1)*p.2 j) (W p.1) M h N
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hGb (p : α × (ℕ → ℝ)) : |G p| ≤ (H : ℝ) := by
    have hb := nativeCarriedTruncatedDuration_bounds (fun j => nativePolarity (S p.1)*p.2 j) (W p.1) 1 h H
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hsections : ∀ x ∈ U, (∫ y, F (x,y) ∂(μ.map Y)) ≤
      β*(∫ y, G (x,y) ∂(μ.map Y))+(2*T*(h : ℝ)^3) := by
    intro x hx
    have hFx : Measurable (fun y => F (x,y)) := hFm.comp measurable_prodMk_left
    have hGx : Measurable (fun y => G (x,y)) := hGm.comp measurable_prodMk_left
    rw [integral_map hY hFx.aestronglyMeasurable, integral_map hY hGx.aestronglyMeasurable]
    exact hfixed (fun t ω => nativePolarity (S x)*C t ω)
      (isBrownianReal_nativePolarity_mul hC (S x)) (W x) h H hh hh1 hHs (hstate x hx).1
      hMh hMH (hstate x hx).2 N hN T β hNT hβ (hratio x hx)
  exact IndepFun.integral_state_guard_le hX hY hi hU hFm hGm (by norm_num) H.coe_nonneg hFb hGb hsections

end SwingRepair
