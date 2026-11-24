import PLAStochastic.Swing.DenseSampling.CarriedPrefix.TailMeanRatio
import PLAStochastic.Swing.DenseSampling.CarriedPrefix.ConditionalTailComparison

/-! # Vanishing conditional tail-to-mean ratios at all small boundary states -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- A deterministic mesh cutoff controls both the slightly negative carry
allowance and the entire moving boundary scale. -/
theorem exists_carried_small_state_cutoff {M δ a : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (ha : 0 < a) :
    ∃ γ h₀ : ℝ, 0 < γ ∧ 0 < h₀ ∧ h₀ ≤ a ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ → 2*M*h ≤ Real.sqrt h ∧
        ∀ w : ℝ, w ≤ 2*γ → max w 0+Real.sqrt h ≤ δ := by
  let γ := δ/4
  let h₀ := min a (min 1 (min ((δ/2)^2) ((1/(2*M+1))^2)))
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hh₀ : 0 < h₀ := by dsimp only [h₀]; positivity
  refine ⟨γ, h₀, hγ, hh₀, min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro h hh hh₀'
  have hδsq : h ≤ (δ/2)^2 := hh₀'.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hMsq : h ≤ (1/(2*M+1))^2 := hh₀'.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hrootδ : Real.sqrt h ≤ δ/2 := by
    have hl := Real.sqrt_le_sqrt hδsq
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)] at hl
  have hrootM : Real.sqrt h ≤ 1/(2*M+1) := by
    have hl := Real.sqrt_le_sqrt hMsq
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)] at hl
  have hm := (le_div_iff₀ (show 0 < 2*M+1 by positivity)).mp hrootM
  have hs := Real.sqrt_nonneg h
  have hsq := Real.sq_sqrt hh.le
  have hmul := mul_le_mul_of_nonneg_right hm hs
  refine ⟨by nlinarith, ?_⟩
  intro w hw
  have hmax : max w 0 ≤ 2*γ := max_le hw (by positivity)
  dsimp only [γ] at hmax
  linarith

/-- For every requested ratio beta>0, a common state layer and mesh cutoff
make the genuine conditional long-tail cost at most beta times the genuine
truncated-duration budget. There is no remaining assumed ratio limit. -/
theorem exists_native_carried_small_state_guard_comparison {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) {M : ℝ} (hM : 0 ≤ M) {q H : ℝ≥0} (hq : 0 < q)
    (hH : 0 < H) (hHs : (H : ℝ) ≤ 1/32) (hMH : M*(H : ℝ) ≤ 1)
    {β : ℝ} (hβ : 0 < β) :
    ∃ γ h₀ : ℝ, 0 < γ ∧ 0 < h₀ ∧ ∀ h : ℝ≥0, 0 < h → (h : ℝ) ≤ h₀ →
    ∀ C : ℝ≥0 → Ω → ℝ, IsBrownianReal C μ →
    ∀ X : Ω → α, AEMeasurable X μ → IndepFun X (fun ω (j : ℕ) => C ((j : ℝ≥0)*h) ω) μ →
    ∀ W S : α → ℝ, Measurable W → Measurable S → ∀ U : Set α, MeasurableSet U →
    (∀ x ∈ U, -M*(h : ℝ) ≤ W x ∧ W x ≤ 2*γ) →
    ∀ N : ℕ, q ≤ (N : ℝ≥0)*h → ∀ T : ℝ, (N : ℝ)*(h : ℝ) ≤ T →
    (∫ ω, if X ω ∈ U then nativeCarriedLongIndicator
      (fun j => nativePolarity (S (X ω))*C ((j : ℝ≥0)*h) ω) (W (X ω)) M h N else 0 ∂μ) ≤
      β*(∫ ω, if X ω ∈ U then nativeCarriedTruncatedDuration
        (fun j => nativePolarity (S (X ω))*C ((j : ℝ≥0)*h) ω) (W (X ω)) 1 h H else 0 ∂μ)+
        (2*T*(h : ℝ)^3)*μ.real (X ⁻¹' U) := by
  obtain ⟨A, hA, hcomp⟩ := exists_native_carried_state_guard_comparison (α := α) hB hM hq
  obtain ⟨δ, a, hδ, hδH, ha, _, hratio⟩ := exists_carried_ratio_mesh_cutoff
    (show (0 : ℝ) < H by exact_mod_cast hH) hA nativeCarriedLowerConstant_pos hβ
  obtain ⟨γ, h₀, hγ, hh₀, hh₀a, hh₀1, hsmall⟩ := exists_carried_small_state_cutoff hM hδ ha
  refine ⟨γ, h₀, hγ, hh₀, ?_⟩
  intro h hh hhh C hC X hX hi W S hW hS U hU hstate N hN T hNT
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hbounds := hsmall h hhR hhh
  have hstates : ∀ x ∈ U, -M*(h : ℝ) ≤ W x ∧
      8*(max (W x) 0+Real.sqrt (h : ℝ)) ≤ (H : ℝ) := by
    intro x hx
    exact ⟨(hstate x hx).1, (mul_le_mul_of_nonneg_left
      (hbounds.2 _ (hstate x hx).2) (by norm_num)).trans hδH.le⟩
  apply hcomp C hC h H hh (hhh.trans hh₀1) hHs hbounds.1 hMH X hX hi W S hW hS U hU
    hstates N hN T β hNT hβ.le
  intro x hx
  have hr := hratio h hhR (hhh.trans hh₀a) (max (W x) 0+Real.sqrt (h : ℝ))
    (le_add_of_nonneg_left (le_max_right _ _)) (hbounds.2 _ (hstate x hx).2)
  simpa only [mul_assoc] using hr

end SwingRepair
