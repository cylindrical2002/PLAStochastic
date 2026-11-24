import PLAStochastic.Swing.DenseSampling.Rejection.ConditionalEstimates

/-! # A quantitative all-stream probability budget from the original Brownian law -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem nativeRejectionLongCost_bounds (y : ℕ → ℝ) (M γ : ℝ) (h : ℝ≥0) (N b : ℕ) :
    0 ≤ nativeRejectionLongCost y M γ h N b ∧ nativeRejectionLongCost y M γ h N b ≤ 1 := by
  dsimp only [nativeRejectionLongCost]
  split_ifs
  · exact nativeCarriedLongIndicator_bounds _ _ _ _ _
  · norm_num

theorem nativeRejectionBudgetCost_bounds (y : ℕ → ℝ) (M γ : ℝ) (h H : ℝ≥0) (b : ℕ) :
    0 ≤ nativeRejectionBudgetCost y M γ h H b ∧ nativeRejectionBudgetCost y M γ h H b ≤ H := by
  unfold nativeRejectionBudgetCost
  split_ifs
  · exact nativeCarriedTruncatedDuration_bounds _ _ _ _ _
  · exact ⟨le_rfl, H.coe_nonneg⟩

theorem sum_nativeRejectionBudgetCost_le_horizon (y : ℕ → ℝ) (M γ : ℝ)
    {h H : ℝ≥0} (hh : 0 < h) {n last : ℕ} (hn : n+1 ≤ last) {T : ℝ}
    (hnT : (n : ℝ)*(h : ℝ) ≤ T) (horizon : T+(H : ℝ) ≤ (last : ℝ)*(h : ℝ)) :
    (∑ b ∈ Finset.range (n+1), nativeRejectionBudgetCost y M γ h H b) ≤ (last : ℝ)*(h : ℝ) := by
  apply le_trans _ (sum_nativeRejectionDuration_le_horizon y (by norm_num : (0 : ℝ) ≤ 1) hh hn hnT horizon)
  apply Finset.sum_le_sum
  intro b _
  unfold nativeRejectionBudgetCost
  split_ifs with hg hr
  · exact le_rfl
  · exact False.elim (hr hg.1)
  · exact (nativeCarriedTruncatedDuration_bounds _ _ _ _ _).1
  · exact le_rfl

theorem integrable_nativeRejectionLongCost {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : ∀ j, AEMeasurable (Y j) μ)
    (M γ : ℝ) {h : ℝ≥0} (hh : 0 < h) (N b : ℕ) :
    Integrable (fun ω => nativeRejectionLongCost (fun j => Y j ω) M γ h N b) μ := by
  apply Integrable.of_bound ((measurable_nativeRejectionLongCost M γ hh N b).comp_aemeasurable
    (aemeasurable_pi_lambda _ hY)).aestronglyMeasurable 1
  exact ae_of_all _ (fun ω => by
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (nativeRejectionLongCost_bounds _ _ _ _ _ _).1]
    exact (nativeRejectionLongCost_bounds _ _ _ _ _ _).2)

theorem integrable_nativeRejectionBudgetCost {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : ∀ j, AEMeasurable (Y j) μ)
    (M γ : ℝ) {h : ℝ≥0} (hh : 0 < h) (H : ℝ≥0) (b : ℕ) :
    Integrable (fun ω => nativeRejectionBudgetCost (fun j => Y j ω) M γ h H b) μ := by
  apply Integrable.of_bound ((measurable_nativeRejectionBudgetCost M γ hh H b).comp_aemeasurable
    (aemeasurable_pi_lambda _ hY)).aestronglyMeasurable H
  exact ae_of_all _ (fun ω => by
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (nativeRejectionBudgetCost_bounds _ _ _ _ _ _).1]
    exact (nativeRejectionBudgetCost_bounds _ _ _ _ _ _).2)

/-- Summing at all possible rejection observations uses the actual pathwise time
budget. The quantitative mesh exception is O(h^3 times the number of grid times). -/
theorem exists_native_rejection_sum_comparison {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {M : ℝ} (hM : 0 ≤ M) {q H : ℝ≥0} (hq : 0 < q) (hH : 0 < H)
    (hHs : (H : ℝ) ≤ 1/32) (hMH : M*(H : ℝ) ≤ 1) {β : ℝ} (hβ : 0 < β) :
    ∃ γ h₀ : ℝ, 0 < γ ∧ 0 < h₀ ∧ ∀ h : ℝ≥0, 0 < h → (h : ℝ) ≤ h₀ →
    ∀ n last : ℕ, n+1 ≤ last → ∀ T₀ : ℝ, (n : ℝ)*(h : ℝ) ≤ T₀ →
    T₀+(H : ℝ) ≤ (last : ℝ)*(h : ℝ) →
    ∀ N : ℕ, q ≤ (N : ℝ≥0)*h → ∀ T : ℝ, (N : ℝ)*(h : ℝ) ≤ T →
    (∫ ω, ∑ b ∈ Finset.range (n+1),
      nativeRejectionLongCost (fun j => B ((j : ℝ≥0)*h) ω) M γ h N b ∂μ) ≤
      β*((last : ℝ)*(h : ℝ))+(2*T*(h : ℝ)^3)*((n : ℝ)+1) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨γ, h₀, hγ, hh₀, hc⟩ := exists_native_rejection_conditional_comparison hB hM hq hH hHs hMH hβ
  refine ⟨γ, h₀, hγ, hh₀, ?_⟩
  intro h hh hhh n last hn T₀ hnT horizon N hN T hNT
  let Y (j : ℕ) (ω : Ω) := B ((j : ℝ≥0)*h) ω
  have hY : ∀ j, AEMeasurable (Y j) μ := fun j => hB.aemeasurable _
  have hIL (b : ℕ) := integrable_nativeRejectionLongCost hY M γ hh N b
  have hID (b : ℕ) := integrable_nativeRejectionBudgetCost hY M γ hh H b
  have hT : 0 ≤ T := (mul_nonneg (Nat.cast_nonneg N) h.coe_nonneg).trans hNT
  have he : 0 ≤ 2*T*(h : ℝ)^3 := by positivity
  have hb (b : ℕ) : (∫ ω, nativeRejectionLongCost (fun j => Y j ω) M γ h N b ∂μ) ≤
      β*(∫ ω, nativeRejectionBudgetCost (fun j => Y j ω) M γ h H b ∂μ)+2*T*(h : ℝ)^3 := by
    exact (hc h hh hhh b N hN T hNT).trans (add_le_add le_rfl
      ((mul_le_mul_of_nonneg_left measureReal_le_one he).trans_eq (mul_one _)))
  have hd : (∫ ω, ∑ b ∈ Finset.range (n+1), nativeRejectionBudgetCost (fun j => Y j ω) M γ h H b ∂μ) ≤
      (last : ℝ)*(h : ℝ) := by
    have hid := integrable_finsetSum (Finset.range (n+1)) (fun b _ => hID b)
    have hm := integral_mono_ae hid (integrable_const ((last : ℝ)*(h : ℝ)))
      (ae_of_all _ (fun ω => sum_nativeRejectionBudgetCost_le_horizon (fun j => Y j ω) M γ hh hn hnT horizon))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hm
  calc
    _ = ∑ b ∈ Finset.range (n+1), ∫ ω, nativeRejectionLongCost (fun j => Y j ω) M γ h N b ∂μ :=
      integral_finsetSum _ (fun b _ => hIL b)
    _ ≤ ∑ b ∈ Finset.range (n+1), (β*(∫ ω, nativeRejectionBudgetCost (fun j => Y j ω) M γ h H b ∂μ)+2*T*(h : ℝ)^3) :=
      Finset.sum_le_sum (fun b _ => hb b)
    _ = β*(∫ ω, ∑ b ∈ Finset.range (n+1), nativeRejectionBudgetCost (fun j => Y j ω) M γ h H b ∂μ)+
        (2*T*(h : ℝ)^3)*((n : ℝ)+1) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← integral_finsetSum _ (fun b _ => hID b)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hd hβ.le) le_rfl

end SwingRepair
