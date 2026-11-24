import PLAStochastic.Brownian.Hitting.GridStopping
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous two-barrier exit values

The exit is the infimum of strict crossings. Continuity proves the boundary
value and keeps every bounded stopped value inside the closed strip.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
theorem before_boundedOpenExitTime_mem_strip {X : ℝ≥0 → Ω → ℝ} {a b : ℝ} {T t : ℝ≥0} {ω : Ω}
    (ht : t < boundedOpenExitTime X (driftBarrierSet a b) T ω) : X t ω ∈ Icc (-b) a := by
  have hn : X t ω ∉ driftBarrierSet a b := by
    intro h
    have hm : t ∈ insert T {s : ℝ≥0 | s ≤ T ∧ X s ω ∈ driftBarrierSet a b} :=
      mem_insert_of_mem _ ⟨ht.le.trans (boundedOpenExitTime_le X _ T ω), h⟩
    exact (not_le_of_gt ht) (csInf_le ⟨0, fun _ _ => bot_le⟩ hm)
  simpa only [driftBarrierSet, mem_union, mem_Iio, mem_Ioi, not_or, not_lt, mem_Icc] using hn

omit [MeasurableSpace Ω] in
theorem boundedOpenExitTime_mem_strip {X : ℝ≥0 → Ω → ℝ} {a b : ℝ} {T : ℝ≥0} {ω : Ω}
    (hX : Continuous (X · ω)) (h0 : X 0 ω ∈ Icc (-b) a) :
    X (boundedOpenExitTime X (driftBarrierSet a b) T ω) ω ∈ Icc (-b) a := by
  let ρ := boundedOpenExitTime X (driftBarrierSet a b) T ω
  change X ρ ω ∈ Icc (-b) a
  by_cases hρ : ρ = 0
  · simpa only [hρ] using h0
  · have hi : Ico (0 : ℝ≥0) ρ ⊆ (fun t => X t ω) ⁻¹' Icc (-b) a := by
      intro t ht
      exact before_boundedOpenExitTime_mem_strip ht.2
    have hm : ρ ∈ closure (Ico (0 : ℝ≥0) ρ) := by
      rw [closure_Ico (Ne.symm hρ)]
      exact ⟨bot_le, le_rfl⟩
    exact closure_minimal hi (isClosed_Icc.preimage hX) hm

omit [MeasurableSpace Ω] in
theorem boundedOpenExitTime_boundary {X : ℝ≥0 → Ω → ℝ} {a b : ℝ} {T : ℝ≥0} {ω : Ω}
    (hX : Continuous (X · ω)) (h0 : X 0 ω ∈ Icc (-b) a)
    (hT : boundedOpenExitTime X (driftBarrierSet a b) T ω < T) :
    X (boundedOpenExitTime X (driftBarrierSet a b) T ω) ω = a ∨
      X (boundedOpenExitTime X (driftBarrierSet a b) T ω) ω = -b := by
  let ρ := boundedOpenExitTime X (driftBarrierSet a b) T ω
  have hi := boundedOpenExitTime_mem_strip (T := T) hX h0
  have hc : ρ ∈ closure (insert T {t : ℝ≥0 | t ≤ T ∧ X t ω ∈ driftBarrierSet a b}) :=
    (isGLB_csInf (insert_nonempty _ _) ⟨0, fun _ _ => bot_le⟩).mem_closure (insert_nonempty _ _)
  rw [insert_eq, closure_union, closure_singleton] at hc
  have hm : ρ ∈ closure {t : ℝ≥0 | t ≤ T ∧ X t ω ∈ driftBarrierSet a b} :=
    hc.resolve_left hT.ne
  have hout : X ρ ω ∈ Iic (-b) ∪ Ici a := by
    apply closure_minimal (t := (fun t => X t ω) ⁻¹' (Iic (-b) ∪ Ici a)) ?_
      ((isClosed_Iic.union isClosed_Ici).preimage hX) hm
    intro t ht
    rcases ht.2 with h | h
    · exact Or.inl (show X t ω ≤ -b from le_of_lt h)
    · exact Or.inr (show a ≤ X t ω from le_of_lt h)
  rcases hout with hlo | hup
  · exact Or.inr (le_antisymm hlo hi.1)
  · exact Or.inl (le_antisymm hi.2 hup)

def openExitTime (X : ℝ≥0 → Ω → ℝ) (S : Set ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t : ℝ≥0 | X t ω ∈ S}

omit [MeasurableSpace Ω] in
theorem boundedOpenExitTime_eq_openExitTime {X : ℝ≥0 → Ω → ℝ} {S : Set ℝ} {T : ℝ≥0} {ω : Ω}
    (hne : {t : ℝ≥0 | X t ω ∈ S}.Nonempty) (hT : openExitTime X S ω ≤ T) :
    boundedOpenExitTime X S T ω = openExitTime X S ω := by
  apply le_antisymm
  · apply le_csInf hne
    intro t ht
    by_cases htT : t ≤ T
    · exact csInf_le ⟨0, fun _ _ => bot_le⟩ (mem_insert_of_mem _ ⟨htT, ht⟩)
    · exact (boundedOpenExitTime_le X S T ω).trans (le_of_not_ge htT)
  · apply le_csInf (insert_nonempty _ _)
    intro t ht
    rcases mem_insert_iff.mp ht with rfl | ht
    · exact hT
    · exact csInf_le ⟨0, fun _ _ => bot_le⟩ ht.2

omit [MeasurableSpace Ω] in
theorem openExitTime_boundary {X : ℝ≥0 → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hX : Continuous (X · ω)) (h0 : X 0 ω ∈ Icc (-b) a)
    (hne : {t : ℝ≥0 | X t ω ∈ driftBarrierSet a b}.Nonempty) :
    X (openExitTime X (driftBarrierSet a b) ω) ω = a ∨
      X (openExitTime X (driftBarrierSet a b) ω) ω = -b := by
  let T := openExitTime X (driftBarrierSet a b) ω + 1
  have heq := boundedOpenExitTime_eq_openExitTime (T := T) hne (le_add_right le_rfl)
  have hlt : boundedOpenExitTime X (driftBarrierSet a b) T ω < T := by
    rw [heq]
    exact lt_add_one _
  simpa only [heq] using boundedOpenExitTime_boundary hX h0 hlt

omit [MeasurableSpace Ω] in
theorem boundedOpenExitTime_eventually_eq {X : ℝ≥0 → Ω → ℝ} {S : Set ℝ} {ω : Ω}
    (hne : {t : ℝ≥0 | X t ω ∈ S}.Nonempty) :
    ∀ᶠ H : ℕ in atTop, boundedOpenExitTime X S H ω = openExitTime X S ω := by
  have ht : Tendsto (fun H : ℕ => (H : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
  exact (ht.eventually (eventually_ge_atTop (openExitTime X S ω))).mono
    (fun _ hH => boundedOpenExitTime_eq_openExitTime hne hH)

variable {B : ℝ≥0 → Ω → ℝ}

theorem brownianDrift_exit_nonempty_ae (hB : IsBrownianReal B μ) (a b : ℝ) :
    ∀ᵐ ω ∂μ, {t : ℝ≥0 | actualBrownianDrift B t ω ∈ driftBarrierSet a b}.Nonempty := by
  filter_upwards [brownian_eventually_below_every_barrier hB (by norm_num : (0 : ℝ) < 1)] with ω hω
  obtain ⟨t, _, ht⟩ := hω (-b) 0
  refine ⟨t, Or.inl ?_⟩
  simpa only [actualBrownianDrift, one_mul, mem_Iio] using ht

/-- The actual unbounded two-barrier exit has exponential expectation one.
The proof removes the deterministic cutoff by dominated convergence. -/
theorem integral_actualBrownianExponential_exit (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun ω => actualBrownianExponential B
      (openExitTime (actualBrownianDrift B) (driftBarrierSet a b) ω) ω) μ ∧
    (∫ ω, actualBrownianExponential B
      (openExitTime (actualBrownianDrift B) (driftBarrierSet a b) ω) ω ∂μ) = 1 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let F : ℕ → Ω → ℝ := fun H ω => actualBrownianExponential B
    (boundedOpenExitTime (actualBrownianDrift B) (driftBarrierSet a b) H ω) ω
  let f : Ω → ℝ := fun ω => actualBrownianExponential B
    (openExitTime (actualBrownianDrift B) (driftBarrierSet a b) ω) ω
  have hF (H : ℕ) : Integrable (F H) μ ∧ (∫ ω, F H ω ∂μ) = 1 :=
    integral_actualBrownianExponential_bounded_exit hB a b H
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun H => F H ω) atTop (𝓝 (f ω)) := by
    filter_upwards [brownianDrift_exit_nonempty_ae hB a b] with ω hω
    apply tendsto_const_nhds.congr'
    exact (boundedOpenExitTime_eventually_eq hω).mono (fun H hH => by
      dsimp only [F, f]
      rw [hH])
  have hbound (H : ℕ) : ∀ᵐ ω ∂μ, ‖F H ω‖ ≤ Real.exp (2 * a) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hzero
    have h0 : actualBrownianDrift B 0 ω ∈ Icc (-b) a := by
      simp only [actualBrownianDrift, NNReal.coe_zero, hzero, sub_zero, mem_Icc]
      exact ⟨neg_nonpos.mpr hb, ha⟩
    have hc : Continuous (actualBrownianDrift B · ω) := hω.sub continuous_subtype_val
    have hs := boundedOpenExitTime_mem_strip (X := actualBrownianDrift B)
      (T := (H : ℝ≥0)) hc h0
    dsimp only [F, actualBrownianExponential]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    change -b ≤ _ ∧ _ ≤ a at hs
    dsimp only [actualBrownianDrift] at hs
    linarith [hs.2]
  have hfmeas : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun H => (hF H).1.aestronglyMeasurable) hlim
  have hfbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ Real.exp (2 * a) := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with ω hω hbω
    exact le_of_tendsto (hω.norm) (Eventually.of_forall hbω)
  have hf : Integrable f μ := (integrable_const (Real.exp (2 * a))).mono' hfmeas hfbound
  refine ⟨hf, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω => Real.exp (2 * a))
    (fun H => (hF H).1.aestronglyMeasurable) (integrable_const _) hbound hlim
  have heq : (fun H : ℕ => ∫ ω, F H ω ∂μ) = fun _ => (1 : ℝ) := funext (fun H => (hF H).2)
  rw [heq] at ht
  exact (tendsto_nhds_unique ht tendsto_const_nhds)

end BrownianAffine
