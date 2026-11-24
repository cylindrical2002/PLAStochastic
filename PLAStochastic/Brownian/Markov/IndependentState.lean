import PLAStochastic.Brownian.Markov.StrongMarkov
import Mathlib.Probability.Independence.Integration

/-! # Transfer of fresh-path estimates to a history-measurable state -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β}

/-- Integrating a bounded fresh-path functional at an independent random state
is exactly integration of its fixed-state sections. -/
theorem IndepFun.integral_state_guard_eq (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hi : IndepFun X Y μ) {A : Set α} (hA : MeasurableSet A)
    {F : α × β → ℝ} (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ p, |F p| ≤ C) :
    (∫ ω, if X ω ∈ A then F (X ω,Y ω) else 0 ∂μ) =
      ∫ x in A, ∫ y, F (x,y) ∂(μ.map Y) ∂(μ.map X) := by
  let G (p : α × β) := if p.1 ∈ A then F p else 0
  have hG : Measurable G := hF.ite (hA.preimage measurable_fst) measurable_const
  have hGi : Integrable G ((μ.map X).prod (μ.map Y)) := by
    apply Integrable.of_bound hG.aestronglyMeasurable C
    apply Eventually.of_forall
    intro p
    dsimp only [G]
    split_ifs
    · simpa only [Real.norm_eq_abs] using hbound p
    · simpa only [norm_zero] using hC
  have hmap := IndepFun.map_prod_eq_prod_map_map hX hY hi
  calc
    _ = ∫ p, G p ∂(μ.map (fun ω => (X ω,Y ω))) :=
      (integral_map (hX.prodMk hY) hG.aestronglyMeasurable).symm
    _ = ∫ p, G p ∂((μ.map X).prod (μ.map Y)) := by rw [hmap]
    _ = ∫ x, ∫ y, G (x,y) ∂(μ.map Y) ∂(μ.map X) := integral_prod G hGi
    _ = ∫ x, A.indicator (fun x => ∫ y, F (x,y) ∂(μ.map Y)) x ∂(μ.map X) := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      by_cases hx : x ∈ A
      · simp only [G, if_pos hx, Set.indicator_of_mem hx]
      · simp only [G, if_neg hx, Set.indicator_of_notMem hx, integral_zero]
    _ = _ := integral_indicator hA

/-- Sectionwise fresh-path comparisons remain valid after selecting a state
from the observed history. The additive error is paid only on the guard. -/
theorem IndepFun.integral_state_guard_le (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hi : IndepFun X Y μ) {A : Set α} (hA : MeasurableSet A)
    {F G : α × β → ℝ} (hF : Measurable F) (hG : Measurable G)
    {CF CG : ℝ} (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (hFb : ∀ p, |F p| ≤ CF) (hGb : ∀ p, |G p| ≤ CG) {b δ : ℝ}
    (hsection : ∀ x ∈ A, (∫ y, F (x,y) ∂(μ.map Y)) ≤
      b*(∫ y, G (x,y) ∂(μ.map Y))+δ) :
    (∫ ω, if X ω ∈ A then F (X ω,Y ω) else 0 ∂μ) ≤
      b*(∫ ω, if X ω ∈ A then G (X ω,Y ω) else 0 ∂μ)+δ*μ.real (X ⁻¹' A) := by
  have hFi : Integrable F ((μ.map X).prod (μ.map Y)) :=
    Integrable.of_bound hF.aestronglyMeasurable CF (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using hFb p)
  have hGi : Integrable G ((μ.map X).prod (μ.map Y)) :=
    Integrable.of_bound hG.aestronglyMeasurable CG (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using hGb p)
  rw [IndepFun.integral_state_guard_eq hX hY hi hA hF hCF hFb,
    IndepFun.integral_state_guard_eq hX hY hi hA hG hCG hGb]
  have hb := integral_mono_ae hFi.integral_prod_left.restrict
    ((hGi.integral_prod_left.restrict.const_mul b).add (integrable_const δ)) (by
      filter_upwards [ae_restrict_mem hA] with x hx
      exact hsection x hx)
  dsimp only [Pi.add_apply] at hb
  rw [integral_add (hGi.integral_prod_left.restrict.const_mul b) (integrable_const δ),
    integral_const_mul, integral_const, Measure.real, Measure.restrict_apply_univ,
    Measure.map_apply_of_aemeasurable hX hA, smul_eq_mul, mul_comm _ δ] at hb
  exact hb

omit [IsProbabilityMeasure μ] in
/-- Actual strong Markov independence also covers every measurable function of
the stopped history and every countable family of future samples. -/
theorem brownianRestart_grid_indep_state {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (brownianNaturalFiltration hB.toIsPreBrownianReal)
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {S : Ω → α} (hS : Measurable[hτ.measurableSpace] S) (t : ℕ → ℝ≥0) :
    IndepFun S (fun ω j => brownianRestart B τ (t j) ω) μ := by
  have hi := brownianRestart_indep_stopped hB hτ
  have hs : MeasurableSpace.comap S inferInstance ≤ hτ.measurableSpace :=
    measurable_iff_comap_le.mp hS
  have hy : MeasurableSpace.comap (fun ω j => brownianRestart B τ (t j) ω) inferInstance ≤
      MeasurableSpace.comap (fun ω u => brownianRestart B τ u ω) inferInstance := by
    have hp : Measurable (fun f : ℝ≥0 → ℝ => fun j : ℕ => f (t j)) :=
      measurable_pi_lambda _ (fun j => measurable_pi_apply (t j))
    have hh := MeasurableSpace.comap_mono (g := fun ω u => brownianRestart B τ u ω)
      (measurable_iff_comap_le.mp hp)
    simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hh
  exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left hi hy) hs).symm

omit [IsProbabilityMeasure μ] in
/-- The actually observed finite grid history, represented as a full array by
zero padding. This representation is Borel and retains every past sample. -/
def brownianGridPast (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (r : ℕ) (ω : Ω) (j : ℕ) : ℝ :=
  if j ≤ r then B ((j : ℝ≥0)*h) ω else 0

omit [IsProbabilityMeasure μ] in
/-- Independence at each possible rejection grid time follows directly from
Brownian increments, even before introducing a random rejection index. -/
theorem indepFun_brownianGridPast_future {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (h : ℝ≥0) (r : ℕ) :
    IndepFun (brownianGridPast B h r)
      (fun ω (j : ℕ) => B ((r : ℝ≥0)*h+(j : ℝ≥0)*h) ω-B ((r : ℝ≥0)*h) ω) μ := by
  let P (f : Set.Iic ((r : ℝ≥0)*h) → ℝ) (j : ℕ) : ℝ :=
    if hj : j ≤ r then f ⟨(j : ℝ≥0)*h,
      Set.mem_Iic.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (show (0 : ℝ≥0) ≤ h from bot_le))⟩ else 0
  have hp : Measurable P := by
    apply measurable_pi_lambda
    intro j
    dsimp only [P]
    split_ifs with hj
    · exact measurable_pi_apply _
    · exact measurable_const
  have hi := (hB.indepFun_shift ((r : ℝ≥0)*h)).comp
    (measurable_pi_lambda _ (fun j : ℕ => measurable_pi_apply ((j : ℝ≥0)*h))) hp
  convert hi.symm using 1
  · ext ω j
    dsimp only [Function.comp_def, P, brownianGridPast]
    split_ifs <;> rfl
  · rfl

omit [IsProbabilityMeasure μ] in
/-- Any Borel state computed from the observed grid history is independent of
the entire fresh sampled path. No independence is assigned to the carry. -/
theorem indepFun_brownianGridPast_state_future {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (h : ℝ≥0) (r : ℕ) {S : (ℕ → ℝ) → α} (hS : Measurable S) :
    IndepFun (fun ω => S (brownianGridPast B h r ω))
      (fun ω (j : ℕ) => B ((r : ℝ≥0)*h+(j : ℝ≥0)*h) ω-B ((r : ℝ≥0)*h) ω) μ := by
  simpa only [Function.comp_def, id_eq] using
    (indepFun_brownianGridPast_future hB h r).comp hS measurable_id

end BrownianAffine
