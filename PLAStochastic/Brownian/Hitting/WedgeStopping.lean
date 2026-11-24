import PLAStochastic.Brownian.Markov.ExponentialFamily
import PLAStochastic.Brownian.Hitting.TwoBarrierExit

/-!
# Actual stopping at an expanding Brownian wedge

A scalar continuous deviation turns the moving two-sided boundary into the
fixed open set of positive reals. The reciprocal grids then give genuine
continuous exit times and all exponential-parameter stopping identities.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def wedgeDeviation (B : ℝ≥0 → Ω → ℝ) (a b : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max (B t ω - (t : ℝ) - a) (-B t ω - (t : ℝ) - b)

def boundedWedgeExit (B : ℝ≥0 → Ω → ℝ) (a b : ℝ) (T : ℝ≥0) : Ω → ℝ≥0 :=
  boundedOpenExitTime (wedgeDeviation B a b) (Ioi 0) T

omit [MeasurableSpace Ω] in
theorem continuous_wedgeDeviation {ω : Ω} (hc : Continuous (B · ω)) (a b : ℝ) :
    Continuous (wedgeDeviation B a b · ω) :=
  ((hc.sub continuous_subtype_val).sub continuous_const).max
    ((hc.neg.sub continuous_subtype_val).sub continuous_const)

theorem adapted_measurableWedgeDeviation (hB : IsPreBrownianReal B μ) (a b : ℝ) :
    Adapted (brownianNaturalFiltration hB) (wedgeDeviation (measurableBrownian hB) a b) := by
  intro t
  have ht := (Filtration.stronglyAdapted_natural
    (fun t => (measurable_measurableBrownian hB t).stronglyMeasurable) t).measurable
  exact ((ht.sub_const _).sub_const a).max ((ht.neg.sub_const _).sub_const b)

theorem gridHittingTime_wedge_ae_eq_original (hB : IsPreBrownianReal B μ)
    (a b : ℝ) (δ : ℝ≥0) (N : ℕ) :
    gridHittingTime (wedgeDeviation (measurableBrownian hB) a b) (Ioi 0) δ N =ᵐ[μ]
      gridHittingTime (wedgeDeviation B a b) (Ioi 0) δ N := by
  filter_upwards [measurableBrownian_countable_ae_eq hB (fun k : ℕ => δ * k)] with ω hω
  have hp : (fun n : ℕ => wedgeDeviation (measurableBrownian hB) a b (δ * n) ω) =
      (fun n : ℕ => wedgeDeviation B a b (δ * n) ω) := by
    funext n
    exact congrArg (fun x : ℝ => max (x - ((δ * n : ℝ≥0) : ℝ) - a)
      (-x - ((δ * n : ℝ≥0) : ℝ) - b)) (hω n)
  have hh := congrArg (fun f : ℕ → ℝ => hittingBtwn (fun n (_ : Unit) => f n) (Ioi 0) 0 N ()) hp
  exact congrArg (fun k : ℕ => δ * (k : ℝ≥0)) hh

theorem integral_actualBrownianExponentialWith_boundedWedgeExit (hB : IsBrownianReal B μ)
    (c a b : ℝ) (H : ℕ) :
    Integrable (fun ω => actualBrownianExponentialWith B c (boundedWedgeExit B a b H ω) ω) μ ∧
    (∫ ω, actualBrownianExponentialWith B c (boundedWedgeExit B a b H ω) ω ∂μ) = 1 := by
  apply integral_actualBrownianExponentialWith_stopping_limit hB c
    (τ := fun n ω => (gridHittingTime (wedgeDeviation (measurableBrownian hB.toIsPreBrownianReal) a b)
      (Ioi 0) (reciprocalMesh n) (H * (n + 1)) ω : WithTop ℝ≥0)) (T := H)
  · intro n
    exact isStoppingTime_gridHittingTime (adapted_measurableWedgeDeviation hB.toIsPreBrownianReal a b)
      measurableSet_Ioi (reciprocalMesh_pos n) _
  · intro n ω
    exact_mod_cast (gridHittingTime_le (wedgeDeviation (measurableBrownian hB.toIsPreBrownianReal) a b)
      (Ioi 0) _ _ ω).trans_eq (reciprocalMesh_mul_cutoff H n)
  · intro n
    exact gridHittingTime_countable_range _ _ _ _
  · have heq : ∀ᵐ ω ∂μ, ∀ n,
        gridHittingTime (wedgeDeviation (measurableBrownian hB.toIsPreBrownianReal) a b)
          (Ioi 0) (reciprocalMesh n) (H * (n + 1)) ω =
        gridHittingTime (wedgeDeviation B a b) (Ioi 0)
          (reciprocalMesh n) (H * (n + 1)) ω :=
      ae_all_iff.mpr (fun n => gridHittingTime_wedge_ae_eq_original hB.toIsPreBrownianReal
        a b (reciprocalMesh n) (H * (n + 1)))
    filter_upwards [hB.cont, heq] with ω hω heqω
    have ht := gridHittingTime_tendsto_boundedOpenExitTime (S := Ioi 0)
      isOpen_Ioi (continuous_wedgeDeviation hω a b) H
    convert! ht.congr (fun n => (heqω n).symm) using 1

omit [MeasurableSpace Ω] in
theorem before_boundedOpenExitTime_notMem {X : ℝ≥0 → Ω → ℝ} {S : Set ℝ}
    {T t : ℝ≥0} {ω : Ω} (ht : t < boundedOpenExitTime X S T ω) : X t ω ∉ S := by
  intro h
  have hm : t ∈ insert T {s : ℝ≥0 | s ≤ T ∧ X s ω ∈ S} :=
    mem_insert_of_mem _ ⟨ht.le.trans (boundedOpenExitTime_le X S T ω), h⟩
  exact (not_le_of_gt ht) (csInf_le ⟨0, fun _ _ => bot_le⟩ hm)

omit [MeasurableSpace Ω] in
theorem boundedOpenExitTime_notMem {X : ℝ≥0 → Ω → ℝ} {S : Set ℝ}
    {T : ℝ≥0} {ω : Ω} (hc : Continuous (X · ω)) (hS : IsOpen S) (h0 : X 0 ω ∉ S) :
    X (boundedOpenExitTime X S T ω) ω ∉ S := by
  let ρ := boundedOpenExitTime X S T ω
  change X ρ ω ∈ Sᶜ
  by_cases hρ : ρ = 0
  · simpa only [hρ, mem_compl_iff] using! h0
  · have hi : Ico (0 : ℝ≥0) ρ ⊆ (fun t => X t ω) ⁻¹' Sᶜ := by
      intro t ht
      exact before_boundedOpenExitTime_notMem ht.2
    have hm : ρ ∈ closure (Ico (0 : ℝ≥0) ρ) := by
      rw [closure_Ico (Ne.symm hρ)]
      exact ⟨bot_le, le_rfl⟩
    exact closure_minimal hi (hS.isClosed_compl.preimage hc) hm

omit [MeasurableSpace Ω] in
theorem boundedOpenExitTime_mem_closure {X : ℝ≥0 → Ω → ℝ} {S : Set ℝ}
    {T : ℝ≥0} {ω : Ω} (hX : Continuous (X · ω))
    (hT : boundedOpenExitTime X S T ω < T) : X (boundedOpenExitTime X S T ω) ω ∈ closure S := by
  let ρ := boundedOpenExitTime X S T ω
  have hc : ρ ∈ closure (insert T {t : ℝ≥0 | t ≤ T ∧ X t ω ∈ S}) :=
    (isGLB_csInf (insert_nonempty _ _) ⟨0, fun _ _ => bot_le⟩).mem_closure (insert_nonempty _ _)
  rw [insert_eq, closure_union, closure_singleton] at hc
  have hm : ρ ∈ closure {t : ℝ≥0 | t ≤ T ∧ X t ω ∈ S} := hc.resolve_left hT.ne
  apply closure_minimal (t := (fun t => X t ω) ⁻¹' closure S) ?_
    (isClosed_closure.preimage hX) hm
  intro t ht
  exact subset_closure ht.2

omit [MeasurableSpace Ω] in
theorem boundedWedgeExit_nonneg_coordinates {a b : ℝ} {T : ℝ≥0} {ω : Ω}
    (hc : Continuous (B · ω)) (hzero : B 0 ω = 0) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a + (boundedWedgeExit B a b T ω : ℝ) - B (boundedWedgeExit B a b T ω) ω ∧
      0 ≤ b + (boundedWedgeExit B a b T ω : ℝ) + B (boundedWedgeExit B a b T ω) ω := by
  have h0 : wedgeDeviation B a b 0 ω ∉ Ioi 0 := by
    simp only [wedgeDeviation, hzero, NNReal.coe_zero, sub_zero, neg_zero, zero_sub,
      mem_Ioi, not_lt, max_le_iff, neg_nonpos]
    exact ⟨ha, hb⟩
  have hs := boundedOpenExitTime_notMem (T := T) (continuous_wedgeDeviation hc a b) isOpen_Ioi h0
  simp only [wedgeDeviation, mem_Ioi, not_lt] at hs
  have hh := max_le_iff.mp hs
  change _ ≤ _ ∧ _ ≤ _ at hh
  dsimp only [boundedWedgeExit]
  constructor <;> linarith [hh.1, hh.2]

omit [MeasurableSpace Ω] in
theorem boundedWedgeExit_zero_coordinate {a b : ℝ} {T : ℝ≥0} {ω : Ω}
    (hc : Continuous (B · ω)) (hzero : B 0 ω = 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hT : boundedWedgeExit B a b T ω < T) :
    a + (boundedWedgeExit B a b T ω : ℝ) - B (boundedWedgeExit B a b T ω) ω = 0 ∨
      b + (boundedWedgeExit B a b T ω : ℝ) + B (boundedWedgeExit B a b T ω) ω = 0 := by
  have hn := boundedWedgeExit_nonneg_coordinates (T := T) hc hzero ha hb
  have hs := boundedOpenExitTime_mem_closure (continuous_wedgeDeviation hc a b) hT
  rw [closure_Ioi] at hs
  simp only [wedgeDeviation, mem_Ici] at hs
  dsimp only [boundedWedgeExit] at hn ⊢
  rcases le_max_iff.mp hs with h | h
  · exact Or.inl (by linarith [hn.1])
  · exact Or.inr (by linarith [hn.2])

/-- A wedge exponential mode factors into a constant and a Brownian exponential
martingale. Both signs are obtained by choosing the real parameter m. -/
theorem integral_wedgeExponential_boundedWedgeExit (hB : IsBrownianReal B μ)
    (m a b : ℝ) (H : ℕ) :
    Integrable (fun ω =>
      let t := boundedWedgeExit B a b H ω
      Real.exp (-(m ^ 2) * ((a + (t : ℝ) - B t ω) + (b + (t : ℝ) + B t ω)) +
        m * ((a + (t : ℝ) - B t ω) - (b + (t : ℝ) + B t ω)))) μ ∧
    (∫ ω,
      let t := boundedWedgeExit B a b H ω
      Real.exp (-(m ^ 2) * ((a + (t : ℝ) - B t ω) + (b + (t : ℝ) + B t ω)) +
        m * ((a + (t : ℝ) - B t ω) - (b + (t : ℝ) + B t ω))) ∂μ) =
      Real.exp (-(m ^ 2) * (a + b) + m * (a - b)) := by
  have hi := integral_actualBrownianExponentialWith_boundedWedgeExit hB (-2 * m) a b H
  have heq : (fun ω =>
      let t := boundedWedgeExit B a b H ω
      Real.exp (-(m ^ 2) * ((a + (t : ℝ) - B t ω) + (b + (t : ℝ) + B t ω)) +
        m * ((a + (t : ℝ) - B t ω) - (b + (t : ℝ) + B t ω)))) =
      (fun ω => Real.exp (-(m ^ 2) * (a + b) + m * (a - b)) *
        actualBrownianExponentialWith B (-2 * m) (boundedWedgeExit B a b H ω) ω) := by
    funext ω
    dsimp only [actualBrownianExponentialWith]
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · rw [heq]
    exact hi.1.const_mul _
  · change (∫ ω, (fun ω =>
        let t := boundedWedgeExit B a b H ω
        Real.exp (-(m ^ 2) * ((a + (t : ℝ) - B t ω) + (b + (t : ℝ) + B t ω)) +
          m * ((a + (t : ℝ) - B t ω) - (b + (t : ℝ) + B t ω)))) ω ∂μ) = _
    rw [heq, integral_const_mul, hi.2, mul_one]

end BrownianAffine
