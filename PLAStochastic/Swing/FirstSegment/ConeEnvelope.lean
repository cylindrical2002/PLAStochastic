import PLAStochastic.Swing.Restart.Chain.FreshWalkEnvelope
import PLAStochastic.Swing.Restart.Chain.StreamRebasing

/-! # A uniform Gaussian envelope for the actual first final cone -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

def nativeFirstSlopeEnvelope (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  5*|X 0 ω|+10*(nativeGaussianEnvelope (fun k => X (1+k)) ω+1)

def nativeFirstSlopeEnvelopeTailConstant : ℝ :=
  (2+nativeGaussianEnvelopeTailConstant)*Real.exp 1

theorem nativeFirstSlopeEnvelope_measurable (hX : ∀ n, Measurable (X n)) :
    Measurable (nativeFirstSlopeEnvelope X) :=
  ((hX 0).abs.const_mul 5).add
    (((nativeGaussianEnvelope_measurable (fun k => hX (1+k))).add_const 1).const_mul 10)

theorem nativeFirstSlopeEnvelope_tail_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t < nativeFirstSlopeEnvelope X ω} ≤
      nativeFirstSlopeEnvelopeTailConstant*Real.exp (-t^2/1600) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hC : 0 < nativeGaussianEnvelopeTailConstant := nativeGaussianEnvelope_tail_constant_pos
  by_cases ht40 : 40 ≤ t
  · let Y := fun k => X (1+k)
    have hiY : iIndepFun Y μ := hi.precomp (g := fun k : ℕ => 1+k)
      (by intro i j hij; dsimp at hij; omega)
    have htailY := nativeGaussianEnvelope_tail_bound (fun k => hX (1+k)) hiY
      (fun k => hG (1+k)) (t := t/40) (by linarith)
    have htailX : μ.real {ω | t/20 < |X 0 ω|} ≤ 2*Real.exp (-(t/20)^2/2) := by
      have hh := cumulativeSamples_abs_tail_bound hX hi hG 1 (z := t/20) (by positivity)
      have hsub : {ω | t/20 < |X 0 ω|} ⊆ {ω | t/20 ≤ |cumulativeSamples X 1 ω|} := by
        intro ω hω
        simpa [cumulativeSamples] using hω.le
      exact (measureReal_mono hsub).trans (by simpa using hh)
    have hcover : {ω | t < nativeFirstSlopeEnvelope X ω} ⊆
        {ω | t/20 < |X 0 ω|} ∪ {ω | t/40 < nativeGaussianEnvelope Y ω} := by
      intro ω hω
      by_contra hn
      have ha : |X 0 ω| ≤ t/20 := le_of_not_gt (fun h => hn (Or.inl h))
      have hb : nativeGaussianEnvelope Y ω ≤ t/40 := le_of_not_gt (fun h => hn (Or.inr h))
      change t < 5*|X 0 ω|+10*(nativeGaussianEnvelope Y ω+1) at hω
      linarith
    have hh := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
    have heX : Real.exp (-(t/20)^2/2) ≤ Real.exp (-t^2/1600) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg t]
    have heY : Real.exp (-(t/40)^2) = Real.exp (-t^2/1600) := by congr 1; ring
    rw [heY] at htailY
    have htotal : μ.real {ω | t < nativeFirstSlopeEnvelope X ω} ≤
        (2+nativeGaussianEnvelopeTailConstant)*Real.exp (-t^2/1600) := by
      nlinarith [htailX, htailY]
    apply htotal.trans
    dsimp [nativeFirstSlopeEnvelopeTailConstant]
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by linarith : 0 ≤ 2+nativeGaussianEnvelopeTailConstant) he)
      (Real.exp_pos _).le
  · have ht40' : t < 40 := lt_of_not_ge ht40
    have he : 1 ≤ Real.exp (1-t^2/1600) := Real.one_le_exp (by nlinarith)
    have heq : Real.exp 1*Real.exp (-t^2/1600) = Real.exp (1-t^2/1600) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hb : 1 ≤ nativeFirstSlopeEnvelopeTailConstant*Real.exp (-t^2/1600) := by
      dsimp [nativeFirstSlopeEnvelopeTailConstant]
      rw [mul_assoc, heq]
      nlinarith
    exact (measureReal_le_one).trans hb

/-- On one full-measure set, every first-rejection cone at every E is bounded
by the same random envelope.  The quantifier over E is inside the a.e. statement. -/
theorem nativeFirst_feasible_slope_bound_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, ∀ E : ℝ, 0 ≤ E → ∀ n : ℕ, 1 ≤ n →
      nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples X i ω) E 0 n 0 →
      ¬ nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples X i ω) E 0 (n+1) 0 →
      ∀ m : ℝ, feasibleSlope (Finset.Icc 1 n) (fun i => (i : ℝ))
        (fun i => cumulativeSamples X i ω) 0 0 E m → |m| ≤ nativeFirstSlopeEnvelope X ω := by
  let Y := fun k => X (1+k)
  have hiY : iIndepFun Y μ := hi.precomp (g := fun k : ℕ => 1+k)
    (by intro i j hij; dsimp at hij; omega)
  filter_upwards [nativeGaussianEnvelope_bounds_ae (fun k => hX (1+k)) hiY
    (fun k => hG (1+k))] with ω hω
  intro E hE n hn hfit hrej m hm
  let G := nativeGaussianEnvelope Y ω+1
  have hG0 : 0 ≤ G := by dsimp [G]; linarith [nativeGaussianEnvelope_nonneg Y ω]
  have hW : ∀ k, |cumulativeSamples Y k ω| ≤ G*((k : ℝ)+1) := by
    intro k
    exact (hω k).trans (mul_le_mul_of_nonneg_right (by dsimp [G]; linarith) (by positivity))
  have hB : 0 < nativeRestartExcess E (X 0 ω)+2*G := by
    have hc : 0 ≤ nativeRestartExcess E (X 0 ω) := le_max_right _ _
    dsimp [G]
    linarith [nativeGaussianEnvelope_nonneg Y ω]
  have hfeas (k : ℕ) : nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples X i ω) E 0 k 0 ↔
        (k : WithTop ℕ) ≤ nativeRestartLength Y E (X 0 ω) ω := by
    simpa [cumulativeSamples, Y] using nativeRestart_feasible_iff X 0 k E 0 ω
  have hN : nativeRestartLength Y E (X 0 ω) ω = (n : WithTop ℕ) := by
    apply le_antisymm _ ((hfeas n).mp hfit)
    by_contra hnot
    have hgt : (n : WithTop ℕ) < nativeRestartLength Y E (X 0 ω) ω := lt_of_not_ge hnot
    have hnext : ((n+1 : ℕ) : WithTop ℕ) ≤ nativeRestartLength Y E (X 0 ω) ω := by
      cases heq : nativeRestartLength Y E (X 0 ω) ω using WithTop.recTopCoe with
      | top => exact le_top
      | coe k =>
        rw [heq] at hgt
        have hnk : n < k := WithTop.coe_lt_coe.mp hgt
        exact WithTop.coe_le_coe.mpr (by omega : n+1 ≤ k)
    exact hrej ((hfeas (n+1)).mpr hnext)
  have hf : nativeRestartLength Y E (X 0 ω) ω ≠ ⊤ := by rw [hN]; exact WithTop.coe_ne_top
  have hNat : nativeRestartLengthNat Y E (X 0 ω) ω = n := by
    change (nativeRestartLength Y E (X 0 ω) ω).untopD 0 = n
    rw [hN]
    rfl
  have hlocal : feasibleSlope (Finset.Icc 1 (nativeRestartLengthNat Y E (X 0 ω) ω))
      (fun i => (i : ℝ)) (fun i => nativeCarriedSamples Y (fun _ => X 0 ω) i ω) 0 0 E m := by
    rw [hNat]
    intro i hi
    have heq : nativeCarriedSamples Y (fun _ => X 0 ω) i ω = cumulativeSamples X i ω := by
      simpa [Y, cumulativeSamples] using nativeRestart_samples_rebase X 0 i 0 ω (Finset.mem_Icc.mp hi).1
    dsimp only
    rw [heq]
    exact hm i hi
  have hb := nativeRestart_feasible_slope_bound Y hE hG0 ω hW hB hf hlocal
  have hc : nativeRestartExcess E (X 0 ω) ≤ |X 0 ω| :=
    max_le (by linarith) (abs_nonneg _)
  change |m| ≤ 5*|X 0 ω|+10*G
  linarith

end SwingRepair
