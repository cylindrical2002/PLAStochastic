import PLAStochastic.Swing.Restart.MaximalPrefix.ObservedHistory
import Mathlib.Probability.Kernel.Composition.Prod

/-! # The actual constrained-SSE restart state and its probability kernel

The state is the already observed sample minus the fitted anchor.  The duration
retains the first failed cone test; the fit uses exactly the accepted prefix.
No increment selected by rejection is replaced by an independent Gaussian.
-/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem measurable_restart_nat_index {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {N : α → ℕ}
    (hN : Measurable N) {F : ℕ → α → β} (hF : ∀ n, Measurable (F n)) :
    Measurable (fun a => F (N a) a) := by
  intro s hs
  have heq : (fun a => F (N a) a) ⁻¹' s = ⋃ n, (N ⁻¹' {n}) ∩ (F n ⁻¹' s) := by
    ext a
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => ⟨N a, rfl, h⟩, by rintro ⟨n, hn, h⟩; rwa [hn]⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n => (hN (measurableSet_singleton n)).inter (hF n hs)

def nativeRestartLength (X : ℕ → Ω → ℝ) (E x : ℝ) : Ω → WithTop ℕ :=
  nativePrefixLength (nativeCarriedSamples X (fun _ => x)) (fun _ => 0) E

def nativeRestartLengthNat (X : ℕ → Ω → ℝ) (E x : ℝ) : Ω → ℕ :=
  nativePrefixLengthNat (nativeCarriedSamples X (fun _ => x)) (fun _ => 0) E

/-- The fallback for an infinite duration is used only off the Gaussian full-measure set. -/
def nativeRestartSlopeAt (X : ℕ → Ω → ℝ) (E x : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if hn : 0 < n then
    nativeSelectedSlope (Finset.Icc 1 n) (Finset.nonempty_Icc.mpr hn)
      (fun i => (i : ℝ)) (fun i => nativeCarriedSamples X (fun _ => x) i ω) 0 0 E
  else 0

def nativeRestartSlope (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω) : ℝ :=
  nativeRestartSlopeAt X E x (nativeRestartLengthNat X E x ω) ω

/-- Exactly `x + W_N - m N`, with the rejected sample excluded from the fit. -/
def nativeRestartNext (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω) : ℝ :=
  x + cumulativeSamples X (nativeRestartLengthNat X E x ω) ω -
    nativeRestartSlope X E x ω * (nativeRestartLengthNat X E x ω : ℝ)

theorem nativeRestartLength_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    Measurable (fun p : ℝ × Ω => nativeRestartLength X E p.1 p.2) := by
  exact nativePrefixLength_measurable
    (nativeCarriedSamples (fun k (p : ℝ × Ω) => X k p.2) Prod.fst) (fun _ => 0)
    (nativeCarriedSamples_measurable (fun k => (hX k).comp measurable_snd) measurable_fst)
    measurable_const E

theorem nativeRestartLengthNat_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    Measurable (fun p : ℝ × Ω => nativeRestartLengthNat X E p.1 p.2) :=
  (nativeRestartLength_measurable X hX E).untopD 0

theorem nativeRestartSlopeAt_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (E : ℝ) (n : ℕ) :
    Measurable (fun p : ℝ × Ω => nativeRestartSlopeAt X E p.1 n p.2) := by
  by_cases hn : 0 < n
  · simp only [nativeRestartSlopeAt, dif_pos hn]
    exact measurable_nativeSelectedSlope _ _ _
      (nativeCarriedSamples (fun k (p : ℝ × Ω) => X k p.2) Prod.fst) 0 E
      measurable_const (fun k _ => nativeCarriedSamples_measurable
        (fun k => (hX k).comp measurable_snd) measurable_fst k)
  · simp only [nativeRestartSlopeAt, dif_neg hn]
    exact measurable_const

theorem nativeRestartSlope_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    Measurable (fun p : ℝ × Ω => nativeRestartSlope X E p.1 p.2) := by
  exact measurable_restart_nat_index (nativeRestartLengthNat_measurable X hX E)
    (nativeRestartSlopeAt_measurable X hX E)

theorem nativeRestartNext_measurable (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    Measurable (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) := by
  have hN := nativeRestartLengthNat_measurable X hX E
  have hW : Measurable (fun p : ℝ × Ω =>
      cumulativeSamples X (nativeRestartLengthNat X E p.1 p.2) p.2) :=
    measurable_restart_nat_index hN (fun n =>
      (Finset.measurable_sum (Finset.range n) (fun k _ => hX k)).comp measurable_snd)
  exact (measurable_fst.add hW).sub
    ((nativeRestartSlope_measurable X hX E).mul ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp hN))

theorem nativeRestartLength_ae_finite {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ) :
    ∀ᵐ ω ∂μ, nativeRestartLength X E x ω ≠ ⊤ := by
  apply nativePrefixLength_ae_finite hX hi hG _ _ _ hE ⌈8 * E ^ 2⌉₊ (Nat.le_ceil _)
  intro ω k
  simp [nativeCarriedSamples, Nat.add_comm]

theorem nativeRestartLengthNat_integrable {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ) :
    Integrable (fun ω => (nativeRestartLengthNat X E x ω : ℝ)) μ := by
  apply nativePrefixLengthNat_integrable hX hi hG _ _
    (nativeCarriedSamples_measurable hX measurable_const) measurable_const _
    hE ⌈8 * E ^ 2⌉₊ (Nat.le_ceil _)
  intro ω k
  simp [nativeCarriedSamples, Nat.add_comm]

def nativeRestartMean (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E x : ℝ) : ℝ :=
  ∫ ω, (nativeRestartLengthNat X E x ω : ℝ) ∂μ

theorem nativeRestartMean_measurable {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ k, Measurable (X k)) (E : ℝ) : Measurable (nativeRestartMean X μ E) := by
  have h : Measurable (fun p : ℝ × Ω => (nativeRestartLengthNat X E p.1 p.2 : ℝ)) :=
    (measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      (nativeRestartLengthNat_measurable X hX E)
  exact h.stronglyMeasurable.integral_prod_right.measurable

theorem nativeRestartMean_bounds {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ) :
    1 ≤ nativeRestartMean X μ E x ∧
      nativeRestartMean X μ E x ≤ 2 * (⌈8 * E ^ 2⌉₊ : ℝ) /
        (1 - gaussianBlockPass.toReal) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  constructor
  · have hlow : ∀ᵐ ω ∂μ, (1 : ℝ) ≤ (nativeRestartLengthNat X E x ω : ℝ) := by
      filter_upwards [nativeRestartLength_ae_finite hX hi hG hE x] with ω hω
      have hone := one_le_nativePrefixLength (nativeCarriedSamples X (fun _ => x))
        (fun _ => 0) hE.le ω
      change (1 : WithTop ℕ) ≤ nativeRestartLength X E x ω at hone
      change (1 : ℝ) ≤ (((nativeRestartLength X E x ω).untopD 0 : ℕ) : ℝ)
      cases heq : nativeRestartLength X E x ω using WithTop.recTopCoe with
      | top => exact (hω heq).elim
      | coe n =>
        rw [heq] at hone
        have hn : 1 ≤ n := WithTop.coe_le_coe.mp hone
        simp only [WithTop.untopD_coe]
        exact_mod_cast hn
    simpa [nativeRestartMean] using integral_mono_ae (integrable_const (1 : ℝ))
      (nativeRestartLengthNat_integrable hX hi hG hE x) hlow
  · apply nativePrefixLengthNat_mean_le_ceil hX hi hG _ _
      (nativeCarriedSamples_measurable hX measurable_const) measurable_const _ hE
    intro ω k
    simp [nativeCarriedSamples, Nat.add_comm]

/-- The probability kernel induced by the actual measurable constrained-SSE update. -/
def nativeRestartKernel (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) : Kernel ℝ ℝ :=
  (Kernel.id ×ₖ Kernel.const ℝ μ).map (fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2)

theorem nativeRestartKernel_apply {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ k, Measurable (X k)) (E x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    nativeRestartKernel X μ E x A = μ {ω | nativeRestartNext X E x ω ∈ A} := by
  rw [nativeRestartKernel, Kernel.map_apply' _ (nativeRestartNext_measurable X hX E) _ hA,
    Kernel.id_prod_apply' _ _ ((nativeRestartNext_measurable X hX E) hA)]
  rfl

theorem nativeRestartKernel_isMarkov {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    IsMarkovKernel (nativeRestartKernel X μ E) := by
  exact Kernel.IsMarkovKernel.map _ (nativeRestartNext_measurable X hX E)

end SwingRepair
