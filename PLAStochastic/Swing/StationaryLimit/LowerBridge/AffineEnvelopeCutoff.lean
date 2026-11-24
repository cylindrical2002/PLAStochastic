import PLAStochastic.Swing.StationaryLimit.LowerBridge.NegativeCarryEnvelope

/-!
# Probability cutoff for the two-sided Gaussian affine envelope

The exponential-series certificate gives an integrable random intercept.  The
lemmas below turn that fact into an explicit Markov cutoff.  They deliberately
stop at a pathwise affine-envelope event; no passage-window or least-squares
asymptotic is hidden in this file.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def gaussianNegativeCarryAffineEnvelopeEvent
    (X : ℕ → Ω → ℝ) (c R : ℝ) : Set Ω :=
  {ω | ∀ n : ℕ,
    |cumulativeSamples X n ω| ≤ R + (c / 2) * ((n : ℝ) + 1)}

omit mΩ in
theorem gaussianNegativeCarryAffineIntercept_nonneg
    (X : ℕ → Ω → ℝ) {c : ℝ} (hc : 0 < c) (ω : Ω) :
    0 ≤ gaussianNegativeCarryAffineIntercept X c ω := by
  unfold gaussianNegativeCarryAffineIntercept
  calc
    0 ≤ (2 / c) * (gaussianNegativeCarryEnvelope X c ω).toReal := by
      exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
    _ ≤ max ((2 / c) * (gaussianNegativeCarryEnvelope X c ω).toReal)
        ((2 / c) * (gaussianNegativeCarryEnvelope (negIncrements X) c ω).toReal) :=
      le_max_left _ _

theorem gaussianNegativeCarryAffineIntercept_tail
    [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    μ.real {ω | R < gaussianNegativeCarryAffineIntercept X c ω} ≤
      (∫ ω, gaussianNegativeCarryAffineIntercept X c ω ∂μ) / R := by
  have hI := gaussianNegativeCarryAffineIntercept_integrable hX hi hG hc
  have hF0 : 0 ≤ᵐ[μ] gaussianNegativeCarryAffineIntercept X c :=
    ae_of_all _ (gaussianNegativeCarryAffineIntercept_nonneg X hc)
  have hE : {ω | R < gaussianNegativeCarryAffineIntercept X c ω} ≤ᵐ[μ]
      {ω | R ≤ gaussianNegativeCarryAffineIntercept X c ω} := by
    exact ae_of_all _ (fun ω hω => hω.le)
  exact BrownianAffine.measureReal_le_integral_div_of_ae_dom hR hI hF0 hE

/-! A version with the same `(n+1)` convention used by the passage lemmas. -/
theorem gaussianNegativeCarryAffineEnvelope_cutoff
    [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    μ.real {ω | ¬ (∀ n : ℕ,
      |cumulativeSamples X n ω| ≤
        R + (c / 2) * ((n : ℝ) + 1))} ≤
      (∫ ω, gaussianNegativeCarryAffineIntercept X c ω ∂μ) / R := by
  let A : Ω → ℝ := gaussianNegativeCarryAffineIntercept X c
  let B : Set Ω := {ω | ∀ n : ℕ,
    |cumulativeSamples X n ω| ≤ A ω + (c / 2) * (n : ℝ)}
  let E : Set Ω := {ω | ∀ n : ℕ,
    |cumulativeSamples X n ω| ≤ R + (c / 2) * ((n : ℝ) + 1)}
  have hAE : ∀ᵐ ω ∂μ, ω ∈ B := by
    simpa [B, A] using
      (gaussianNegativeCarryAffineEnvelope_bounds_ae hX hi hG hc)
  have hsub : Eᶜ ≤ᵐ[μ] {ω | R < A ω} := by
    filter_upwards [hAE] with ω hω
    intro hnot
    by_contra hnotR
    have hAR : A ω ≤ R := le_of_not_gt hnotR
    apply hnot
    intro n
    have hn := hω n
    have hq : 0 ≤ c / 2 := by positivity
    dsimp [E] at *
    linarith
  have hmono : μ.real Eᶜ ≤ μ.real {ω | R < A ω} := by
    exact ENNReal.toReal_mono (measure_ne_top μ _)
      (measure_mono_ae hsub)
  have htail := gaussianNegativeCarryAffineIntercept_tail hX hi hG hc hR
  change μ.real Eᶜ ≤
    (∫ ω, gaussianNegativeCarryAffineIntercept X c ω ∂μ) / R
  exact hmono.trans htail

theorem gaussianNegativeCarryAffineEnvelopeEvent_compl_bound
    [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    μ.real (gaussianNegativeCarryAffineEnvelopeEvent X c R)ᶜ ≤
      (∫ ω, gaussianNegativeCarryAffineIntercept X c ω ∂μ) / R := by
  change μ.real {ω | ¬ (∀ n : ℕ,
    |cumulativeSamples X n ω| ≤ R + (c / 2) * ((n : ℝ) + 1))} ≤
      (∫ ω, gaussianNegativeCarryAffineIntercept X c ω ∂μ) / R
  exact gaussianNegativeCarryAffineEnvelope_cutoff hX hi hG hc hR

theorem gaussianNegativeCarryAffineEnvelopeEvent_intersection_compl_bound
    [IsFiniteMeasure μ]
    {A : Set Ω} {α : ℝ} (hα : μ.real Aᶜ ≤ α)
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    μ.real (A ∩ gaussianNegativeCarryAffineEnvelopeEvent X c R)ᶜ ≤
      α + (∫ ω, gaussianNegativeCarryAffineIntercept X c ω ∂μ) / R := by
  let B := gaussianNegativeCarryAffineEnvelopeEvent X c R
  have hsub : (A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ := by
    intro ω hω
    by_cases hAω : ω ∈ A
    · right
      intro hBω
      exact hω ⟨hAω, hBω⟩
    · left
      exact hAω
  have hunion : μ.real (Aᶜ ∪ Bᶜ) ≤ μ.real Aᶜ + μ.real Bᶜ :=
    measureReal_union_le _ _
  have hB := gaussianNegativeCarryAffineEnvelopeEvent_compl_bound hX hi hG hc hR
  calc
    μ.real (A ∩ B)ᶜ ≤ μ.real (Aᶜ ∪ Bᶜ) :=
      measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real Aᶜ + μ.real Bᶜ := hunion
    _ ≤ α + (∫ ω, gaussianNegativeCarryAffineIntercept X c ω ∂μ) / R := by
      dsimp [B] at hB ⊢
      linarith

theorem exists_gaussianNegativeCarryAffineEnvelope_cutoff
    [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      μ.real {ω | ¬ (∀ n : ℕ,
        |cumulativeSamples X n ω| ≤
          R + (c / 2) * ((n : ℝ) + 1))} ≤ ε := by
  let A : Ω → ℝ := gaussianNegativeCarryAffineIntercept X c
  let I : ℝ := ∫ ω, A ω ∂μ
  have hI0 : 0 ≤ I := by
    dsimp [I, A]
    exact integral_nonneg_of_ae
      (ae_of_all _ (gaussianNegativeCarryAffineIntercept_nonneg X hc))
  let R : ℝ := (I + 1) / ε
  have hR : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  have hcut := gaussianNegativeCarryAffineEnvelope_cutoff hX hi hG hc hR
  have hquot : I / R ≤ ε := by
    have hstep : I / R ≤ (I + 1) / R :=
      div_le_div_of_nonneg_right (by linarith) hR.le
    have hReq : (I + 1) / R = ε := by
      dsimp [R]
      field_simp
    exact hstep.trans_eq hReq
  exact hcut.trans hquot

end SwingRepair
