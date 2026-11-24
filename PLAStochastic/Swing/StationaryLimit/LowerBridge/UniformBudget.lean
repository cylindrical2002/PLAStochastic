import PLAStochastic.Swing.StationaryLimit.LowerBridge.WindowArithmetic
import PLAStochastic.Swing.StationaryLimit.LowerBridge.AffineEnvelopeCutoff

/-!
# A uniform scalar budget for the affine lower bridge

The affine lower-bridge theorem has four scalar side conditions (`hstrict`,
`hD`, `hx`, and the lower-window inequality).  This file records one fully
explicit sufficient budget which discharges all four at once.  The constants
are intentionally conservative: the point is to remove hidden pathwise
obligations, while leaving the genuinely probabilistic passage/localization
input visible.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
The budget
`41K + 69C + 69qJ + 14MJ + 7M + 21q ≤ E`
is a convenient sufficient condition for the ceiling lower endpoint.  The
factor `8q ≤ δ` gives `8q ≤ a` for every localized prefix slope `a ≥ δ`,
which yields the ratio bound
`3(a+q)/(2(a-q)) ≤ 27/14`.
-/
theorem prefixCrossingLowerBridgeEventRandom_of_affine_original_envelope_of_uniform_budget
    {Ω : Type*} {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    {K δ M C q : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hr : |r| ≤ K)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J - 1))
    (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hqsmall : 8 * q ≤ δ)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1))
    (hbudget :
      41 * K + 69 * C + 69 * q * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * q ≤ E) :
    ω ∈ prefixCrossingLowerBridgeEventRandom X E r J := by
  have hqδ : q < δ := by
    nlinarith
  have hbounds := prefixCrossingSlope_bounds_of_earlySlopeGood
    (X := X) (r := r) (K := K) (δ := δ) (M := M) ω hJ hδ hgood hr
  let a : ℝ := prefixCrossingSlope X r J ω
  let D : ℝ := E - r + C + q * (J : ℝ)
  let b : ℝ := prefixCrossingLevel X E r J ω
  have ha_lower : δ ≤ a := by
    exact hbounds.1
  have ha_upper : a ≤ M := by
    exact hbounds.2
  have hJr : (0 : ℝ) ≤ (J : ℝ) := by positivity
  have hqJ : 0 ≤ q * (J : ℝ) := mul_nonneg hq hJr
  have hMJ : 0 ≤ M * (J : ℝ) := mul_nonneg hM hJr
  have hD_lower : E - K + C + q * (J : ℝ) ≤ D := by
    dsimp [D]
    have hrK : -K ≤ -r := by
      have hr' : r ≤ K := (abs_le.mp hr).2
      linarith
    linarith
  have hD_nonneg : 0 ≤ D := by
    have hbase : 0 ≤ E - K + C + q * (J : ℝ) := by
      nlinarith [hbudget]
    exact hbase.trans hD_lower
  have hD_upper : D ≤ E + K + C + q * (J : ℝ) := by
    dsimp [D]
    have hrK : -r ≤ K := by
      have hr' : -K ≤ r := (abs_le.mp hr).1
      linarith
    linarith
  have hden : 0 < a - q := by
    have : q < a := lt_of_lt_of_le hqδ ha_lower
    exact sub_pos.mpr this
  have ha_nonneg : 0 ≤ a := le_trans (le_of_lt hδ) ha_lower
  have hME : M ≤ E := by
    nlinarith [hbudget]
  have hstrict : M * (J : ℝ) + K + C + q * (J : ℝ) < 2 * E := by
    nlinarith [hbudget]
  have hx : 0 < (3 * D / (a - q) - 1) / 2 := by
    have hthree : a - q < 3 * D := by
      have hamq : a - q ≤ M := by linarith
      have hDlarge : M < 3 * D := by
        nlinarith [hbudget]
      linarith
    have hquot : 1 < 3 * D / (a - q) :=
      (lt_div_iff₀ hden).2 (by linarith)
    linarith
  have hD_req : 0 ≤ E - r + C + q * (J : ℝ) := by
    exact hD_nonneg
  have hratio : 3 * (a + q) / (2 * (a - q)) ≤ (27 / 14 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (a - q))).2
    have h8 : 8 * q ≤ a := by linarith [hqsmall, ha_lower]
    nlinarith
  have hterm :
      (a + q) * (3 * D / (2 * (a - q))) ≤
        (27 / 14 : ℝ) * (E + K + C + q * (J : ℝ)) := by
    have hrewrite :
        (a + q) * (3 * D / (2 * (a - q))) =
          (3 * (a + q) / (2 * (a - q))) * D := by
      field_simp
    rw [hrewrite]
    have hmul := mul_le_mul_of_nonneg_right hratio hD_nonneg
    have hcoef : 0 ≤ (27 / 14 : ℝ) := by norm_num
    have hmul' := mul_le_mul_of_nonneg_left hD_upper hcoef
    linarith
  have hLscalar :
      (a + q) * ((3 * D / (a - q) - 1) / 2 + 1) +
          (2 * C + 2 * q * (J : ℝ) + q) ≤ b := by
    have hb_lower :
        2 * E - K - M * (J : ℝ) - C - q * (J : ℝ) ≤ b := by
      dsimp [b]
      have hWJ := hW (J - 1)
      have hJcast : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
        rw [Nat.cast_sub hJ]
        push_cast
        ring
      rw [hJcast] at hWJ
      have hlow : -(C + q * (J : ℝ)) ≤ cumulativeSamples X (J - 1) ω := by
        have habs := neg_le_abs (cumulativeSamples X (J - 1) ω)
        linarith
      have hrK : -K ≤ -r := by
        have hr' : r ≤ K := (abs_le.mp hr).2
        linarith
      have haM : a ≤ M := ha_upper
      have haM' : prefixCrossingSlope X r J ω ≤ M := by
        simpa [a] using ha_upper
      have haJ' :
          prefixCrossingSlope X r J ω * (J : ℝ) ≤ M * (J : ℝ) :=
        mul_le_mul_of_nonneg_right haM' hJr
      dsimp [prefixCrossingLevel, a]
      linarith
    have hrewrite :
        (a + q) * ((3 * D / (a - q) - 1) / 2 + 1) =
          (a + q) * (3 * D / (2 * (a - q))) + (a + q) / 2 := by
      field_simp
      ring
    rw [hrewrite]
    have hmain :
        (27 / 14 : ℝ) * (E + K + C + q * (J : ℝ)) +
            (M + q) / 2 + (2 * C + 2 * q * (J : ℝ) + q) ≤
          2 * E - K - M * (J : ℝ) - C - q * (J : ℝ) := by
      nlinarith [hbudget]
    have hhalf : (a + q) / 2 ≤ (M + q) / 2 := by linarith
    linarith [hterm, hhalf, hb_lower, hmain]
  exact prefixCrossingLowerBridgeEventRandom_of_affine_original_envelope_of_ceil_window
    (X := X) E r J ω hJ hE hK hδ hM hME hr hgood hC hq hqδ hW hstrict
    hD_req hx hLscalar

/-! The pathwise event supplied by the Gaussian affine certificate.  Writing
the event explicitly is useful later: its complement can be bounded by the
integrable-intercept cutoff, while the early-slope part is handled separately.
-/
def prefixCrossingUniformBudgetEvent
    {Ω : Type*} (X : ℕ → Ω → ℝ) (_E _r : ℝ) (J : ℕ)
    (K δ M C q : ℝ) : Set Ω :=
  swingEarlySlopeGood X K δ M (J - 1) ∩
    gaussianNegativeCarryAffineEnvelopeEvent X (2 * q) C

theorem prefixCrossingUniformBudgetEvent_subset_bridge
    {Ω : Type*} {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ M C q : ℝ}
    (hJ : 1 ≤ J) (hE : 0 ≤ E) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hq : 0 ≤ q) (hqsmall : 8 * q ≤ δ)
    (hr : |r| ≤ K)
    (hbudget :
      41 * K + 69 * C + 69 * q * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * q ≤ E) :
    prefixCrossingUniformBudgetEvent X E r J K δ M C q ⊆
      prefixCrossingLowerBridgeEventRandom X E r J := by
  intro ω hω
  rcases hω with ⟨hgood, henv⟩
  apply prefixCrossingLowerBridgeEventRandom_of_affine_original_envelope_of_uniform_budget
    (X := X) E r J ω hJ hE hK hδ hM hr hgood (C := C) hC hq hqsmall ?_ hbudget
  intro n
  have h := henv n
  simpa [gaussianNegativeCarryAffineEnvelopeEvent] using h

theorem prefixCrossingUniformBudgetEvent_compl_measure_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ M C q α : ℝ}
    (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hJ : 1 ≤ J) (hE : 0 ≤ E) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hC : 0 < C) (hq : 0 < q) (hqsmall : 8 * q ≤ δ)
    (hr : |r| ≤ K)
    (hα : μ.real (swingEarlySlopeGood X K δ M (J - 1))ᶜ ≤ α)
    (hbudget :
      41 * K + 69 * C + 69 * q * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * q ≤ E) :
    μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤
      α +
        (∫ ω, gaussianNegativeCarryAffineIntercept X (2 * q) ω ∂μ) / C := by
  have hsubset := prefixCrossingUniformBudgetEvent_subset_bridge
    (X := X) E r J hJ hE hK hδ hM hC.le hq.le hqsmall hr hbudget
  have hbridge :
      μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤
        μ.real (prefixCrossingUniformBudgetEvent X E r J K δ M C q)ᶜ := by
    exact measureReal_mono
      (Set.compl_subset_compl.mpr hsubset) (measure_ne_top μ _)
  have hcut := gaussianNegativeCarryAffineEnvelopeEvent_intersection_compl_bound
    (μ := μ) (A := swingEarlySlopeGood X K δ M (J - 1))
    (α := α) hα hX hi hG (c := 2 * q) (R := C)
    (by positivity : 0 < (2 : ℝ) * q) hC
  change μ.real (prefixCrossingUniformBudgetEvent X E r J K δ M C q)ᶜ ≤
    α + (∫ ω, gaussianNegativeCarryAffineIntercept X (2 * q) ω ∂μ) / C at hcut
  exact hbridge.trans hcut

/-! The same estimate with the affine-envelope mass supplied directly.  This
version is useful when the cutoff radius is chosen by the preceding
existence lemma: it avoids throwing away the already-established event bound
in favour of the (usually less transparent) integral-over-radius expression.
-/
theorem prefixCrossingUniformBudgetEvent_compl_measure_le_of_envelope_compl
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ M C q α β : ℝ}
    (_hX : ∀ n, Measurable (X n))
    (hJ : 1 ≤ J) (hE : 0 ≤ E) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hq : 0 ≤ q) (hqsmall : 8 * q ≤ δ)
    (hr : |r| ≤ K)
    (hα : μ.real (swingEarlySlopeGood X K δ M (J - 1))ᶜ ≤ α)
    (hβ : μ.real (gaussianNegativeCarryAffineEnvelopeEvent X (2 * q) C)ᶜ ≤ β)
    (hbudget :
      41 * K + 69 * C + 69 * q * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * q ≤ E) :
    μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤ α + β := by
  have hsubset := prefixCrossingUniformBudgetEvent_subset_bridge
    (X := X) E r J hJ hE hK hδ hM hC hq hqsmall hr hbudget
  have hbridge :
      μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤
        μ.real (prefixCrossingUniformBudgetEvent X E r J K δ M C q)ᶜ := by
    exact measureReal_mono
      (Set.compl_subset_compl.mpr hsubset) (measure_ne_top μ _)
  let A : Set Ω := swingEarlySlopeGood X K δ M (J - 1)
  let B : Set Ω := gaussianNegativeCarryAffineEnvelopeEvent X (2 * q) C
  have hAB : μ.real (A ∩ B)ᶜ ≤ μ.real Aᶜ + μ.real Bᶜ := by
    have hsub : (A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ := by
      intro ω hω
      by_cases hAω : ω ∈ A
      · right
        intro hBω
        exact hω ⟨hAω, hBω⟩
      · left
        exact hAω
    calc
      μ.real (A ∩ B)ᶜ ≤ μ.real (Aᶜ ∪ Bᶜ) :=
        measureReal_mono hsub (measure_ne_top μ _)
      _ ≤ μ.real Aᶜ + μ.real Bᶜ := measureReal_union_le _ _
  have hident : prefixCrossingUniformBudgetEvent X E r J K δ M C q = A ∩ B := by
    rfl
  rw [hident] at hbridge
  calc
    μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤
        μ.real (A ∩ B)ᶜ := hbridge
    _ ≤ μ.real Aᶜ + μ.real Bᶜ := hAB
    _ ≤ α + β := by
      dsimp [A, B] at hα hβ ⊢
      linarith

end SwingRepair
