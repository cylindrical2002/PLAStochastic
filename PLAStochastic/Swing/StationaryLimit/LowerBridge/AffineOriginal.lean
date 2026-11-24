import PLAStochastic.Swing.StationaryLimit.LowerBridge.PathwiseCore
import PLAStochastic.Swing.StationaryLimit.LowerBridge.AffineCore

/-!
# Lower bridge from an affine envelope of the original walk

The Gaussian carry certificate supplies a pathwise bound of the form
`|W n| ≤ C + q (n+1)`, with a finite (random) intercept `C`.  This file
pushes that bound through the prefix-crossing construction.  All constants
which arise from the finite prefix are displayed explicitly; the theorem is
pathwise and does not assert that the scalar window hypotheses hold with high
probability.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
theorem prefixCrossing_level_pos_of_strict_affine_budget
    {X : ℕ → Ω → ℝ} {E r K M C q : ℝ} {J : ℕ} {ω : Ω}
    (hJ : 1 ≤ J) (hr : |r| ≤ K)
    (hA : prefixCrossingSlope X r J ω ≤ M)
    (_hC : 0 ≤ C) (_hq : 0 ≤ q)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1))
    (hstrict : M * (J : ℝ) + K + C + q * (J : ℝ) < 2 * E) :
    0 < prefixCrossingLevel X E r J ω := by
  have hJcast : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
    rw [Nat.cast_sub hJ]
    push_cast
    ring
  have hWJ := hW (J - 1)
  rw [hJcast] at hWJ
  have hlow : -(C + q * (J : ℝ)) ≤ cumulativeSamples X (J - 1) ω := by
    have := neg_le_abs (cumulativeSamples X (J - 1) ω)
    linarith
  have hr' : r ≤ K := by
    have := le_abs_self r
    linarith
  dsimp [prefixCrossingLevel]
  nlinarith

/-! The main affine-envelope bridge.  We use `Q = C + q J` for the finite
prefix budget and `2 C + 2 q J` for the reflected future intercept. -/
omit [MeasurableSpace Ω] in
theorem prefixCrossingLowerBridgeEventRandom_of_affine_original_envelope
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    {K δ M C q : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hME : M ≤ E)
    (hr : |r| ≤ K)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J - 1))
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hqδ : q < δ)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1))
    (hstrict : M * (J : ℝ) + K + C + q * (J : ℝ) < 2 * E)
    {L U : ℕ} (_hLpos : 1 ≤ L)
    (hwindowL :
      (prefixCrossingSlope X r J ω + q) * (L : ℝ) +
          (2 * C + 2 * q * (J : ℝ)) + q ≤
        prefixCrossingLevel X E r J ω)
    (hwindowU :
      prefixCrossingLevel X E r J ω <
        (prefixCrossingSlope X r J ω - q) * (U : ℝ) -
          (2 * C + 2 * q * (J : ℝ)) - q)
    (hselector :
      3 * (E - r + (C + q * (J : ℝ))) ≤
        (prefixCrossingSlope X r J ω - q) * (2 * (L : ℝ) + 1)) :
    ω ∈ prefixCrossingLowerBridgeEventRandom X E r J := by
  let Q : ℝ := C + q * (J : ℝ)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hbounds := prefixCrossingSlope_bounds_of_earlySlopeGood
    (X := X) (r := r) (K := K) (δ := δ) (M := M) ω hJ hδ hgood hr
  have ha_lower : δ ≤ prefixCrossingSlope X r J ω := hbounds.1
  have haE0 : prefixCrossingSlope X r J ω ≤ M := hbounds.2
  have ha : 0 < prefixCrossingSlope X r J ω := lt_of_lt_of_le hδ ha_lower
  have hqa : q < prefixCrossingSlope X r J ω := lt_of_lt_of_le hqδ ha_lower
  have hqale : q ≤ prefixCrossingSlope X r J ω := hqa.le
  have hb : 0 < prefixCrossingLevel X E r J ω :=
    prefixCrossing_level_pos_of_strict_affine_budget hJ hr haE0 hC hq hW hstrict
  have hbudget : M * (J : ℝ) ≤ 2 * E - K - Q := by
    dsimp [Q]
    nlinarith
  have hprefix_env :
      ∀ i ∈ Finset.Icc 1 (J - 1),
        |cumulativeSamples X (i - 1) ω| ≤ Q + q * (i : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hiJm : i ≤ J - 1 := (Finset.mem_Icc.mp hi).2
    have hiJ : i ≤ J := by omega
    have hWi := hW (i - 1)
    have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      rw [Nat.cast_sub hi1]
      norm_num
    rw [hcast] at hWi
    have hiR : (i : ℝ) ≤ (J : ℝ) := by exact_mod_cast hiJ
    have hqJ : 0 ≤ q * (J : ℝ) := mul_nonneg hq (Nat.cast_nonneg J)
    dsimp [Q]
    exact hWi.trans (by linarith)
  have hprefix_bound :
      ∀ i ∈ Finset.Icc 1 (J - 1),
        |cumulativeSamples X (i - 1) ω| ≤ Q := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hiJm : i ≤ J - 1 := (Finset.mem_Icc.mp hi).2
    have hiJ : i ≤ J := by omega
    have hWi := hW (i - 1)
    have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      rw [Nat.cast_sub hi1]
      norm_num
    rw [hcast] at hWi
    have hiR : (i : ℝ) ≤ (J : ℝ) := by exact_mod_cast hiJ
    have hqJ : 0 ≤ q * (J : ℝ) := mul_nonneg hq (Nat.cast_nonneg J)
    have hqmono : q * (i : ℝ) ≤ q * (J : ℝ) :=
      mul_le_mul_of_nonneg_left hiR hq
    dsimp [Q]
    linarith
  have hNwindow :
      ∀ n : ℕ,
        |cumulativeSamples
            (negIncrements (fun q' => X (J - 1 + q'))) n ω| ≤
          (2 * C + 2 * q * (J : ℝ)) + q * ((n : ℝ) + 1) := by
    intro n
    exact shiftedNegIncrements_affine_envelope_of_affine
      hJ hC hq hW n
  have hwindow := gaussianWalkPassage_window_of_affine_envelope
    (Y := negIncrements (fun q' => X (J - 1 + q')))
    (a := prefixCrossingSlope X r J ω)
    (b := prefixCrossingLevel X E r J ω)
    (η := q) (C := 2 * C + 2 * q * (J : ℝ)) (ω := ω)
    ha.le (by positivity) hq hqa hNwindow hwindowL hwindowU
  let k := gaussianWalkPassage
    (negIncrements (fun q' => X (J - 1 + q')))
      (prefixCrossingSlope X r J ω)
      (prefixCrossingLevel X E r J ω) ω
  have hk_lower : L < k := hwindow.2.1
  have hN : 1 ≤ J - 1 + k := by omega
  have hWglobal :
      ∀ i ∈ Finset.Icc 1 (J - 1 + k),
        |cumulativeSamples X (i - 1) ω| ≤ Q + q * (i : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hWi := hW (i - 1)
    have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      rw [Nat.cast_sub hi1]
      norm_num
    rw [hcast] at hWi
    have hqJ : 0 ≤ q * (J : ℝ) := mul_nonneg hq (Nat.cast_nonneg J)
    dsimp [Q]
    linarith
  have hlsbound :
      3 * (E-r+Q) /
          (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + q ≤
        prefixCrossingSlope X r J ω := by
    exact leastSquares_threshold_of_lower_index hqale hselector
      (by omega : L ≤ J - 1 + k)
  have hcross : ∃ m : ℕ,
      prefixCrossingLevel X E r J ω <
        gaussianDriftWalk
          (negIncrements (fun q' => X (J - 1 + q'))) 0
          (prefixCrossingSlope X r J ω) m ω := hwindow.1
  have hpass : gaussianWalkPassage
      (negIncrements (fun q' => X (J - 1 + q')))
      (prefixCrossingSlope X r J ω)
      (prefixCrossingLevel X E r J ω) ω = k := by rfl
  exact prefixCrossingLowerBridgeEventRandom_of_envelopes
    (X := X) E r J k ω hJ hE hN hr hK hQ hM hq haE0
    hprefix_bound hbudget hWglobal hlsbound
    (by
      intro i hi
      exact prefixCrossing_lower_future_of_earlySlopeGood_unbounded
        (X := X) (E := E) (r := r) (K := K) (δ := δ) (M := M)
        (J := J) ω hJ hδ hgood hr i (Finset.mem_Icc.mp hi).1)
    (prefixCrossingSlope_attained_lower_cone (X := X) (E := E) (r := r)
      hJ ω)
    ha hb (le_trans haE0 hME) hcross hpass

end SwingRepair
