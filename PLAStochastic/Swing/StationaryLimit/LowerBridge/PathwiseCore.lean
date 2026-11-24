import PLAStochastic.Swing.StationaryLimit.LowerBridge.LocalizationCertificate
import PLAStochastic.Swing.Restart.Chain.FreshWalkEnvelope
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.AffinePassageWindows

/-!
# Pathwise lower-bridge core

This file turns the global Gaussian envelope into the exact affine envelope
needed by the shifted reflected walk.  It also packages the deterministic
consequences (positive level, automatic least-squares bound, and a first
passage window) into one theorem.  The window and selector inequalities are
kept as explicit scalar hypotheses; no probability or uniform-in-parameter
claim is made here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! A global envelope for the original walk gives an affine envelope for the
shifted reflected walk.  The intercept `2*G*J` records the finite prefix and
is not discarded. -/
omit mΩ in
theorem shiftedNegIncrements_affine_envelope
    {X : ℕ → Ω → ℝ} {J : ℕ} {G : ℝ} {ω : Ω}
    (hJ : 1 ≤ J) (hG : 0 ≤ G)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ G * ((n : ℝ) + 1)) :
    ∀ n : ℕ,
      |cumulativeSamples (negIncrements (fun q => X (J - 1 + q))) n ω| ≤
        2 * G * (J : ℝ) + G * ((n : ℝ) + 1) := by
  intro n
  have hshift := cumulativeSamples_shifted_succ X J n hJ ω
  rw [cumulativeSamples_neg]
  have hshift' :
      cumulativeSamples (fun q => X (J - 1 + q)) n ω =
        cumulativeSamples X (J - 1 + n) ω - cumulativeSamples X (J - 1) ω := by
    linarith [hshift]
  rw [hshift']
  rw [abs_neg]
  have hleft := hW (J - 1 + n)
  have hright := hW (J - 1)
  have habs :
      |cumulativeSamples X (J - 1 + n) ω - cumulativeSamples X (J - 1) ω| ≤
        |cumulativeSamples X (J - 1 + n) ω| +
          |cumulativeSamples X (J - 1) ω| := by
    exact abs_sub _ _
  have hcast₁ : ((J - 1 + n : ℕ) : ℝ) + 1 =
      (J : ℝ) + (n : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hJ]
    push_cast
    ring
  have hcast₂ : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
    rw [Nat.cast_sub hJ]
    push_cast
    ring
  rw [hcast₁] at hleft
  rw [hcast₂] at hright
  have hsum :
      |cumulativeSamples X (J - 1 + n) ω| +
          |cumulativeSamples X (J - 1) ω| ≤
        G * ((J : ℝ) + (n : ℝ)) + G * (J : ℝ) :=
    add_le_add hleft hright
  have hnonneg_n : 0 ≤ (n : ℝ) := by positivity
  have htarget :
      G * ((J : ℝ) + (n : ℝ)) + G * (J : ℝ) ≤
        2 * G * (J : ℝ) + G * ((n : ℝ) + 1) := by
    nlinarith
  exact habs.trans (hsum.trans htarget)

/-! The same shift calculation for an affine (rather than purely linear)
original envelope.  This is the form supplied by the two-sided exponential
carry certificate: the slope `q` is preserved and only the finite-prefix
intercept changes. -/
omit mΩ in
theorem shiftedNegIncrements_affine_envelope_of_affine
    {X : ℕ → Ω → ℝ} {J : ℕ} {C q : ℝ} {ω : Ω}
    (hJ : 1 ≤ J) (_hC : 0 ≤ C) (hq : 0 ≤ q)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1)) :
    ∀ n : ℕ,
      |cumulativeSamples (negIncrements (fun r => X (J - 1 + r))) n ω| ≤
        2 * C + 2 * q * (J : ℝ) + q * ((n : ℝ) + 1) := by
  intro n
  rw [cumulativeSamples_neg]
  have hshift := cumulativeSamples_shifted_succ X J n hJ ω
  have hshift' :
      cumulativeSamples (fun r => X (J - 1 + r)) n ω =
        cumulativeSamples X (J - 1 + n) ω - cumulativeSamples X (J - 1) ω := by
    linarith [hshift]
  rw [hshift', abs_neg]
  have htri := abs_sub (cumulativeSamples X (J - 1 + n) ω)
    (cumulativeSamples X (J - 1) ω)
  have h1 := hW (J - 1 + n)
  have h2 := hW (J - 1)
  have hcast1 : ((J - 1 + n : ℕ) : ℝ) + 1 =
      (J : ℝ) + (n : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hJ]
    push_cast
    ring
  have hcast2 : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
    rw [Nat.cast_sub hJ]
    push_cast
    ring
  rw [hcast1] at h1
  rw [hcast2] at h2
  have hsum :
      |cumulativeSamples X (J - 1 + n) ω| +
        |cumulativeSamples X (J - 1) ω| ≤
      (C + q * ((J : ℝ) + (n : ℝ))) +
        (C + q * (J : ℝ)) := add_le_add h1 h2
  have hn : 0 ≤ (n : ℝ) := by positivity
  have htarget :
      (C + q * ((J : ℝ) + (n : ℝ))) +
        (C + q * (J : ℝ)) ≤
      2 * C + 2 * q * (J : ℝ) + q * ((n : ℝ) + 1) := by
    nlinarith
  exact htri.trans (hsum.trans htarget)

omit mΩ in
theorem cumulativeSamples_global_envelope_Icc
    {X : ℕ → Ω → ℝ} {N : ℕ} {G Q η : ℝ} {ω : Ω}
    (hG : 0 ≤ G) (hQ : 0 ≤ Q)
    (hGQ : G ≤ η) (hQprefix : G * (N : ℝ) ≤ Q)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ G * ((n : ℝ) + 1)) :
    ∀ i ∈ Finset.Icc 1 N,
      |cumulativeSamples X (i - 1) ω| ≤ Q + η * (i : ℝ) := by
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hiN : i ≤ N := (Finset.mem_Icc.mp hi).2
  have hWi := hW (i - 1)
  have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
    rw [Nat.cast_sub hi1]
    norm_num
  rw [hcast] at hWi
  have hiR : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hiN
  have hGi : G * (i : ℝ) ≤ Q := by
    exact (mul_le_mul_of_nonneg_left hiR hG).trans hQprefix
  have hGη : G * (i : ℝ) ≤ η * (i : ℝ) :=
    mul_le_mul_of_nonneg_right hGQ (Nat.cast_nonneg i)
  linarith

omit mΩ in
theorem prefixCrossing_level_pos_of_strict_global_budget
    {X : ℕ → Ω → ℝ} {E r K M G : ℝ} {J : ℕ} {ω : Ω}
    (hJ : 1 ≤ J) (hr : |r| ≤ K) (hA : prefixCrossingSlope X r J ω ≤ M)
    (_hG : 0 ≤ G)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ G * ((n : ℝ) + 1))
    (hstrict : M * (J : ℝ) + K + G * (J : ℝ) < 2 * E) :
    0 < prefixCrossingLevel X E r J ω := by
  have hJcast : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
    rw [Nat.cast_sub hJ]
    push_cast
    ring
  have hWJ := hW (J - 1)
  rw [hJcast] at hWJ
  have hlow : -G * (J : ℝ) ≤ cumulativeSamples X (J - 1) ω := by
    have := neg_le_abs (cumulativeSamples X (J - 1) ω)
    linarith
  have hr' : r ≤ K := by
    have := le_abs_self r
    linarith
  dsimp [prefixCrossingLevel]
  nlinarith

/-! The main pathwise core.  `L` and `U` are arbitrary candidate passage
window endpoints.  `hselector` is the one scalar inequality needed to turn
the lower endpoint `L` into the least-squares threshold; it is precisely the
remaining arithmetic check in a concrete localization proof. -/
omit [MeasurableSpace Ω] in
theorem prefixCrossingLowerBridgeEventRandom_of_global_envelope
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    {K δ M G q : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hME : M ≤ E)
    (hr : |r| ≤ K)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J - 1))
    (hG : 0 ≤ G) (hGq : G ≤ q) (hqδ : q < δ)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ G * ((n : ℝ) + 1))
    (hstrict : M * (J : ℝ) + K + q * (J : ℝ) < 2 * E)
    {L U : ℕ} (hLpos : 1 ≤ L)
    (hwindowL :
      (prefixCrossingSlope X r J ω + q) * (L : ℝ) +
          2 * G * (J : ℝ) + q ≤ prefixCrossingLevel X E r J ω)
    (hwindowU :
      prefixCrossingLevel X E r J ω <
        (prefixCrossingSlope X r J ω - q) * (U : ℝ) -
          2 * G * (J : ℝ) - q)
    (hselector :
      3 * (E - r + q * (J : ℝ)) ≤
        (prefixCrossingSlope X r J ω - q) * (2 * (L : ℝ) + 1)) :
    ω ∈ prefixCrossingLowerBridgeEventRandom X E r J := by
  have hq : 0 ≤ q := le_trans hG hGq
  have hbounds := prefixCrossingSlope_bounds_of_earlySlopeGood
    (X := X) (r := r) (K := K) (δ := δ) (M := M) ω hJ hδ hgood hr
  have ha_lower : δ ≤ prefixCrossingSlope X r J ω := hbounds.1
  have haE0 : prefixCrossingSlope X r J ω ≤ M := hbounds.2
  have ha : 0 < prefixCrossingSlope X r J ω := lt_of_lt_of_le hδ ha_lower
  have hqa : q < prefixCrossingSlope X r J ω := lt_of_lt_of_le hqδ ha_lower
  have hqale : q ≤ prefixCrossingSlope X r J ω := hqa.le
  have hb : 0 < prefixCrossingLevel X E r J ω :=
    prefixCrossing_level_pos_of_strict_global_budget hJ hr haE0 hG hW
      (by
        have hqG : G ≤ q := hGq
        nlinarith)
  have hbudget : M * (J : ℝ) ≤ 2 * E - K - q * (J : ℝ) := by
    nlinarith
  have hprefix_env :
      ∀ i ∈ Finset.Icc 1 (J - 1),
        |cumulativeSamples X (i - 1) ω| ≤ q * (J : ℝ) + q * (i : ℝ) := by
    have hGprefix : G * (J : ℝ) ≤ q * (J : ℝ) :=
      mul_le_mul_of_nonneg_right hGq (Nat.cast_nonneg J)
    have hJminus : ((J - 1 : ℕ) : ℝ) ≤ (J : ℝ) := by
      exact_mod_cast (Nat.sub_le J 1)
    have hGprefix' : G * ((J - 1 : ℕ) : ℝ) ≤ q * (J : ℝ) := by
      exact (mul_le_mul_of_nonneg_left hJminus hG).trans hGprefix
    have hqJ : 0 ≤ q * (J : ℝ) := mul_nonneg hq (Nat.cast_nonneg J)
    apply cumulativeSamples_global_envelope_Icc
      (N := J - 1) (Q := q * (J : ℝ)) (η := q)
      hG hqJ hGq hGprefix' hW
  have hNwindow :
      ∀ n : ℕ,
        |cumulativeSamples (negIncrements (fun q' => X (J - 1 + q'))) n ω| ≤
          2 * G * (J : ℝ) + q * ((n : ℝ) + 1) := by
    intro n
    exact (shiftedNegIncrements_affine_envelope hJ hG hW n).trans
      (by
        have hn : 0 ≤ (n : ℝ) + 1 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hGq hn])
  have hwindow := gaussianWalkPassage_window_of_affine_envelope
    (Y := negIncrements (fun q' => X (J - 1 + q')))
    (a := prefixCrossingSlope X r J ω)
    (b := prefixCrossingLevel X E r J ω) (η := q) (C := 2 * G * (J : ℝ))
    ha.le (by positivity) hq hqa hNwindow hwindowL hwindowU
  let k := gaussianWalkPassage
    (negIncrements (fun q' => X (J - 1 + q'))) 
      (prefixCrossingSlope X r J ω) (prefixCrossingLevel X E r J ω) ω
  have hk_lower : L < k := by
    dsimp [k]
    exact hwindow.2.1
  have hk_upper : k ≤ U := by
    dsimp [k]
    exact hwindow.2.2
  have hN : 1 ≤ J - 1 + k := by omega
  have hWglobal :
      ∀ i ∈ Finset.Icc 1 (J - 1 + k),
        |cumulativeSamples X (i - 1) ω| ≤ q * (J : ℝ) + q * (i : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hWi := hW (i - 1)
    have hcast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      rw [Nat.cast_sub hi1]
      norm_num
    rw [hcast] at hWi
    have hGi : G * (i : ℝ) ≤ q * (i : ℝ) :=
      mul_le_mul_of_nonneg_right hGq (Nat.cast_nonneg i)
    have hqJ : 0 ≤ q * (J : ℝ) := mul_nonneg hq (Nat.cast_nonneg J)
    linarith
  have hLN : L ≤ J - 1 + k := by omega
  have hlsbound :
      3 * (E-r+q * (J : ℝ)) /
          (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + q ≤
        prefixCrossingSlope X r J ω := by
    exact leastSquares_threshold_of_lower_index hqale hselector hLN
  have hcross : ∃ m : ℕ,
      prefixCrossingLevel X E r J ω <
        gaussianDriftWalk
          (negIncrements (fun q' => X (J - 1 + q'))) 0
          (prefixCrossingSlope X r J ω) m ω := hwindow.1
  have hpass : gaussianWalkPassage
      (negIncrements (fun q' => X (J - 1 + q')))
      (prefixCrossingSlope X r J ω)
      (prefixCrossingLevel X E r J ω) ω = k := by rfl
  have hqJ : 0 ≤ q * (J : ℝ) := mul_nonneg hq (Nat.cast_nonneg J)
  have hprefix_bound :
      ∀ i ∈ Finset.Icc 1 (J - 1),
        |cumulativeSamples X (i - 1) ω| ≤ q * (J : ℝ) := by
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
    have hGi : G * (i : ℝ) ≤ q * (J : ℝ) := by
      exact (mul_le_mul_of_nonneg_left hiR hG).trans
        (mul_le_mul_of_nonneg_right hGq (Nat.cast_nonneg J))
    linarith
  exact prefixCrossingLowerBridgeEventRandom_of_envelopes
    (X := X) E r J k ω hJ hE hN
    (K := K) (Q := q * (J : ℝ)) (M := M) (η := q)
    hr hK hqJ hM hq haE0 hprefix_bound hbudget hWglobal hlsbound
    (by
      intro i hi
      exact prefixCrossing_lower_future_of_earlySlopeGood_unbounded
        (X := X) (E := E) (r := r) (K := K) (δ := δ) (M := M)
        (J := J) ω hJ hδ hgood hr i (Finset.mem_Icc.mp hi).1)
    (prefixCrossingSlope_attained_lower_cone (X := X) (E := E) (r := r)
      hJ ω)
    ha hb (le_trans haE0 hME) hcross hpass

end SwingRepair
