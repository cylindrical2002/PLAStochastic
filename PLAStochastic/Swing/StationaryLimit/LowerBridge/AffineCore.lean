import PLAStochastic.Swing.StationaryLimit.LowerBridge.LocalizationCertificate
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.AffinePassageWindows
import PLAStochastic.Swing.StationaryLimit.LowerBridge.PathwiseCore

/-!
# An affine-envelope certificate for the random lower bridge

This is a deterministic refinement of `randomBridgeWindowCore`.  A global
partial-sum envelope plus two explicit passage-window inequalities produces
the crossing existence and passage index; a separate scalar inequality then
produces the least-squares bound.  Thus the three conditions are no longer
independent black-box fields.  The window inequalities are intentionally left
visible, since their uniform budget proof is a separate arithmetic/localization
task.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem leastSquares_bound_of_denominator_bound
    {E r Q η a : ℝ} {N : ℕ}
    (_hηa : η ≤ a) (hden : 0 < 2 * (N : ℝ) + 1)
    (hbound : 3 * (E-r+Q) ≤ (a-η) * (2 * (N : ℝ) + 1)) :
    3 * (E-r+Q) / (2 * (N : ℝ) + 1) + η ≤ a := by
  have hfrac : 3 * (E-r+Q) / (2 * (N : ℝ) + 1) ≤ a - η := by
    apply (div_le_iff₀ hden).2
    simpa [mul_comm] using hbound
  linarith

/-! A lower bound on the deterministic passage index is enough for the
least-squares side of the bridge.  This lemma isolates all denominator
monotonicity and leaves only one scalar inequality at the lower window index.
-/

omit [MeasurableSpace Ω] in
theorem leastSquares_bound_of_lower_passage_index
    {E r Q η a : ℝ} {J L k : ℕ}
    (_hJ : 1 ≤ J) (_hη : 0 ≤ η) (hηa : η ≤ a)
    (_hA : 0 ≤ E-r+Q) (hLk : L < k)
    (hbound : 3 * (E-r+Q) ≤
      (a-η) * (2 * ((J - 1 + L : ℕ) : ℝ) + 1)) :
    3 * (E-r+Q) / (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + η ≤ a := by
  have hNat : J - 1 + L ≤ J - 1 + k := by omega
  have hcast : (J - 1 + L : ℕ) ≤ (J - 1 + k : ℕ) := hNat
  have hdenL : 0 < 2 * ((J - 1 + L : ℕ) : ℝ) + 1 := by positivity
  have hdenK : 0 < 2 * ((J - 1 + k : ℕ) : ℝ) + 1 := by positivity
  have hdenle : 2 * ((J - 1 + L : ℕ) : ℝ) + 1 ≤
      2 * ((J - 1 + k : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show 2 * (J - 1 + L) + 1 ≤ 2 * (J - 1 + k) + 1 by omega)
  have hcoef : 0 ≤ a - η := sub_nonneg.mpr hηa
  have hnum : 3 * (E-r+Q) ≤
      (a-η) * (2 * ((J - 1 + k : ℕ) : ℝ) + 1) := by
    exact hbound.trans (mul_le_mul_of_nonneg_left hdenle hcoef)
  have hfrac : 3 * (E-r+Q) /
      (2 * ((J - 1 + k : ℕ) : ℝ) + 1) ≤ a - η := by
    apply (div_le_iff₀ hdenK).2
    simpa [mul_comm] using hnum
  linarith

/-! The crossing level itself can replace the lower-window inequality.  The
factor `7η ≤ a` is a transparent sufficient margin: it gives
`(3/4)(a+η) ≤ a-η`, hence a crossing above the level forces enough samples for
the least-squares denominator. -/

omit [MeasurableSpace Ω] in
theorem leastSquares_bound_of_crossing_level
    {Y : ℕ → Ω → ℝ} {E r Q η a b C : ℝ} {J k : ℕ} {ω : Ω}
    (_hJ : 1 ≤ J) (ha : 0 < a) (_hη : 0 ≤ η) (h7 : 7*η ≤ a)
    (_hA : 0 ≤ E-r+Q) (_hB : 0 ≤ b-C-η)
    (hcross : b < gaussianDriftWalk Y 0 a k ω)
    (hW : |cumulativeSamples Y k ω| ≤ C + η * ((k : ℝ) + 1))
    (hlevel : 3 * (E-r+Q) ≤
      (a-η) * (2 * ((J - 1 : ℕ) : ℝ) + 1) +
        (3/2 : ℝ) * (b-C-η)) :
    3 * (E-r+Q) /
        (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + η ≤ a := by
  have hAk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcross' : b <
      (a + η) * (k : ℝ) + C + η := by
    have hupp : cumulativeSamples Y k ω ≤ C + η * ((k : ℝ) + 1) :=
      (le_abs_self _).trans hW
    dsimp [gaussianDriftWalk] at hcross
    linarith
  have hBcross : b-C-η < (a+η) * (k : ℝ) := by linarith
  have hcoef : (3/4 : ℝ) * (a+η) ≤ a-η := by
    nlinarith
  have hscaled : (3/4 : ℝ) * (b-C-η) <
      (a-η) * (k : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hBcross (by norm_num : (0 : ℝ) < 3/4)
    have hcoefk := mul_le_mul_of_nonneg_right hcoef hAk
    nlinarith
  have hdouble : (3/2 : ℝ) * (b-C-η) <
      2 * (a-η) * (k : ℝ) := by nlinarith
  have hdenbound : 3 * (E-r+Q) ≤
      (a-η) * (2 * ((J - 1 + k : ℕ) : ℝ) + 1) := by
    have hcast : ((J - 1 + k : ℕ) : ℝ) =
        ((J - 1 : ℕ) : ℝ) + (k : ℝ) := by
      rw [Nat.cast_add]
    rw [hcast]
    have hbase : 0 ≤ a-η := by nlinarith
    nlinarith [hlevel, hdouble]
  exact leastSquares_bound_of_denominator_bound
    (by linarith : η ≤ a) (by positivity) hdenbound

omit [MeasurableSpace Ω] in
theorem randomBridgeWindowCore_of_affine_envelope
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    {K δ Q M η G : ℝ} {L U : ℕ}
    (hJ : 1 ≤ J) (hδ : 0 < δ) (_hE : 0 ≤ E)
    (hr : |r| ≤ K) (_hK : 0 ≤ K) (_hQ : 0 ≤ Q) (_hM : 0 ≤ M)
    (hη : 0 ≤ η) (hG : 0 ≤ G) (hGη : G ≤ η)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J-1))
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ G * ((n : ℝ) + 1))
    (hηa : η < prefixCrossingSlope X r J ω)
    (hlevel : 0 < prefixCrossingLevel X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hwindowL :
      (prefixCrossingSlope X r J ω + η) * (L : ℝ) +
          G * (2 * (J : ℝ) - 1) + η ≤ prefixCrossingLevel X E r J ω)
    (hwindowU :
      prefixCrossingLevel X E r J ω <
        (prefixCrossingSlope X r J ω - η) * (U : ℝ) -
          G * (2 * (J : ℝ) - 1) - η)
    (hLS : ∀ k : ℕ, L < k →
      3 * (E-r+Q) / (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + η ≤
        prefixCrossingSlope X r J ω) :
    ω ∈ randomBridgeWindowCore (X := X) E r J η Q := by
  have hbounds := prefixCrossingSlope_bounds_of_earlySlopeGood
    (X := X) (r := r) (K := K) (δ := δ) (M := M)
    (J := J) ω hJ hδ hgood hr
  have ha : 0 < prefixCrossingSlope X r J ω :=
    prefixCrossingSlope_pos_of_earlySlopeGood ω hJ hδ hgood hr
  have hpassage := gaussianWalkPassage_window_neg_shift_of_global_envelope
    (X := X) (J := J) (a := prefixCrossingSlope X r J ω)
    (b := prefixCrossingLevel X E r J ω) (G := G) (η := η) (ω := ω)
    hJ hG hGη hW hη hηa hwindowL hwindowU
  rcases hpassage with ⟨hcross, hLpass, _hpassU⟩
  let k : ℕ := gaussianWalkPassage
    (negIncrements (fun q => X (J - 1 + q)))
    (prefixCrossingSlope X r J ω)
    (prefixCrossingLevel X E r J ω) ω
  have hk : L < k := by
    exact hLpass
  have hN : 1 ≤ J - 1 + k := by omega
  have hWglobal : ∀ i ∈ Finset.Icc 1 (J - 1 + k),
      |cumulativeSamples X (i-1) ω| ≤ Q + η * (i : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hWi := hW (i-1)
    have hcast : ((i-1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ i)]
      norm_num
    rw [hcast] at hWi
    have hmul : G * (i : ℝ) ≤ η * (i : ℝ) :=
      mul_le_mul_of_nonneg_right hGη (Nat.cast_nonneg i)
    linarith
  have hls := hLS k hk
  refine ⟨k, hN, hWglobal, hls, ha, hlevel, haE, hcross, ?_⟩
  rfl

/-! A scalar lower-window inequality is the only least-squares input needed
by the preceding certificate. -/

omit [MeasurableSpace Ω] in
theorem randomBridgeWindowCore_of_affine_envelope_of_lower_window
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    {K δ Q M η G : ℝ} {L U : ℕ}
    (hJ : 1 ≤ J) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hr : |r| ≤ K) (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hη : 0 ≤ η) (hG : 0 ≤ G) (hGη : G ≤ η)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J-1))
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ G * ((n : ℝ) + 1))
    (hηa : η < prefixCrossingSlope X r J ω)
    (hlevel : 0 < prefixCrossingLevel X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hwindowL :
      (prefixCrossingSlope X r J ω + η) * (L : ℝ) +
          G * (2 * (J : ℝ) - 1) + η ≤ prefixCrossingLevel X E r J ω)
    (hwindowU :
      prefixCrossingLevel X E r J ω <
        (prefixCrossingSlope X r J ω - η) * (U : ℝ) -
          G * (2 * (J : ℝ) - 1) - η)
    (hA : 0 ≤ E-r+Q)
    (hbound : 3 * (E-r+Q) ≤
      (prefixCrossingSlope X r J ω - η) *
        (2 * ((J - 1 + L : ℕ) : ℝ) + 1)) :
    ω ∈ randomBridgeWindowCore (X := X) E r J η Q := by
  apply randomBridgeWindowCore_of_affine_envelope E r J ω hJ hδ hE hr hK hQ hM
    hη hG hGη hgood hW hηa hlevel haE hwindowL hwindowU
  intro k hk
  exact leastSquares_bound_of_lower_passage_index
    hJ hη (le_of_lt hηa) hA hk hbound

/-! The same core with an affine original envelope.  This is the interface
used by the two-sided exponential carry certificate: the finite intercept is
preserved through the shifted reflected walk, while the requested passage
slope `η` may dominate the original slope `q`. -/

omit [MeasurableSpace Ω] in
theorem randomBridgeWindowCore_of_affine_original_envelope
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    {K δ Q M η C q : ℝ} {L U : ℕ}
    (hJ : 1 ≤ J) (hδ : 0 < δ) (_hE : 0 ≤ E)
    (hr : |r| ≤ K) (_hK : 0 ≤ K) (_hQ : 0 ≤ Q) (_hM : 0 ≤ M)
    (hη : 0 ≤ η) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hCQ : C ≤ Q) (hqη : q ≤ η)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J-1))
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1))
    (hηa : η < prefixCrossingSlope X r J ω)
    (hlevel : 0 < prefixCrossingLevel X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hwindowL :
      (prefixCrossingSlope X r J ω + η) * (L : ℝ) +
          2 * C + 2 * q * (J : ℝ) + η ≤ prefixCrossingLevel X E r J ω)
    (hwindowU :
      prefixCrossingLevel X E r J ω <
        (prefixCrossingSlope X r J ω - η) * (U : ℝ) -
          2 * C - 2 * q * (J : ℝ) - η)
    (hLS : ∀ k : ℕ, L < k →
      3 * (E-r+Q) / (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + η ≤
        prefixCrossingSlope X r J ω) :
    ω ∈ randomBridgeWindowCore (X := X) E r J η Q := by
  have hshift : ∀ n : ℕ,
      |cumulativeSamples (negIncrements (fun j => X (J - 1 + j))) n ω| ≤
        (2 * C + 2 * q * (J : ℝ)) + η * ((n : ℝ) + 1) := by
    intro n
    have hs := shiftedNegIncrements_affine_envelope_of_affine
      (X := X) (J := J) (C := C) (q := q) (ω := ω) hJ hC hq hW n
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    have hrel : q * ((n : ℝ) + 1) ≤ η * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hqη hn
    exact hs.trans (by nlinarith)
  have hCshift : 0 ≤ 2 * C + 2 * q * (J : ℝ) := by positivity
  have hwindowL' :
      (prefixCrossingSlope X r J ω + η) * (L : ℝ) +
          (2 * C + 2 * q * (J : ℝ)) + η ≤ prefixCrossingLevel X E r J ω := by
    linarith [hwindowL]
  have hwindowU' :
      prefixCrossingLevel X E r J ω <
        (prefixCrossingSlope X r J ω - η) * (U : ℝ) -
          (2 * C + 2 * q * (J : ℝ)) - η := by
    linarith [hwindowU]
  have hpassage := gaussianWalkPassage_window_of_affine_envelope
    (Y := negIncrements (fun j => X (J - 1 + j)))
    (a := prefixCrossingSlope X r J ω)
    (b := prefixCrossingLevel X E r J ω)
    (C := 2 * C + 2 * q * (J : ℝ)) (η := η) (ω := ω)
    (L := L) (U := U)
    (by exact le_of_lt (prefixCrossingSlope_pos_of_earlySlopeGood
      ω hJ hδ hgood hr)) hCshift hη hηa hshift hwindowL' hwindowU'
  rcases hpassage with ⟨hcross, hLpass, _hU⟩
  let k : ℕ := gaussianWalkPassage
    (negIncrements (fun j => X (J - 1 + j)))
    (prefixCrossingSlope X r J ω)
    (prefixCrossingLevel X E r J ω) ω
  have hk : L < k := by exact hLpass
  have hN : 1 ≤ J - 1 + k := by omega
  have hWglobal : ∀ i ∈ Finset.Icc 1 (J - 1 + k),
      |cumulativeSamples X (i-1) ω| ≤ Q + η * (i : ℝ) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hWi := hW (i-1)
    have hcast : ((i-1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ i)]
      norm_num
    rw [hcast] at hWi
    have hiq : q * (i : ℝ) ≤ η * (i : ℝ) :=
      mul_le_mul_of_nonneg_right hqη (Nat.cast_nonneg i)
    linarith
  have hls := hLS k hk
  refine ⟨k, hN, hWglobal, hls,
    prefixCrossingSlope_pos_of_earlySlopeGood ω hJ hδ hgood hr,
    hlevel, haE, hcross, ?_⟩
  rfl

omit [MeasurableSpace Ω] in
theorem randomBridgeWindowCore_of_affine_original_envelope_of_lower_window
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    {K δ Q M η C q : ℝ} {L U : ℕ}
    (hJ : 1 ≤ J) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hr : |r| ≤ K) (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hη : 0 ≤ η) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hCQ : C ≤ Q) (hqη : q ≤ η)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J-1))
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1))
    (hηa : η < prefixCrossingSlope X r J ω)
    (hlevel : 0 < prefixCrossingLevel X E r J ω)
    (haE : prefixCrossingSlope X r J ω ≤ E)
    (hwindowL :
      (prefixCrossingSlope X r J ω + η) * (L : ℝ) +
          2 * C + 2 * q * (J : ℝ) + η ≤ prefixCrossingLevel X E r J ω)
    (hwindowU :
      prefixCrossingLevel X E r J ω <
        (prefixCrossingSlope X r J ω - η) * (U : ℝ) -
          2 * C - 2 * q * (J : ℝ) - η)
    (hA : 0 ≤ E-r+Q)
    (hbound : 3 * (E-r+Q) ≤
      (prefixCrossingSlope X r J ω - η) *
        (2 * ((J - 1 + L : ℕ) : ℝ) + 1)) :
    ω ∈ randomBridgeWindowCore (X := X) E r J η Q := by
  apply randomBridgeWindowCore_of_affine_original_envelope E r J ω hJ hδ hE
    hr hK hQ hM hη hC hq hCQ hqη hgood hW hηa hlevel haE hwindowL hwindowU
  intro k hk
  exact leastSquares_bound_of_lower_passage_index
    hJ hη (le_of_lt hηa) hA hk hbound

end SwingRepair
