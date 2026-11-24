import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.PassageWindows
import PLAStochastic.Swing.Restart.MaximalPrefix.ObservedHistory
import PLAStochastic.Swing.FirstSegment.LowerRejectionReflection

/-!
# First-passage windows with an affine partial-sum envelope

The original passage-window lemma assumes a pure linear bound
`|W n| ≤ η (n+1)`.  A global Gaussian envelope naturally gives a finite
head plus a linear tail, so this file records the corresponding deterministic
variant with an explicit intercept `C`.  No probability or asymptotic claim is
used here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

omit mΩ in
theorem gaussianWalkPassage_window_of_affine_envelope
    {Y : ℕ → Ω → ℝ} {a b C η : ℝ} {ω : Ω}
    (_ha : 0 ≤ a) (_hC : 0 ≤ C) (hη : 0 ≤ η) (_hηa : η < a)
    (henv : ∀ n : ℕ,
      |cumulativeSamples Y n ω| ≤ C + η * ((n : ℝ) + 1))
    {L U : ℕ}
    (hL : (a + η) * (L : ℝ) + C + η ≤ b)
    (hU : b < (a - η) * (U : ℝ) - C - η) :
    (∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω) ∧
      L < gaussianWalkPassage Y a b ω ∧
        gaussianWalkPassage Y a b ω ≤ U := by
  have hcross : ∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω := by
    refine ⟨U, ?_⟩
    have henvU := henv U
    have hlow : -(C + η * ((U : ℝ) + 1)) ≤ cumulativeSamples Y U ω := by
      have habs := neg_le_abs (cumulativeSamples Y U ω)
      linarith
    dsimp [gaussianDriftWalk]
    linarith
  have hbelow : ∀ j ≤ L, gaussianDriftWalk Y 0 a j ω ≤ b := by
    intro j hj
    have henvj := henv j
    have hlow : -(C + η * ((j : ℝ) + 1)) ≤ cumulativeSamples Y j ω := by
      have habs := neg_le_abs (cumulativeSamples Y j ω)
      linarith
    have hjcast : (j : ℝ) ≤ (L : ℝ) := by exact_mod_cast hj
    dsimp [gaussianDriftWalk]
    have hcoef : 0 ≤ a + η := by linarith
    have hmul : (a + η) * (j : ℝ) ≤ (a + η) * (L : ℝ) :=
      mul_le_mul_of_nonneg_left hjcast hcoef
    have hLj : (a + η) * (j : ℝ) + C + η ≤ b := by
      linarith [hL, hmul]
    have hupp : cumulativeSamples Y j ω ≤ C + η * ((j : ℝ) + 1) :=
      (le_abs_self _).trans henvj
    have hwalk : gaussianDriftWalk Y 0 a j ω =
        cumulativeSamples Y j ω + a * (j : ℝ) := by
      simp [gaussianDriftWalk]
    linarith [hupp, hLj]
  refine ⟨hcross, ?_, ?_⟩
  · exact gaussianWalkPassage_gt_of_prefix_le hcross hbelow
  · apply gaussianWalkPassage_le_of_crossing hcross
    have henvU := henv U
    have hlow : -(C + η * ((U : ℝ) + 1)) ≤ cumulativeSamples Y U ω := by
      have habs := neg_le_abs (cumulativeSamples Y U ω)
      linarith
    dsimp [gaussianDriftWalk]
    linarith

omit mΩ in
theorem gaussianWalkPassage_exists_of_affine_envelope
    {Y : ℕ → Ω → ℝ} {a b C η : ℝ} {ω : Ω}
    (_ha : 0 ≤ a) (_hC : 0 ≤ C) (_hη : 0 ≤ η) (hηa : η < a)
    (henv : ∀ n : ℕ,
      |cumulativeSamples Y n ω| ≤ C + η * ((n : ℝ) + 1)) :
    ∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω := by
  have hpos : 0 < a - η := sub_pos.mpr hηa
  obtain ⟨U, hU⟩ := exists_nat_gt ((b + C + η) / (a - η))
  refine ⟨U, ?_⟩
  have henvU := henv U
  have hlow : -(C + η * ((U : ℝ) + 1)) ≤ cumulativeSamples Y U ω := by
    have habs := neg_le_abs (cumulativeSamples Y U ω)
    linarith
  dsimp [gaussianDriftWalk]
  have hcast : (b + C + η) / (a - η) < (U : ℝ) := by
    exact_mod_cast hU
  have hmul' := (div_lt_iff₀ hpos).mp hcast
  have hmul : b + C + η < (a - η) * (U : ℝ) := by
    nlinarith [hmul']
  linarith

omit mΩ in
theorem shifted_cumulativeSamples_abs_le_of_global_envelope
    {X : ℕ → Ω → ℝ} {G : ℝ} {J : ℕ} {ω : Ω}
    (hJ : 1 ≤ J) (_hG : 0 ≤ G) (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ G * ((n : ℝ) + 1))
    (m : ℕ) :
    |cumulativeSamples (fun q => X (J - 1 + q)) m ω| ≤
      G * ((m : ℝ) + 2 * (J : ℝ)) := by
  have hshift0 := cumulativeSamples_add_shift X (J - 1) m ω
  have hshift : cumulativeSamples (fun q => X (J - 1 + q)) m ω =
      cumulativeSamples X (J - 1 + m) ω - cumulativeSamples X (J - 1) ω := by
    linarith [hshift0]
  rw [hshift]
  have htri := abs_sub (cumulativeSamples X (J - 1 + m) ω)
    (cumulativeSamples X (J - 1) ω)
  have h1 := hW (J - 1 + m)
  have h2 := hW (J - 1)
  have hcast1 : ((J - 1 + m : ℕ) : ℝ) + 1 =
      (m : ℝ) + (J : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ J)]
    push_cast
    ring
  have hcast2 : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ J)]
    norm_num
  rw [hcast1] at h1
  rw [hcast2] at h2
  have hsum :
      |cumulativeSamples X (J - 1 + m) ω| +
        |cumulativeSamples X (J - 1) ω| ≤
      G * ((m : ℝ) + (J : ℝ)) + G * (J : ℝ) :=
    add_le_add h1 h2
  rw [show G * ((m : ℝ) + (J : ℝ)) + G * (J : ℝ) =
      G * ((m : ℝ) + 2 * (J : ℝ)) by ring] at hsum
  exact htri.trans hsum

/-! The reflected future walk used by the lower bridge is covered by the same
global envelope.  The finite prefix contributes the explicit intercept
`G * (2J-1)`. -/

omit mΩ in
theorem gaussianWalkPassage_window_neg_shift_of_global_envelope
    {X : ℕ → Ω → ℝ} {J : ℕ} {a b G η : ℝ} {ω : Ω}
    (hJ : 1 ≤ J) (hG : 0 ≤ G) (hGη : G ≤ η)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ G * ((n : ℝ) + 1))
    (hη : 0 ≤ η) (hηa : η < a)
    {L U : ℕ}
    (hL : (a + η) * (L : ℝ) + G * (2 * (J : ℝ) - 1) + η ≤ b)
    (hU : b < (a - η) * (U : ℝ) - G * (2 * (J : ℝ) - 1) - η) :
    (∃ m : ℕ, b < gaussianDriftWalk
        (negIncrements (fun q => X (J - 1 + q))) 0 a m ω) ∧
      L < gaussianWalkPassage
        (negIncrements (fun q => X (J - 1 + q))) a b ω ∧
        gaussianWalkPassage
          (negIncrements (fun q => X (J - 1 + q))) a b ω ≤ U := by
  have henv : ∀ m : ℕ,
      |cumulativeSamples (negIncrements (fun q => X (J - 1 + q))) m ω| ≤
        G * (2 * (J : ℝ) - 1) + η * ((m : ℝ) + 1) := by
    intro m
    have hs := shifted_cumulativeSamples_abs_le_of_global_envelope hJ hG hW m
    simp only [cumulativeSamples_neg, abs_neg] at hs ⊢
    have hηG : G * ((m : ℝ) + 2 * (J : ℝ)) ≤
        G * (2 * (J : ℝ) - 1) + η * ((m : ℝ) + 1) := by
      have hm : 0 ≤ (m : ℝ) + 1 := by positivity
      have hηG' : G * ((m : ℝ) + 1) ≤ η * ((m : ℝ) + 1) := by
        -- The wrapper is useful when the supplied affine slope dominates the
        -- global envelope; callers can choose `η = G` for the sharp form.
        exact mul_le_mul_of_nonneg_right hGη hm
      nlinarith [hηG']
    exact hs.trans hηG
  have hC : 0 ≤ G * (2 * (J : ℝ) - 1) := by
    apply mul_nonneg hG
    have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  exact gaussianWalkPassage_window_of_affine_envelope
    (a := a) (b := b) (C := G * (2 * (J : ℝ) - 1))
    (η := η) (ω := ω) (by linarith) hC hη hηa henv hL hU

end SwingRepair
