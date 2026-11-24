import PLAStochastic.Swing.Gaussian.ZeroLadder.StrictLadderLaw

/-!
# The actual strict ascending ladder law for positive Gaussian drift

The first ladder time is defined through reflection of the existing half-line
exit.  The pathwise identification below keeps the positive-drift walk and its
strict first crossing explicit.  No renewal expansion is assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

def gaussianAscendingLadderTime (X : ℕ → Ω → ℝ) (a : ℝ) : Ω → WithTop ℕ :=
  gaussianHalfLineExit (fun n ω => -X n ω) 0 (-a)

def gaussianAscendingLadderHeight (X : ℕ → Ω → ℝ) (a : ℝ) : Ω → ℝ :=
  gaussianHalfLineOvershoot (fun n ω => -X n ω) 0 (-a)

theorem gaussianDriftWalk_reflect_neg_drift (a : ℝ) (n : ℕ) (ω : Ω) :
    gaussianDriftWalk (fun n ω => -X n ω) 0 (-a) n ω =
      -gaussianDriftWalk X 0 a n ω := by
  simp [gaussianDriftWalk, cumulativeSamples, Finset.sum_neg_distrib]
  ring

theorem gaussianAscendingLadderTime_eq_hittingAfter (a : ℝ) (ω : Ω) :
    gaussianAscendingLadderTime X a ω =
      hittingAfter (gaussianDriftWalk X 0 a) (Ioi 0) 0 ω := by
  simp only [gaussianAscendingLadderTime, gaussianHalfLineExit, hittingAfter,
    gaussianDriftWalk_reflect_neg_drift, mem_Iio, neg_lt_zero, mem_Ioi]

theorem gaussianAscendingLadderTime_pos (a : ℝ) (ω : Ω) :
    (0 : WithTop ℕ) < gaussianAscendingLadderTime X a ω := by
  apply (lt_gaussianHalfLineExit_iff _ _ _ 0 ω).mpr
  intro j hj
  have hj0 : j = 0 := by omega
  simp [hj0, gaussianDriftWalk]

theorem gaussianAscendingLadderHeight_eq_position {a : ℝ} {ω : Ω}
    (hT : gaussianAscendingLadderTime X a ω ≠ ⊤) :
    gaussianAscendingLadderHeight X a ω =
      gaussianDriftWalk X 0 a ((gaussianAscendingLadderTime X a ω).untopD 0) ω := by
  dsimp only [gaussianAscendingLadderTime] at hT
  unfold gaussianAscendingLadderHeight gaussianHalfLineOvershoot
  rw [if_neg hT]
  unfold gaussianHalfLineExitPosition
  rw [gaussianDriftWalk_reflect_neg_drift, neg_neg]
  rfl

theorem gaussianAscendingLadderHeight_nonneg (a : ℝ) (ω : Ω) :
    0 ≤ gaussianAscendingLadderHeight X a ω :=
  gaussianHalfLineOvershoot_nonneg _ 0 (-a) ω

theorem gaussianAscendingLadderHeight_pos_of_finite {a : ℝ} {ω : Ω}
    (hT : gaussianAscendingLadderTime X a ω ≠ ⊤) :
    0 < gaussianAscendingLadderHeight X a ω := by
  dsimp only [gaussianAscendingLadderTime] at hT
  unfold gaussianAscendingLadderHeight gaussianHalfLineOvershoot
  rw [if_neg hT]
  exact neg_pos.mpr (gaussianHalfLineExitPosition_neg hT)

variable [MeasurableSpace Ω] {μ : Measure Ω}

def gaussianAscendingLadderLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) : Measure ℝ :=
  μ.map (gaussianAscendingLadderHeight X a)

theorem gaussianAscendingLadderTime_measurable
    (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    Measurable (gaussianAscendingLadderTime X a) :=
  (gaussianHalfLineExit_isStoppingTime (fun n => (hX n).neg) 0 (-a)).measurable'

theorem gaussianAscendingLadderHeight_measurable
    (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    Measurable (gaussianAscendingLadderHeight X a) :=
  gaussianHalfLineOvershoot_measurable (fun n => (hX n).neg) 0 (-a)

theorem gaussianAscendingLadderLaw_isProbabilityMeasure
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (a : ℝ) :
    IsProbabilityMeasure (gaussianAscendingLadderLaw X μ a) := by
  have := hi.isProbabilityMeasure
  exact Measure.isProbabilityMeasure_map
    (gaussianAscendingLadderHeight_measurable hX a).aemeasurable

theorem gaussianAscendingLadderTime_finite_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, gaussianAscendingLadderTime X a ω ≠ ⊤ := by
  filter_upwards [gaussianDriftWalk_strongLaw hX hi hG 0 a] with ω hω
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < gaussianDriftWalk X 0 a n ω / (n : ℝ) :=
    hω.eventually (Ioi_mem_nhds ha)
  obtain ⟨n, hn, hp⟩ := (eventually_ge_atTop 1 |>.and hpositive).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpos : 0 < gaussianDriftWalk X 0 a n ω :=
    (div_pos_iff_of_pos_right hn0).mp hp
  rw [gaussianAscendingLadderTime_eq_hittingAfter]
  exact ne_top_of_le_ne_top WithTop.coe_ne_top
    (hittingAfter_le_of_mem (Nat.zero_le n) hpos)

theorem gaussianAscendingLadderHeight_positive_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂μ, 0 < gaussianAscendingLadderHeight X a ω :=
  (gaussianAscendingLadderTime_finite_ae hX hi hG ha).mono
    (fun _ hT => gaussianAscendingLadderHeight_pos_of_finite hT)

theorem gaussianAscendingLadderLaw_positive_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ u ∂gaussianAscendingLadderLaw X μ a, 0 < u := by
  rw [gaussianAscendingLadderLaw,
    ae_map_iff (gaussianAscendingLadderHeight_measurable hX a).aemeasurable measurableSet_Ioi]
  exact gaussianAscendingLadderHeight_positive_ae hX hi hG ha

theorem gaussianAscendingLadderLaw_eq_canonical
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (a : ℝ) :
    gaussianAscendingLadderLaw X μ a =
      gaussianAscendingLadderLaw (fun n (w : ℕ → ℝ) => w n)
        (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) a := by
  have hp : μ.map (fun ω n => X n ω) =
      Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) := by
    rw [hi.map_fun_eq_infinitePi_map hX]
    simp_rw [hG]
  have hheight := gaussianAscendingLadderHeight_measurable
    (fun n => measurable_pi_apply n) a
  unfold gaussianAscendingLadderLaw
  rw [← hp, Measure.map_map hheight (measurable_pi_lambda _ hX)]
  rfl

end SwingRepair
