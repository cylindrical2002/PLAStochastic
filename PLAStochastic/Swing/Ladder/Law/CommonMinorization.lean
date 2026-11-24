import PLAStochastic.Swing.Ladder.Law.CompactTail

/-!
# A concrete Gaussian component of the positive-drift ladder law

A positive first increment of the drifted walk crosses immediately.  This
event gives a subprobability measure inside the actual ladder-height law,
and hence a common Lebesgue density component on bounded drift intervals.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

theorem gaussianAscendingLadderTime_first_step {a : ℝ} {ω : Ω}
    (hfirst : 0 < a + X 0 ω) :
    gaussianAscendingLadderTime X a ω = (1 : ℕ) := by
  apply (gaussianHalfLineExit_eq_succ_iff (fun n ω => -X n ω) 0 (-a) 0 ω).mpr
  constructor
  · intro j hj
    have hj0 : j = 0 := by omega
    simp [hj0, gaussianDriftWalk]
  · change gaussianDriftWalk (fun n ω => -X n ω) 0 (-a) 1 ω < 0
    rw [gaussianDriftWalk_reflect_neg_drift]
    simp only [gaussianDriftWalk, cumulativeSamples, Finset.sum_range_one,
      Nat.cast_one, mul_one, zero_add]
    linarith

theorem gaussianAscendingLadderHeight_first_step {a : ℝ} {ω : Ω}
    (hfirst : 0 < a + X 0 ω) :
    gaussianAscendingLadderHeight X a ω = a + X 0 ω := by
  have hT := gaussianAscendingLadderTime_first_step hfirst
  have hfinite : gaussianAscendingLadderTime X a ω ≠ ⊤ := by
    rw [hT]
    exact WithTop.coe_ne_top
  rw [gaussianAscendingLadderHeight_eq_position hfinite]
  have hindex : (gaussianAscendingLadderTime X a ω).untopD 0 = 1 := by rw [hT]; rfl
  rw [hindex]
  simp [gaussianDriftWalk, cumulativeSamples, add_comm]

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- The entire positive first-step Gaussian density is contained in the
actual strict ascending ladder law. -/
theorem gaussianAscendingLadderLaw_first_step_minorization
    (hX : ∀ n, Measurable (X n)) (hG : μ.map (X 0) = gaussianReal 0 1) (a : ℝ) :
    (gaussianReal a 1).restrict (Ioi 0) ≤ gaussianAscendingLadderLaw X μ a := by
  have hmap : μ.map (fun ω => a + X 0 ω) = gaussianReal a 1 := by
    rw [show (fun ω => a + X 0 ω) = (fun z : ℝ => a+z) ∘ X 0 from rfl,
      ← Measure.map_map (by fun_prop) (hX 0), hG, gaussianReal_map_const_add, zero_add]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, ← hmap,
    Measure.map_apply (by fun_prop) (hA.inter measurableSet_Ioi),
    gaussianAscendingLadderLaw,
    Measure.map_apply (gaussianAscendingLadderHeight_measurable hX a) hA]
  apply measure_mono
  intro ω hω
  change a + X 0 ω ∈ A ∧ 0 < a + X 0 ω at hω
  change gaussianAscendingLadderHeight X a ω ∈ A
  rw [gaussianAscendingLadderHeight_first_step hω.2]
  exact hω.1

def gaussianAscendingLadderCommonDensity (M : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (M+2)

theorem gaussianAscendingLadderCommonDensity_pos (M : ℝ) :
    0 < gaussianAscendingLadderCommonDensity M :=
  gaussianPDFReal_pos 0 1 (M+2) (by norm_num)

theorem gaussianAscendingLadderCommonDensity_le
    {a M y : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) (hy : y ∈ Icc (1 : ℝ) 2) :
    gaussianAscendingLadderCommonDensity M ≤ gaussianPDFReal a 1 y := by
  have hM : 0 ≤ M := ha.trans haM
  have hsq : (y-a)^2 ≤ (M+2)^2 := by
    have hlow : -(M+2) ≤ y-a := by linarith [hy.1]
    have hhigh : y-a ≤ M+2 := by linarith [hy.2]
    nlinarith
  simp only [gaussianAscendingLadderCommonDensity, gaussianPDFReal,
    NNReal.coe_one, sub_zero, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  linarith

/-- All drifts in `[0,M]` have the same strictly positive Lebesgue density
component on `[1,2]`. -/
theorem gaussianAscendingLadderLaw_common_minorization
    (hX : ∀ n, Measurable (X n)) (hG : μ.map (X 0) = gaussianReal 0 1)
    {a M : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) :
    ENNReal.ofReal (gaussianAscendingLadderCommonDensity M) •
      (volume.restrict (Icc (1 : ℝ) 2)) ≤ gaussianAscendingLadderLaw X μ a := by
  have hgauss : ENNReal.ofReal (gaussianAscendingLadderCommonDensity M) •
      (volume.restrict (Icc (1 : ℝ) 2)) ≤ (gaussianReal a 1).restrict (Icc (1 : ℝ) 2) := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
      Measure.restrict_apply hA, gaussianReal_apply _ (by norm_num)]
    have hbound : (∫⁻ _y : ℝ in A ∩ Icc (1 : ℝ) 2,
        ENNReal.ofReal (gaussianAscendingLadderCommonDensity M)) ≤
        ∫⁻ y : ℝ in A ∩ Icc (1 : ℝ) 2, gaussianPDF a 1 y := by
      apply setLIntegral_mono' (hA.inter measurableSet_Icc)
      intro y hy
      exact ENNReal.ofReal_le_ofReal (gaussianAscendingLadderCommonDensity_le ha haM hy.2)
    simpa only [setLIntegral_const] using hbound
  have hrestrict : (gaussianReal a 1).restrict (Icc (1 : ℝ) 2) ≤
      (gaussianReal a 1).restrict (Ioi 0) := by
    apply Measure.restrict_mono
    · intro y hy
      exact lt_of_lt_of_le (by norm_num) hy.1
    · exact le_rfl
  exact hgauss.trans (hrestrict.trans (gaussianAscendingLadderLaw_first_step_minorization hX hG a))

end SwingRepair
