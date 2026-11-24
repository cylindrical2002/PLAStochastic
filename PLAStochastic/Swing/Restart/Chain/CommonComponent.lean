import PLAStochastic.Swing.Restart.Chain.ShortSegments

/-! # A uniform two-step common component for the actual restart kernel -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def nativeRestartPositiveInterval (E : ℝ) : Set ℝ := Icc (4*E+1) (4*E+2)
def nativeRestartNegativeInterval (E : ℝ) : Set ℝ := Icc (-(4*E+2)) (-(4*E+1))
def nativeRestartCommonInterval (E : ℝ) : Set ℝ := Icc (8*E+4) (8*E+5)

def nativeRestartCommonWeight (E : ℝ) : ℝ≥0∞ := (1/2) *
  min (gaussianReal 0 1 (nativeRestartPositiveInterval E))
    (gaussianReal 0 1 (nativeRestartNegativeInterval E))

private theorem gaussianReal_Icc_pos {a b : ℝ} (hab : a < b) :
    0 < gaussianReal 0 1 (Icc a b) := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num) hz
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero] at hv
  linarith

theorem nativeRestartCommonWeight_bounds (E : ℝ) :
    0 < nativeRestartCommonWeight E ∧ nativeRestartCommonWeight E ≤ 1/2 := by
  have hp : 0 < gaussianReal 0 1 (nativeRestartPositiveInterval E) :=
    gaussianReal_Icc_pos (by linarith)
  have hn : 0 < gaussianReal 0 1 (nativeRestartNegativeInterval E) :=
    gaussianReal_Icc_pos (by linarith)
  constructor
  · exact ENNReal.mul_pos (by norm_num) (lt_min hp hn).ne'
  · calc
      nativeRestartCommonWeight E ≤ (1/2 : ℝ≥0∞)*1 := by
        apply mul_le_mul_right
        exact (min_le_left _ _).trans (prob_le_one)
      _ = _ := mul_one _

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The two short segments are events of the original input, with no intervention. -/
theorem nativeRestartKernel_two_step_lower [SFinite μ]
    (hX : ∀ k, Measurable (X k)) (hG : μ.map (X 0) = gaussianReal 0 1)
    {E : ℝ} (hE : 0 < E) (x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    nativeRestartCommonWeight E * gaussianReal 0 1 (A ∩ nativeRestartCommonInterval E) ≤
      (nativeRestartKernel X μ E ∘ₖ nativeRestartKernel X μ E) x A := by
  let P := nativeRestartKernel X μ E
  let S : Set ℝ := if x ≤ 0 then nativeRestartPositiveInterval E
    else nativeRestartNegativeInterval E
  have hS : MeasurableSet S := by
    dsimp [S]
    split <;> exact measurableSet_Icc
  have hsep : ∀ y ∈ S, 3*E < |y-x| := by
    intro y hy
    dsimp [S] at hy
    split_ifs at hy with hx
    · have := hy.1
      exact lt_of_lt_of_le (by linarith : 3*E < y-x) (le_abs_self _)
    · have := hy.2
      exact lt_of_lt_of_le (by linarith : 3*E < -(y-x)) (neg_le_abs _)
  have hmass : nativeRestartCommonWeight E ≤ P x S := by
    have hbase : gaussianReal 0 1 S ≤ P x S := by
      have hh := nativeRestartKernel_one_step_lower hX hG hE.le x hS
      have heq : S ∩ {y | 3*E < |y-x|} = S :=
        inter_eq_left.mpr (fun y hy => hsep y hy)
      rwa [heq] at hh
    apply le_trans _ hbase
    have hhalf : (1/2 : ℝ≥0∞) ≤ 1 := by norm_num
    calc
      nativeRestartCommonWeight E ≤ min
          (gaussianReal 0 1 (nativeRestartPositiveInterval E))
          (gaussianReal 0 1 (nativeRestartNegativeInterval E)) := by
        exact (mul_le_mul_left hhalf _).trans_eq (one_mul _)
      _ ≤ _ := by dsimp [S]; split <;> simp
  have hnext : ∀ y ∈ S, gaussianReal 0 1 (A ∩ nativeRestartCommonInterval E) ≤ P y A := by
    intro y hy
    apply le_trans _ (nativeRestartKernel_one_step_lower hX hG hE.le y hA)
    apply measure_mono
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hzlo := hz.2.1
    dsimp [S] at hy
    split_ifs at hy <;>
      exact lt_of_lt_of_le (by linarith [hy.2] : 3*E < z-y) (le_abs_self _)
  rw [Kernel.comp_apply' _ _ _ hA]
  calc
    nativeRestartCommonWeight E * gaussianReal 0 1 (A ∩ nativeRestartCommonInterval E)
      ≤ gaussianReal 0 1 (A ∩ nativeRestartCommonInterval E) * P x S := by
        rw [mul_comm]
        exact mul_le_mul_right hmass _
    _ = ∫⁻ y in S, gaussianReal 0 1 (A ∩ nativeRestartCommonInterval E) ∂P x :=
      (setLIntegral_const _ _).symm
    _ = ∫⁻ y, S.indicator (fun _ => gaussianReal 0 1
          (A ∩ nativeRestartCommonInterval E)) y ∂P x :=
      (lintegral_indicator hS _).symm
    _ ≤ ∫⁻ y, P y A ∂P x := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ S
      · simpa only [indicator_of_mem hy] using hnext y hy
      · simp only [indicator_of_notMem hy]; exact zero_le

theorem nativeRestartKernel_two_step_common [IsProbabilityMeasure μ]
    (hX : ∀ k, Measurable (X k)) (hG : μ.map (X 0) = gaussianReal 0 1)
    {E : ℝ} (hE : 0 < E) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∃ α : ℝ≥0∞,
      0 < α ∧ α < 1 ∧ ∀ x,
        α • ν ≤ (nativeRestartKernel X μ E ∘ₖ nativeRestartKernel X μ E) x := by
  let q := gaussianReal 0 1 (nativeRestartCommonInterval E)
  have hq : 0 < q := gaussianReal_Icc_pos (by linarith)
  have hq1 : q ≤ 1 := prob_le_one
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hq1
  let ν := q⁻¹ • (gaussianReal 0 1).restrict (nativeRestartCommonInterval E)
  have hν : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hq.ne' hqtop
  refine ⟨ν, hν, nativeRestartCommonWeight E*q, ENNReal.mul_pos
    (nativeRestartCommonWeight_bounds E).1.ne' hq.ne', ?_, ?_⟩
  · calc
      nativeRestartCommonWeight E*q ≤ (1/2 : ℝ≥0∞)*1 :=
        mul_le_mul' (nativeRestartCommonWeight_bounds E).2 hq1
      _ < 1 := by norm_num
  · intro x
    apply Measure.le_iff.mpr
    intro A hA
    have heq : (nativeRestartCommonWeight E*q) • ν =
        nativeRestartCommonWeight E •
          (gaussianReal 0 1).restrict (nativeRestartCommonInterval E) := by
      rw [show ν = q⁻¹ • (gaussianReal 0 1).restrict (nativeRestartCommonInterval E) from rfl,
        smul_smul, mul_assoc, ENNReal.mul_inv_cancel hq.ne' hqtop, mul_one]
    rw [heq, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
    exact nativeRestartKernel_two_step_lower hX hG hE x hA

end SwingRepair
