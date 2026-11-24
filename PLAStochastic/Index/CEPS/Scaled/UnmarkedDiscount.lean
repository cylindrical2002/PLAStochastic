import PLAStochastic.ForMathlib.Analysis.Complex.SimpleZeroUnit
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc

/-! # The unmarked scaled discount and its invertible unit at scale zero -/

noncomputable section
open Complex Set Metric
namespace PGM

def cepsUnmarkedDiscount (q : ℂ) : ℂ := 1 - exp (-q)
def cepsUnmarkedDiscountUnit (q : ℂ) : ℂ := dslope cepsUnmarkedDiscount 0 q

def cepsUnmarkedUnitRadius : ℝ := simpleZeroUnitRadius 1 (1 + Real.exp 1)

def cepsUnmarkedScaleRadius (z : ℂ) : ℝ := min 1 cepsUnmarkedUnitRadius / (1 + ‖z‖)

def cepsScaledUnmarkedUnit (z b : ℂ) : ℂ := cepsUnmarkedDiscountUnit (b ^ 2 * z)
def cepsScaledUnmarkedDiscount (z b : ℂ) : ℂ := z * cepsScaledUnmarkedUnit z b

theorem cepsUnmarkedDiscount_zero_jets :
    cepsUnmarkedDiscount 0 = 0 ∧ deriv cepsUnmarkedDiscount 0 = 1 := by
  constructor
  · simp [cepsUnmarkedDiscount]
  · have h := (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub
      (((hasDerivAt_id' (0 : ℂ)).neg).cexp)
    convert! h.deriv using 1
    simp

theorem cepsUnmarkedDiscountUnit_zero : cepsUnmarkedDiscountUnit 0 = 1 := by
  rw [cepsUnmarkedDiscountUnit, dslope_same, cepsUnmarkedDiscount_zero_jets.2]

theorem cepsUnmarkedDiscountUnit_eq_div {q : ℂ} (hq : q ≠ 0) :
    cepsUnmarkedDiscountUnit q = cepsUnmarkedDiscount q / q := by
  rw [cepsUnmarkedDiscountUnit, dslope_of_ne _ hq, slope_def_field,
    cepsUnmarkedDiscount_zero_jets.1, sub_zero, sub_zero]

theorem cepsUnmarkedUnitRadius_pos : 0 < cepsUnmarkedUnitRadius := by
  unfold cepsUnmarkedUnitRadius simpleZeroUnitRadius
  positivity

theorem cepsUnmarkedScaleRadius_pos (z : ℂ) : 0 < cepsUnmarkedScaleRadius z :=
  div_pos (lt_min zero_lt_one cepsUnmarkedUnitRadius_pos) (by positivity)

theorem cepsUnmarkedDiscount_budget :
    DifferentiableOn ℂ cepsUnmarkedDiscount (ball 0 1) ∧
      ∀ q ∈ ball (0 : ℂ) 1, ‖cepsUnmarkedDiscount q‖ ≤ 1 + Real.exp 1 := by
  refine ⟨by unfold cepsUnmarkedDiscount; fun_prop, fun q hq => ?_⟩
  have hn : ‖q‖ < 1 := mem_ball_zero_iff.mp hq
  calc
    ‖cepsUnmarkedDiscount q‖ ≤ ‖(1 : ℂ)‖ + ‖exp (-q)‖ := norm_sub_le _ _
    _ ≤ 1 + Real.exp 1 := by
      rw [norm_one, norm_exp]
      have h := (re_le_norm (-q)).trans (by simpa only [norm_neg] using hn.le)
      have he := Real.exp_le_exp.mpr h
      linarith

theorem cepsUnmarkedDiscountUnit_budget :
    DifferentiableOn ℂ cepsUnmarkedDiscountUnit (ball 0 cepsUnmarkedUnitRadius) ∧
    (∀ q ∈ ball (0 : ℂ) cepsUnmarkedUnitRadius, ‖cepsUnmarkedDiscountUnit q‖ ≤ 1 + Real.exp 1) ∧
    DifferentiableOn ℂ (fun q => (cepsUnmarkedDiscountUnit q)⁻¹) (ball 0 cepsUnmarkedUnitRadius) ∧
    (∀ q ∈ ball (0 : ℂ) cepsUnmarkedUnitRadius,
      1 / 2 ≤ ‖cepsUnmarkedDiscountUnit q‖ ∧ ‖(cepsUnmarkedDiscountUnit q)⁻¹‖ ≤ 2) := by
  obtain ⟨hd, hb⟩ := cepsUnmarkedDiscount_budget
  obtain ⟨hu, hm, _⟩ := simpleZeroUnit_budget (by norm_num : (0 : ℝ) < 1)
    (by positivity : (0 : ℝ) < 1 + Real.exp 1) hd
    cepsUnmarkedDiscount_zero_jets.1 cepsUnmarkedDiscount_zero_jets.2 hb
  obtain ⟨hi, hbi⟩ := simpleZeroUnit_inverse_budget (by norm_num : (0 : ℝ) < 1)
    (by positivity : (0 : ℝ) < 1 + Real.exp 1) hd
    cepsUnmarkedDiscount_zero_jets.1 cepsUnmarkedDiscount_zero_jets.2 hb
  have hsub : ball (0 : ℂ) cepsUnmarkedUnitRadius ⊆ ball 0 1 := by
    apply ball_subset_ball
    exact (min_le_left _ _).trans (by norm_num : (1 : ℝ) / 2 ≤ 1)
  exact ⟨hu.mono hsub, fun q hq => by
    change ‖dslope cepsUnmarkedDiscount 0 q‖ ≤ _
    simpa only [div_one] using hm q (hsub hq), hi, hbi⟩

theorem cepsUnmarkedScale_mapsTo (z : ℂ) :
    MapsTo (fun b : ℂ => b ^ 2 * z) (ball 0 (cepsUnmarkedScaleRadius z))
      (ball 0 cepsUnmarkedUnitRadius) := by
  intro b hb
  have hn := mem_ball_zero_iff.mp hb
  have hm : ‖b‖ * (1 + ‖z‖) < min 1 cepsUnmarkedUnitRadius :=
    (lt_div_iff₀ (by positivity : 0 < 1 + ‖z‖)).mp hn
  have hb1 : ‖b‖ ≤ 1 := by nlinarith [min_le_left 1 cepsUnmarkedUnitRadius, norm_nonneg z]
  rw [mem_ball, dist_zero_right, norm_mul, norm_pow]
  calc
    ‖b‖ ^ 2 * ‖z‖ ≤ ‖b‖ * (1 + ‖z‖) := by
      have := mul_le_mul_of_nonneg_right hb1 (mul_nonneg (norm_nonneg b) (norm_nonneg z))
      nlinarith [norm_nonneg b]
    _ < min 1 cepsUnmarkedUnitRadius := hm
    _ ≤ cepsUnmarkedUnitRadius := min_le_right _ _

theorem cepsScaledUnmarkedDiscount_zero (z : ℂ) : cepsScaledUnmarkedDiscount z 0 = z := by
  simp [cepsScaledUnmarkedDiscount, cepsScaledUnmarkedUnit, cepsUnmarkedDiscountUnit_zero]

theorem cepsScaledUnmarkedDiscount_eq_div (z : ℂ) {b : ℂ} (hb : b ≠ 0) :
    cepsScaledUnmarkedDiscount z b = (1 - exp (-b ^ 2 * z)) / b ^ 2 := by
  by_cases hz : z = 0
  · simp [hz, cepsScaledUnmarkedDiscount]
  · rw [cepsScaledUnmarkedDiscount, cepsScaledUnmarkedUnit,
      cepsUnmarkedDiscountUnit_eq_div (mul_ne_zero (pow_ne_zero _ hb) hz), cepsUnmarkedDiscount]
    field_simp

theorem cepsScaledUnmarkedUnit_budget (z : ℂ) :
    DifferentiableOn ℂ (cepsScaledUnmarkedUnit z) (ball 0 (cepsUnmarkedScaleRadius z)) ∧
    (∀ b ∈ ball (0 : ℂ) (cepsUnmarkedScaleRadius z), ‖cepsScaledUnmarkedUnit z b‖ ≤ 1 + Real.exp 1) ∧
    DifferentiableOn ℂ (fun b => (cepsScaledUnmarkedUnit z b)⁻¹) (ball 0 (cepsUnmarkedScaleRadius z)) ∧
    (∀ b ∈ ball (0 : ℂ) (cepsUnmarkedScaleRadius z),
      1 / 2 ≤ ‖cepsScaledUnmarkedUnit z b‖ ∧ ‖(cepsScaledUnmarkedUnit z b)⁻¹‖ ≤ 2) := by
  obtain ⟨hd, hm, hi, hbi⟩ := cepsUnmarkedDiscountUnit_budget
  have hg : DifferentiableOn ℂ (fun b : ℂ => b ^ 2 * z) (ball 0 (cepsUnmarkedScaleRadius z)) :=
    (differentiableOn_id.pow 2).mul_const z
  exact ⟨hd.comp hg (cepsUnmarkedScale_mapsTo z), fun b hb => hm _ (cepsUnmarkedScale_mapsTo z hb),
    hi.comp hg (cepsUnmarkedScale_mapsTo z), fun b hb => hbi _ (cepsUnmarkedScale_mapsTo z hb)⟩

theorem cepsScaledUnmarkedUnit_inverse_taylor_le (z : ℂ) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (cepsUnmarkedScaleRadius z / 2)) :
    ‖(cepsScaledUnmarkedUnit z b)⁻¹ -
      complexTaylorSum (fun b => (cepsScaledUnmarkedUnit z b)⁻¹) n 0 b‖ ≤
        ((n.factorial : ℝ) * 2 / (cepsUnmarkedScaleRadius z / 4) ^ n) * ‖b‖ ^ n := by
  obtain ⟨_, _, hi, hbi⟩ := cepsScaledUnmarkedUnit_budget z
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (cepsUnmarkedScaleRadius_pos z) hi (fun b hb => (hbi b hb).2) hb

end PGM
