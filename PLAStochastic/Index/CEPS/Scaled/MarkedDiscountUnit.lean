import PLAStochastic.Index.CEPS.Normal.ZeroMarkedDiscount
import PLAStochastic.ForMathlib.Analysis.Complex.SimpleZeroUnit

/-! # A class-controlled unit after removing the marked discount zero -/

noncomputable section
open Complex MeasureTheory Set Metric
open PGM.WienerHopf
namespace PGM

def cepsMarkedDiscountBound (D θ : ℝ) : ℝ :=
  1 + Real.exp (θ / 2) * (2 + 128 * D / θ)

def cepsMarkedUnitRadius (D θ : ℝ) : ℝ :=
  simpleZeroUnitRadius (θ / 2) (cepsMarkedDiscountBound D θ)

def cepsMarkedDiscountUnit (ρW : Measure ℝ) : ℂ → ℂ := dslope (cepsMarkedDiscount ρW) 0

theorem cepsMarkedDiscountBound_pos {D θ : ℝ} (hD : 0 < D) (hθ : 0 < θ) :
    0 < cepsMarkedDiscountBound D θ := by unfold cepsMarkedDiscountBound; positivity

theorem cepsMarkedUnitRadius_pos {D θ : ℝ} (hD : 0 < D) (hθ : 0 < θ) :
    0 < cepsMarkedUnitRadius D θ :=
  simpleZeroUnitRadius_pos (half_pos hθ) (cepsMarkedDiscountBound_pos hD hθ)

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMarkedDiscount_ball_budget :
    DifferentiableOn ℂ (cepsMarkedDiscount ρW) (ball 0 (θ / 2)) ∧
    ∀ t ∈ ball (0 : ℂ) (θ / 2), ‖cepsMarkedDiscount ρW t‖ ≤ cepsMarkedDiscountBound D θ := by
  refine ⟨(differentiableOn_const (1 : ℂ)).sub
    ((differentiableOn_id.neg.cexp).mul (differentiableOn_stepTransform_ball hW hθ hD.le)), ?_⟩
  intro t ht
  have ht' := mem_ball_zero_iff.mp ht
  have hE : ‖exp (-t)‖ ≤ Real.exp (θ / 2) := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr ((re_le_norm (-t)).trans (by simpa only [norm_neg] using ht'.le))
  have hM := norm_stepTransform_le_strip hW hθ hD.le ((abs_re_le_norm t).trans ht'.le)
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖exp (-t) * stepTransform ρW t‖ := norm_sub_le _ _
    _ ≤ cepsMarkedDiscountBound D θ := by
      rw [norm_one, norm_mul]
      exact add_le_add le_rfl (mul_le_mul hE hM (norm_nonneg _) (Real.exp_pos _).le)

include hW hθ hD in
theorem cepsMarkedDiscountUnit_zero : cepsMarkedDiscountUnit ρW 0 = 1 := by
  rw [cepsMarkedDiscountUnit, dslope_same, (cepsMarkedDiscount_zero_jets hW hθ hD).2.1]

include hW hθ hD in
theorem cepsMarkedDiscountUnit_eq_div {t : ℂ} (ht : t ≠ 0) :
    cepsMarkedDiscountUnit ρW t = cepsMarkedDiscount ρW t / t := by
  rw [cepsMarkedDiscountUnit, dslope_of_ne _ ht, slope_def_field,
    (cepsMarkedDiscount_zero_jets hW hθ hD).1, sub_zero, sub_zero]

include hW hθ hD in
theorem cepsMarkedDiscountUnit_budget :
    DifferentiableOn ℂ (cepsMarkedDiscountUnit ρW) (ball 0 (cepsMarkedUnitRadius D θ)) ∧
    (∀ t ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ),
      ‖cepsMarkedDiscountUnit ρW t‖ ≤ cepsMarkedDiscountBound D θ / (θ / 2)) ∧
    DifferentiableOn ℂ (fun t => (cepsMarkedDiscountUnit ρW t)⁻¹)
      (ball 0 (cepsMarkedUnitRadius D θ)) ∧
    (∀ t ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ),
      1 / 2 ≤ ‖cepsMarkedDiscountUnit ρW t‖ ∧ ‖(cepsMarkedDiscountUnit ρW t)⁻¹‖ ≤ 2) := by
  obtain ⟨hd, hb⟩ := cepsMarkedDiscount_ball_budget hW hθ hD
  obtain ⟨hf0, hdf, _⟩ := cepsMarkedDiscount_zero_jets hW hθ hD
  obtain ⟨hu, hbu, _⟩ := simpleZeroUnit_budget (half_pos hθ)
    (cepsMarkedDiscountBound_pos hD hθ) hd hf0 hdf hb
  obtain ⟨hi, hbi⟩ := simpleZeroUnit_inverse_budget (half_pos hθ)
    (cepsMarkedDiscountBound_pos hD hθ) hd hf0 hdf hb
  have hsub : ball (0 : ℂ) (cepsMarkedUnitRadius D θ) ⊆ ball 0 (θ / 2) :=
    ball_subset_ball ((min_le_left _ _).trans (half_le_self (half_pos hθ).le))
  exact ⟨hu.mono hsub, fun t ht => hbu t (hsub ht), hi, hbi⟩

end PGM
