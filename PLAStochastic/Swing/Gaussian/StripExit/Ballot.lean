import PLAStochastic.Swing.Gaussian.StripExit.OneSidedSurvival
import PLAStochastic.Swing.Gaussian.StripExit.BallotWidth

/-! # The complete discrete Gaussian survival lemma C.2 -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def gaussianBallotConstant : ℝ := 2*(gaussianUpperExitConstant+gaussianExitMeanConstant+1)

theorem gaussianBallotConstant_pos : 0 < gaussianBallotConstant := by
  have h := gaussianUpperExitConstant_pos
  have h' := gaussianExitMeanConstant_pos
  unfold gaussianBallotConstant
  positivity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The strip reduction also covers starting points outside the strip, using probability ≤1. -/
theorem gaussianSurvivalEvent_le_any_strip
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : 0 ≤ x) (hR : 1 ≤ R)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (haR : a*R ≤ 1/2) {n : ℕ} (hn : 0 < n) :
    μ.real (gaussianSurvivalEvent X x a n) ≤
      (gaussianUpperExitConstant+gaussianExitMeanConstant+1)*(x+1)*(R⁻¹+R/(n : ℝ)) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let C := gaussianUpperExitConstant+gaussianExitMeanConstant+1
  have hC : 1 ≤ C := by dsimp [C]; linarith [gaussianUpperExitConstant_pos, gaussianExitMeanConstant_pos]
  have hR0 : 0 < R := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1 : 0 ≤ x+1 := by linarith
  have hu : gaussianUpperExitConstant ≤ C := by dsimp [C]; linarith [gaussianExitMeanConstant_pos]
  have ht : gaussianExitMeanConstant ≤ C := by dsimp [C]; linarith [gaussianUpperExitConstant_pos]
  change _ ≤ C*(x+1)*(R⁻¹+R/(n : ℝ))
  by_cases hxR : x ≤ R
  · have hb := gaussianSurvivalEvent_le_strip hX hi hG ⟨hx, hxR⟩ hR ha ha' haR hn
    calc
      _ ≤ gaussianUpperExitConstant*(x+1)/R + gaussianExitMeanConstant*R*(x+1)/(n : ℝ) := hb
      _ ≤ C*(x+1)/R + C*R*(x+1)/(n : ℝ) := by gcongr
      _ = _ := by ring
  · have hxR' : R < x := lt_of_not_ge hxR
    have h1 : (1 : ℝ) ≤ (x+1)/R := (le_div_iff₀ hR0).mpr (by linarith)
    have h2 : (x+1)/R ≤ C*((x+1)/R) := le_mul_of_one_le_left (by positivity) hC
    have h3 : 0 ≤ C*(x+1)*(R/(n : ℝ)) := by positivity
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ C*((x+1)/R) := h1.trans h2
      _ ≤ C*((x+1)/R)+C*(x+1)*(R/(n : ℝ)) := le_add_of_nonneg_right h3
      _ = _ := by ring

/-- Lemma C.2 for the actual standard-Gaussian increment process, all x≥0,
0≤a≤1/2 and every integer n≥1. The constant is universal and explicitly defined. -/
theorem gaussian_ballot_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (ha' : a ≤ 1/2) {n : ℕ} (hn : 0 < n) :
    μ.real (gaussianSurvivalEvent X x a n) ≤
      gaussianBallotConstant*(x+1)*(a+(Real.sqrt (n : ℝ))⁻¹) := by
  obtain ⟨hR, haR, hRI, hRN⟩ := gaussianBallotWidth_bounds ha ha' hn
  have hb := gaussianSurvivalEvent_le_any_strip hX hi hG hx hR ha ha' haR hn
  have hC : 0 ≤ (gaussianUpperExitConstant+gaussianExitMeanConstant+1)*(x+1) := by
    have h := gaussianUpperExitConstant_pos
    have h' := gaussianExitMeanConstant_pos
    positivity
  calc
    _ ≤ (gaussianUpperExitConstant+gaussianExitMeanConstant+1)*(x+1)*
      ((gaussianBallotWidth a n)⁻¹+gaussianBallotWidth a n/(n : ℝ)) := hb
    _ ≤ (gaussianUpperExitConstant+gaussianExitMeanConstant+1)*(x+1)*
      (2*a+(Real.sqrt (n : ℝ))⁻¹+(Real.sqrt (n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add hRI hRN) hC
    _ = _ := by unfold gaussianBallotConstant; ring

end SwingRepair
