import PLAStochastic.Swing.FrozenCarry.DurationTail.BridgeTail
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The harmonic duration bound extended to the short-horizon portion used in mean estimates. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def frozenHarmonicTailConstant : ℝ := 48*gaussianBallotConstant+6

theorem frozenHarmonicTailConstant_pos : 0 < frozenHarmonicTailConstant := by
  have h := gaussianBallotConstant_pos
  unfold frozenHarmonicTailConstant
  positivity

theorem frozenHarmonicTailConstant_ge_six : 6 ≤ frozenHarmonicTailConstant := by
  have h := gaussianBallotConstant_pos
  unfold frozenHarmonicTailConstant
  linarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- A universal enlargement covers all short horizons as well as the bridge-controlled range. -/
theorem frozenPrefixLength_harmonic_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (w : ℝ) {E : ℝ} (hE : 1 ≤ E) {n : ℕ} (hn : 0 < n) (hnE : (n : ℝ) ≤ E^2+1) :
    μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ≤
      frozenHarmonicTailConstant*(1+max w 0)*E/(n : ℝ) := by
  have := hi.isProbabilityMeasure
  have hNr : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 1 ≤ 1+max w 0 := by linarith [le_max_right w 0]
  have hE0 : 0 ≤ E := by linarith
  by_cases hlarge : 4*E+2 ≤ (n : ℝ)
  · have hh := frozenPrefixLength_duration_tail hX hi hG w hE hlarge hnE
    exact hh.trans (by
      dsimp only [frozenHarmonicTailConstant]
      gcongr
      linarith)
  · have hnsmall : (n : ℝ) ≤ 6*E := by push Not at hlarge; linarith
    have hC := frozenHarmonicTailConstant_ge_six
    have hh : (n : ℝ) ≤ frozenHarmonicTailConstant*(1+max w 0)*E := by
      calc
        _ ≤ 6*E := hnsmall
        _ ≤ frozenHarmonicTailConstant*E := mul_le_mul_of_nonneg_right hC hE0
        _ ≤ _ := by gcongr; exact le_mul_of_one_le_right frozenHarmonicTailConstant_pos.le hw
    exact (measureReal_le_one (μ := μ)).trans ((one_le_div hNr).mpr hh)

end SwingRepair
