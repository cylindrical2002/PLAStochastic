import PLAStochastic.Swing.FrozenCarry.Interior.Error
import PLAStochastic.Swing.Gaussian.Survival.SmallDriftUniform

/-! The exact coefficient in the actual frozen tail, with all approximation errors explicit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def frozenScaledTail (X : ℕ → Ω → ℝ) (μ : Measure Ω) (w E : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)/E*μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}

theorem frozenInterior_scaled_error_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {w E r δ ε : ℝ} {n : ℕ} (hE : 2 ≤ E) (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ)
    (hn : frozenInteriorWindow δ E n) (hw : 0 ≤ w) (hwb : 2*|w| ≤ r*E) (hε : 0 ≤ ε)
    (hm : |gaussianInfiniteSurvival X μ (w+(2-r)*E/n) ((2-r)*E/n)/(2*((2-r)*E/n))-
      gaussianRenewalPotential X μ w| ≤ ε)
    (hp : |gaussianInfiniteSurvival X μ (w+(2+r)*E/n) ((2+r)*E/n)/(2*((2+r)*E/n))-
      gaussianRenewalPotential X μ w| ≤ ε) :
    |frozenScaledTail X μ w E n-4*gaussianRenewalPotential X μ w| ≤
      2*r*|gaussianRenewalPotential X μ w|+(4+2*r)*ε+
        2*E^3*Real.exp (-(r^2/8)*E^δ)+
          gaussianBallotConstant*(w+(2+r)*E/n+1)*E*Real.exp (-((2+r)^2/4)*E^δ) := by
  have := hi.isProbabilityMeasure
  have hEp : 0 < E := by linarith
  have hEn := frozenInteriorWindow_ge_budget (by linarith : 1 ≤ E) hδ hn
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le hEp hEn
  have hnN : 0 < n := by exact_mod_cast hnp
  obtain ⟨hlo, hhi⟩ := frozenPrefixLength_interior_probability_sandwich (μ := μ) hnN hEp.le (by linarith : r ≤ 2)
  have hb := frozenInteriorGood_scaled_compl_bound hX hi hG (by linarith : 1 ≤ E) hr hδ hn hwb
  have hf := gaussianSurvival_scaled_remainder_bound hX hi hG hE (by linarith : 0 < 2+r) hδ hn hw
  have hlo' := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (n : ℝ)/E by positivity)
  have hhi' := mul_le_mul_of_nonneg_left hhi (show 0 ≤ (n : ℝ)/E by positivity)
  have he (c : ℝ) (hc : c ≠ 0) :
      (n : ℝ)/E*gaussianInfiniteSurvival X μ (w+c*E/n) (c*E/n) =
        (2*c)*(gaussianInfiniteSurvival X μ (w+c*E/n) (c*E/n)/(2*(c*E/n))) := by
    field_simp
  have hqm := (abs_le.mp hm).1
  have hqp := (abs_le.mp hp).2
  have hlm := mul_le_mul_of_nonneg_left hqm (show 0 ≤ 2*(2-r) by linarith)
  have hlp := mul_le_mul_of_nonneg_left hqp (show 0 ≤ 2*(2+r) by linarith)
  have heM := he (2-r) (by linarith)
  have heP := he (2+r) (by linarith)
  have hV := le_abs_self (gaussianRenewalPotential X μ w)
  have hV' := neg_le_abs (gaussianRenewalPotential X μ w)
  have hVr := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2*r by positivity)
  have hVr' := mul_le_mul_of_nonneg_left hV' (show 0 ≤ 2*r by positivity)
  have hbad : 0 ≤ 2*E^3*Real.exp (-(r^2/8)*E^δ) := by positivity
  have hrem : 0 ≤ gaussianBallotConstant*(w+(2+r)*E/n+1)*E*Real.exp (-((2+r)^2/4)*E^δ) := by
    have := gaussianBallotConstant_pos
    positivity
  unfold frozenScaledTail
  apply abs_le.mpr
  constructor <;> nlinarith

end SwingRepair
