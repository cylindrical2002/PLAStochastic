import PLAStochastic.Swing.FrozenCarry.Interior.GoodTail
import PLAStochastic.Swing.FrozenCarry.Interior.Scale

/-! Explicit, uniformly negligible errors in the actual interior-duration sandwich. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenInteriorGood_scaled_compl_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {w E r δ : ℝ} {n : ℕ} (hE : 1 ≤ E) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hn : frozenInteriorWindow δ E n) (hw : 2*|w| ≤ r*E) :
    (n : ℝ)/E*μ.real (frozenInteriorGood X w E r n)ᶜ ≤
      2*E^3*Real.exp (-(r^2/8)*E^δ) := by
  have hEp : 0 < E := by linarith
  have hnr := frozenInteriorWindow_ge_budget hE hδ hn
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le hEp hnr
  have hnN : 0 < n := by exact_mod_cast hnp
  have hn2 := frozenInteriorWindow_le_square hE hδ hn
  have hz : 0 < r*E-|w| := by nlinarith [mul_pos hr hEp]
  have htail := frozenInteriorGood_compl_bound hX hi hG w E r hnN hz
  have hpow := frozenInteriorWindow_quadratic_ratio_ge hE hδ hn
  have hexp : -(r*E-|w|)^2/(2*(n : ℝ)) ≤ -(r^2/8)*E^δ := by
    have hs : (r*E/2)^2 ≤ (r*E-|w|)^2 := by nlinarith [abs_nonneg w, mul_pos hr hEp]
    have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ r^2/8 by positivity)
    have he : r^2/8*(E^2/(n : ℝ)) = (r*E/2)^2/(2*(n : ℝ)) := by ring
    rw [he] at hp
    have hb := div_le_div_of_nonneg_right hs (show 0 ≤ 2*(n : ℝ) by positivity)
    simpa only [neg_div, neg_mul] using neg_le_neg (hp.trans hb)
  have hcoef : (n : ℝ)/E*(2*(n : ℝ)) ≤ 2*E^3 := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hh : (n : ℝ)^2 ≤ (E^2)^2 := by simpa only [sq] using mul_self_le_mul_self hn0 hn2
    calc
      _ = (2*(n : ℝ)^2)/E := by ring
      _ ≤ _ := (div_le_iff₀ hEp).mpr (by nlinarith)
  calc
    _ ≤ (n : ℝ)/E*(2*(n : ℝ)*Real.exp (-(r*E-|w|)^2/(2*(n : ℝ)))) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = ((n : ℝ)/E*(2*(n : ℝ)))*Real.exp (-(r*E-|w|)^2/(2*(n : ℝ))) := by ring
    _ ≤ _ := mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)


/-- The actual finite/infinite Gaussian correction is negligible throughout the window. -/
theorem gaussianSurvival_scaled_remainder_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {w E c δ : ℝ} {n : ℕ} (hE : 2 ≤ E) (hc : 0 < c) (hδ : 0 ≤ δ)
    (hn : frozenInteriorWindow δ E n) (hw : 0 ≤ w) :
    (n : ℝ)/E*(μ.real (gaussianHalfLineSurvives X (w+c*E/n) (c*E/n) (n-1))-
      gaussianInfiniteSurvival X μ (w+c*E/n) (c*E/n)) ≤
      gaussianBallotConstant*(w+c*E/n+1)*E*Real.exp (-(c^2/4)*E^δ) := by
  have hEp : 0 < E := by linarith
  have hEn := frozenInteriorWindow_ge_budget (by linarith : 1 ≤ E) hδ hn
  have hnp : (0 : ℝ) < n := lt_of_lt_of_le hEp hEn
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ n by linarith)
  have ha : 0 < c*E/(n : ℝ) := by positivity
  have hx : 0 ≤ w+c*E/(n : ℝ) := add_nonneg hw ha.le
  have hb := (gaussianSurvivalEvent_sub_infinite_bound hX hi hG hx ha (by omega : 0 < n-1)).2
  rw [← gaussianHalfLineSurvives_eq_survivalEvent hx] at hb
  have hsqrt : (Real.sqrt ((n-1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (show 1 ≤ n-1 by omega)
  have hcoef : (n : ℝ)/E ≤ E := (div_le_iff₀ hEp).mpr (by
    simpa only [sq] using frozenInteriorWindow_le_square (by linarith : 1 ≤ E) hδ hn)
  have hexp : Real.exp (-(c*E/(n : ℝ))^2*((n-1 : ℕ) : ℝ)/2) ≤ Real.exp (-(c^2/4)*E^δ) := by
    apply Real.exp_le_exp.mpr
    have hh := frozenInteriorWindow_exponent_ge hE hδ hn (c := c)
    linarith
  have hC : 0 ≤ gaussianBallotConstant*(w+c*E/(n : ℝ)+1) := by
    have := gaussianBallotConstant_pos
    positivity
  calc
    _ ≤ (n : ℝ)/E*(gaussianBallotConstant*(w+c*E/n+1)*
        (Real.sqrt ((n-1 : ℕ) : ℝ))⁻¹*Real.exp (-(c*E/n)^2*((n-1 : ℕ) : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ E*(gaussianBallotConstant*(w+c*E/n+1)*1*Real.exp (-(c^2/4)*E^δ)) := by
      apply mul_le_mul hcoef _ (by positivity) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hC) hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

end SwingRepair
