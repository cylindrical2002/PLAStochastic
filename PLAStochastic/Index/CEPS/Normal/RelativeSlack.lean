import PLAStochastic.Index.CEPS.Normal.RelativeDerivative

/-! # Relative spatial budgets with a bounded width-scaled real-part slack -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_relative_weight_on_ball_slack {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : 0 ≤ l)
    {w : ℂ} (hw : ‖w‖ ≤ dom.c₀ / 4)
    {C : ℝ} (hre : (cepsRootMinus D θ ρW μ q).re * l ≤ w.re * l + C)
    {ζ : ℂ} (hζ : ζ ∈ ball w (dom.c₀ / (8 * (1 + l)))) :
    ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l ζ‖ ≤
      Real.exp C * dom.normalWeightRatio *
        ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l
          (cepsRootMinus D θ ρW μ q)‖ := by
  have hc := dom.c₀_pos
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  let a := cepsWHNormalData D θ ρW μ q
  let δ := dom.c₀ / (8 * (1 + l))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ dom.c₀ / 8 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left hc.le (by norm_num)
    linarith
  have hδl : δ * l ≤ dom.c₀ / 8 := by
    have hid : δ * (1 + l) = dom.c₀ / 8 := by dsimp [δ]; field_simp
    nlinarith
  have hdist : ‖ζ - w‖ < δ := by simpa only [mem_ball, dist_eq_norm, δ] using hζ
  have hwide : ‖ζ‖ ≤ dom.c₀ / 2 := by
    have hn := norm_add_le (ζ - w) w
    rw [sub_add_cancel] at hn
    linarith
  have hreal : -ζ.re * l ≤ -a.βm.re * l + dom.c₀ / 8 + C := by
    have hab := abs_re_le_norm (ζ - w)
    simp only [sub_re] at hab
    have hn := (neg_le_abs (ζ.re - w.re)).trans hab
    change a.βm.re * l ≤ w.re * l + C at hre
    have hdiff : w.re - ζ.re ≤ δ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hdiff hl
    nlinarith
  have hupper := cepsNormal_weight_wide_upper dom hW hθ hD hμ hq hwide
  have hlower := (cepsNormal_weight_bounds dom hW hθ hD hμ hq
    (dom.norm_rootMinus_le hW hθ hD hμ' hq)).1
  change cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound) ≤
    ‖a.normalG (dom.canonL ρW) μ q 0 a.βm‖ at hlower
  have hratio : 0 ≤ dom.normalWeightRatio := by
    have := CepsCanonDomain.v_pos hW hθ hD
    have := cepsVarLo_pos hD
    unfold CepsCanonDomain.normalWeightRatio
    positivity
  have hexp : dom.normalWeightRatio *
      (cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound)) =
      Real.exp (dom.c₀ / 8) * (v * Real.exp (2 * dom.normalLogBound)) := by
    have hvl := (cepsVarLo_pos hD).ne'
    unfold CepsCanonDomain.normalWeightRatio
    rw [Real.exp_add]
    have he : Real.exp (4 * dom.normalLogBound) * Real.exp (-2 * dom.normalLogBound) =
        Real.exp (2 * dom.normalLogBound) := by rw [← Real.exp_add]; congr 1; ring
    calc
      _ = v * Real.exp (dom.c₀ / 8) *
          (Real.exp (4 * dom.normalLogBound) * Real.exp (-2 * dom.normalLogBound)) := by
        field_simp
      _ = _ := by rw [he]; ring
  change ‖a.normalG (dom.canonL ρW) μ q l ζ‖ ≤ _
  rw [a.norm_normalG_real_width, a.norm_normalG_real_width]
  calc
    _ ≤ Real.exp (-a.βm.re * l + dom.c₀ / 8 + C) * (v * Real.exp (2 * dom.normalLogBound)) :=
      mul_le_mul (Real.exp_le_exp.mpr hreal) hupper (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp C * (dom.normalWeightRatio *
        (Real.exp (-a.βm.re * l) * (cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound)))) := by
      rw [Real.exp_add, Real.exp_add, mul_left_comm dom.normalWeightRatio, ← mul_assoc, hexp]
      ring
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlower (Real.exp_pos (-a.βm.re * l)).le) hratio
      have hc := mul_le_mul_of_nonneg_left hb (Real.exp_pos C).le
      simpa only [mul_assoc] using! hc


include hW hθ hD in
theorem cepsNormal_relative_secondDerivative_le_slack {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : 0 ≤ l)
    {w : ℂ} (hw : ‖w‖ ≤ dom.c₀ / 4)
    {C : ℝ} (hre : (cepsRootMinus D θ ρW μ q).re * l ≤ w.re * l + C) :
    ‖deriv (deriv ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)) w‖ ≤
      Real.exp C * dom.normalSpatialSecondBound * (1 + l) ^ 2 *
        ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l
          (cepsRootMinus D θ ρW μ q)‖ := by
  let δ := dom.c₀ / (8 * (1 + l))
  have hc := dom.c₀_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ dom.c₀ / 8 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left hc.le (by norm_num)
    linarith
  have hsub : ball w δ ⊆ ball (0 : ℂ) (dom.c₀ / 2) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    apply mem_ball_zero_iff.mpr
    have hn := norm_add_le (z - w) w
    rw [sub_add_cancel] at hn
    linarith
  have hd := norm_iteratedDeriv_le_of_ball 2 hδ
    ((cepsNormalG_differentiableOn_spatial dom hW hθ hD hμ hq l).mono hsub)
    (fun z hz => cepsNormal_relative_weight_on_ball_slack dom hW hθ hD hμ hq hl hw hre hz)
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hd
  refine hd.trans_eq ?_
  simp only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one]
  unfold CepsCanonDomain.normalSpatialSecondBound δ
  field_simp
  ring


end PGM
