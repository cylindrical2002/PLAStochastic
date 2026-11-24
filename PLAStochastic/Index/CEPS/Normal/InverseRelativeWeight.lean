import PLAStochastic.Index.CEPS.Normal.BottomRegular
import PLAStochastic.Index.CEPS.Normal.RelativeSlack

/-! # Relative reciprocal normal weights, including bounded root-direction slack -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsNormalData

theorem norm_normalK_real_width (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ)
    (μ q ζ : ℂ) (l : ℝ) :
    ‖a.normalK L μ q l ζ‖ = Real.exp (ζ.re * l) * ‖a.normalK L μ q 0 ζ‖ := by
  simp only [normalK, norm_inv]
  rw [a.norm_normalG_real_width, mul_inv_rev, ← Real.exp_neg]
  simp only [neg_mul, neg_neg]
  ring

end CepsNormalData

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_weight_wide_lower {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound) ≤
      ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q 0 ζ‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hζA : ‖ζ‖ < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hQlo := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq hζA
  have hL := dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ) hq hζ
  change ‖dom.canonL ρW μ q ζ‖ ≤ dom.normalLogBound at hL
  have hlre := (abs_re_le_norm (dom.canonL ρW μ q ζ)).trans hL
  have hlo : Real.exp (-2 * dom.normalLogBound) ≤ ‖cexp (-2 * dom.canonL ρW μ q ζ)‖ := by
    rw [norm_exp]; apply Real.exp_le_exp.mpr
    simp [mul_re]
    linarith [(le_abs_self (dom.canonL ρW μ q ζ).re).trans hlre]
  simp only [CepsNormalData.normalG, mul_zero, exp_zero, one_mul, cepsWHNormalData, norm_mul]
  exact mul_le_mul hQlo hlo (Real.exp_pos _).le (norm_nonneg _)

include hW hθ hD in
theorem cepsNormal_inverse_weight_wide_upper {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    ‖(cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q 0 ζ‖ ≤
      (4 / cepsVarLo D) * Real.exp (2 * dom.normalLogBound) := by
  have hvl := cepsVarLo_pos hD
  have hd := cepsNormal_weight_wide_lower dom hW hθ hD hμ hq hζ
  rw [CepsNormalData.normalK, norm_inv]
  refine (inv_anti₀ (by positivity) hd).trans_eq ?_
  rw [neg_mul, Real.exp_neg]
  field_simp

include hW hθ hD in
theorem cepsNormal_inverse_weight_lower {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    (1 / v) * Real.exp (-2 * dom.normalLogBound) ≤
      ‖(cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q 0 ζ‖ := by
  have hd := cepsNormal_weight_bounds dom hW hθ hD hμ hq hζ
  have hlo : 0 < cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound) := by
    have := cepsVarLo_pos hD; positivity
  have hn : 0 < ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q 0 ζ‖ :=
    hlo.trans_le hd.1
  rw [CepsNormalData.normalK, norm_inv]
  have hi := inv_anti₀ hn hd.2
  have he : (v * Real.exp (2 * dom.normalLogBound))⁻¹ =
      (1 / v) * Real.exp (-2 * dom.normalLogBound) := by
    rw [mul_inv_rev, neg_mul, Real.exp_neg, one_div]; ring
  rwa [he] at hi

include hW hθ hD in
theorem cepsNormal_inverse_relative_weight_on_ball_slack {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : 0 ≤ l)
    {w : ℂ} (hw : ‖w‖ ≤ dom.c₀ / 4)
    {C : ℝ} (hre : w.re * l ≤ (cepsRootPlus D θ ρW μ q).re * l + C)
    {ζ : ℂ} (hζ : ζ ∈ ball w (dom.c₀ / (8 * (1 + l)))) :
    ‖(cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q l ζ‖ ≤
      Real.exp C * dom.normalWeightRatio *
        ‖(cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q l
          (cepsRootPlus D θ ρW μ q)‖ := by
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
  have hreal : ζ.re * l ≤ a.βp.re * l + dom.c₀ / 8 + C := by
    have hab := abs_re_le_norm (ζ - w)
    simp only [sub_re] at hab
    have hn := (le_abs_self (ζ.re - w.re)).trans hab
    change w.re * l ≤ a.βp.re * l + C at hre
    have hdiff : ζ.re - w.re ≤ δ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hdiff hl
    nlinarith
  have hupper := cepsNormal_inverse_weight_wide_upper dom hW hθ hD hμ hq hwide
  have hlower := cepsNormal_inverse_weight_lower dom hW hθ hD hμ hq
    (dom.norm_rootPlus_le hW hθ hD hμ' hq)
  change (1 / v) * Real.exp (-2 * dom.normalLogBound) ≤
    ‖a.normalK (dom.canonL ρW) μ q 0 a.βp‖ at hlower
  have hratio : 0 ≤ dom.normalWeightRatio := by
    have := CepsCanonDomain.v_pos hW hθ hD
    have := cepsVarLo_pos hD
    unfold CepsCanonDomain.normalWeightRatio
    positivity
  have hexp : dom.normalWeightRatio *
      ((1 / v) * Real.exp (-2 * dom.normalLogBound)) =
      Real.exp (dom.c₀ / 8) * ((4 / cepsVarLo D) * Real.exp (2 * dom.normalLogBound)) := by
    have hvl := (cepsVarLo_pos hD).ne'
    have hvn := (CepsCanonDomain.v_pos hW hθ hD).ne'
    unfold CepsCanonDomain.normalWeightRatio
    rw [Real.exp_add]
    have he : Real.exp (4 * dom.normalLogBound) * Real.exp (-2 * dom.normalLogBound) =
        Real.exp (2 * dom.normalLogBound) := by rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (4 / cepsVarLo D) * Real.exp (dom.c₀ / 8) *
          (Real.exp (4 * dom.normalLogBound) * Real.exp (-2 * dom.normalLogBound)) := by
        field_simp
      _ = _ := by rw [he]; ring
  change ‖a.normalK (dom.canonL ρW) μ q l ζ‖ ≤ _
  rw [a.norm_normalK_real_width, a.norm_normalK_real_width]
  calc
    _ ≤ Real.exp (a.βp.re * l + dom.c₀ / 8 + C) * ((4 / cepsVarLo D) * Real.exp (2 * dom.normalLogBound)) :=
      mul_le_mul (Real.exp_le_exp.mpr hreal) hupper (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp C * (dom.normalWeightRatio *
        (Real.exp (a.βp.re * l) * ((1 / v) * Real.exp (-2 * dom.normalLogBound)))) := by
      rw [Real.exp_add, Real.exp_add, mul_left_comm dom.normalWeightRatio, ← mul_assoc, hexp]
      ring
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlower (Real.exp_pos (a.βp.re * l)).le) hratio
      have hc := mul_le_mul_of_nonneg_left hb (Real.exp_pos C).le
      simpa only [mul_assoc] using! hc


end PGM
