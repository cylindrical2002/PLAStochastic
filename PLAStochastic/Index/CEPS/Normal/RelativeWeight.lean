import PLAStochastic.Index.CEPS.Normal.ActualBridgeBound

/-! # Relative normal weights on discs adapted to the width

Dividing by the lower-root weight removes the exponentially large factor.
Discs of radius proportional to `(1 + l)⁻¹` then have a uniform bound.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def normalWeightRatio {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  4 * v / cepsVarLo D * Real.exp (4 * dom.normalLogBound + dom.c₀ / 8)

def normalSpatialSecondBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  512 * dom.normalWeightRatio / dom.c₀ ^ 2

end CepsCanonDomain

namespace CepsNormalData

theorem norm_normalG_real_width (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ)
    (μ q ζ : ℂ) (l : ℝ) :
    ‖a.normalG L μ q l ζ‖ = Real.exp (-ζ.re * l) * ‖a.normalG L μ q 0 ζ‖ := by
  simp only [normalG, mul_zero, exp_zero, one_mul, norm_mul, norm_exp]
  simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
  ring

end CepsNormalData

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_weight_wide_upper {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q 0 ζ‖ ≤
      v * Real.exp (2 * dom.normalLogBound) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hζA : ‖ζ‖ < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hQ := cepsQ_norm_le_on_rootZone dom hW hθ hD hμ' hq hζA
  have hL := dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ) hq hζ
  change ‖dom.canonL ρW μ q ζ‖ ≤ dom.normalLogBound at hL
  have hExp : ‖cexp (-2 * dom.canonL ρW μ q ζ)‖ ≤ Real.exp (2 * dom.normalLogBound) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    simp [mul_re]
    have hr := (neg_le_abs (dom.canonL ρW μ q ζ).re).trans
      ((abs_re_le_norm _).trans hL)
    linarith
  simp only [CepsNormalData.normalG, mul_zero, exp_zero, one_mul, cepsWHNormalData, norm_mul]
  exact mul_le_mul hQ hExp (norm_nonneg _) (CepsCanonDomain.v_pos hW hθ hD).le

include hW hθ hD in
theorem cepsNormal_relative_weight_on_ball {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : 0 ≤ l)
    {w : ℂ} (hw : ‖w‖ ≤ dom.c₀ / 4)
    (hre : (cepsRootMinus D θ ρW μ q).re ≤ w.re)
    {ζ : ℂ} (hζ : ζ ∈ ball w (dom.c₀ / (8 * (1 + l)))) :
    ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l ζ‖ ≤
      dom.normalWeightRatio *
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
  have hreal : -ζ.re * l ≤ -a.βm.re * l + dom.c₀ / 8 := by
    have hab := abs_re_le_norm (ζ - w)
    simp only [sub_re] at hab
    have hn := (neg_le_abs (ζ.re - w.re)).trans hab
    change a.βm.re ≤ w.re at hre
    have hdiff : a.βm.re - ζ.re ≤ δ := by linarith
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
    _ ≤ Real.exp (-a.βm.re * l + dom.c₀ / 8) * (v * Real.exp (2 * dom.normalLogBound)) :=
      mul_le_mul (Real.exp_le_exp.mpr hreal) hupper (norm_nonneg _) (Real.exp_pos _).le
    _ = dom.normalWeightRatio *
        (Real.exp (-a.βm.re * l) * (cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound))) := by
      rw [Real.exp_add, mul_left_comm dom.normalWeightRatio, ← mul_assoc, hexp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le) hratio

end PGM
