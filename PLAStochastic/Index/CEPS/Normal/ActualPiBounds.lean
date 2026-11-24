import PLAStochastic.Index.CEPS.Normal.ActualMorseData
import PLAStochastic.Index.CEPS.Normal.MergedNonzero
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound

/-! # A class-uniform first-order bound for the actual normal factor ratio -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def normalPiBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  4 * v / cepsVarLo D * dom.normalDerivativeBudget * Real.exp (4 * dom.normalLogBound)

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsNormal_budget_nonneg : 0 ≤ dom.normalDerivativeBudget := by
  have hρ := dom.ρA_pos
  have hc := dom.c₀_pos
  unfold CepsCanonDomain.normalDerivativeBudget CepsCanonDomain.normalLogBound
    CepsCanonDomain.CL CepsCanonDomain.Linf
  positivity

include hW hθ hD in
theorem cepsQ_norm_le_on_rootZone {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ < dom.ρA) : ‖cepsQ D θ ρW μ q ζ‖ ≤ v := by
  have hnear := dom.norm_cepsQuotA_sub_le hW hθ hD hμ hq hζ.le
  rw [← CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμ hq
    (mem_ball_zero_iff.mpr hζ)] at hnear
  have hv := cepsStepVar_pos hW hθ hD
  have hvl := CepsCanonDomain.varLo_le_v hW hθ hD
  have hn : ‖(cepsStepVar ρW : ℂ) / 2‖ = cepsStepVar ρW / 2 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hv]; norm_num
  have ht := norm_add_le (cepsQ D θ ρW μ q ζ - (cepsStepVar ρW : ℂ) / 2)
    ((cepsStepVar ρW : ℂ) / 2)
  rw [sub_add_cancel, hn] at ht
  linarith [cepsStepVar_le hW, cepsVarLo_pos hD]

include hW hθ hD in
theorem cepsNormal_weight_bounds {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound) ≤
        ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q 0 ζ‖ ∧
      ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q 0 ζ‖ ≤
        v * Real.exp (2 * dom.normalLogBound) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hζA : ‖ζ‖ < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hQlo := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq hζA
  have hQhi := cepsQ_norm_le_on_rootZone dom hW hθ hD hμ' hq hζA
  have hL := dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ) hq
    (show ‖ζ‖ ≤ dom.c₀ / 2 by have := dom.c₀_pos; linarith)
  change ‖dom.canonL ρW μ q ζ‖ ≤ dom.normalLogBound at hL
  have hlre := (abs_re_le_norm (dom.canonL ρW μ q ζ)).trans hL
  have hlo : Real.exp (-2 * dom.normalLogBound) ≤ ‖cexp (-2 * dom.canonL ρW μ q ζ)‖ := by
    rw [norm_exp]; apply Real.exp_le_exp.mpr
    simp [mul_re]
    linarith [(le_abs_self (dom.canonL ρW μ q ζ).re).trans hlre]
  have hhi : ‖cexp (-2 * dom.canonL ρW μ q ζ)‖ ≤ Real.exp (2 * dom.normalLogBound) := by
    rw [norm_exp]; apply Real.exp_le_exp.mpr
    simp [mul_re]
    linarith [(neg_le_abs (dom.canonL ρW μ q ζ).re).trans hlre]
  simp only [CepsNormalData.normalG, mul_zero, exp_zero, one_mul, cepsWHNormalData, norm_mul]
  exact ⟨mul_le_mul hQlo hlo (Real.exp_pos _).le (norm_nonneg _),
    mul_le_mul hQhi hhi (norm_nonneg _) (CepsCanonDomain.v_pos hW hθ hD).le⟩

include hW hθ hD in
theorem cepsNormal_weight_derivative_bound {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    ‖deriv ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q 0) ζ‖ ≤
      v * Real.exp (2 * dom.normalLogBound) * dom.normalDerivativeBudget := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hζA : ζ ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hdQ := (CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq hζA).hasDerivAt
  have hdL := (CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq
    (show ζ.re < dom.c₀ by linarith [re_le_norm ζ, dom.c₀_pos])).hasDerivAt
  have hQ0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hζA
  have hd := (cepsWHNormalData D θ ρW μ q).hasDerivAt_normalG
    (dom.canonL ρW) μ q (l := 0) hdQ hdL hQ0
  have hbudget := cepsNormal_actual_derivativeBudget dom hW hθ hD hμ hq hζ
  have hweight := (cepsNormal_weight_bounds dom hW hθ hD hμ hq hζ).2
  rw [hd.deriv, norm_mul]
  simp only [neg_zero, zero_add]
  exact mul_le_mul hweight hbudget (norm_nonneg _) (mul_nonneg (CepsCanonDomain.v_pos hW hθ hD).le (Real.exp_pos _).le)


include hW hθ hD in
/-- The actual factor ratio has a class-uniform first-order zero at merged roots. -/
theorem cepsNormal_actual_pi_sub_one_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) :
    ‖(cepsWHNormalData D θ ρW μ q).pi (dom.canonL ρW) μ q - 1‖ ≤
      dom.normalPiBound * ‖(cepsWHNormalData D θ ρW μ q).eta‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  let a := cepsWHNormalData D θ ρW μ q
  let F := a.normalG (dom.canonL ρW) μ q 0
  have hp : ‖a.βp‖ ≤ dom.c₀ / 4 := dom.norm_rootPlus_le hW hθ hD hμ' hq
  have hm : ‖a.βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμ' hq
  have hd : ∀ ζ ∈ closedBall (0 : ℂ) (dom.c₀ / 4), DifferentiableAt ℂ F ζ := by
    intro ζ hζ
    have hζ' := mem_closedBall_zero_iff.mp hζ
    have hζA : ζ ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
      have := dom.c₀_le; have := dom.ρA_pos; linarith)
    exact (a.hasDerivAt_normalG (dom.canonL ρW) μ q
      ((CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq hζA).hasDerivAt)
      ((CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq
        (show ζ.re < dom.c₀ by linarith [re_le_norm ζ, dom.c₀_pos])).hasDerivAt)
      (CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hζA)).differentiableAt
  have hdiff := (convex_closedBall (0 : ℂ) (dom.c₀ / 4)).norm_image_sub_le_of_norm_deriv_le
    (f := F) hd
    (fun ζ hζ => cepsNormal_weight_derivative_bound dom hW hθ hD hμ hq
      (mem_closedBall_zero_iff.mp hζ))
    (mem_closedBall_zero_iff.mpr hm) (mem_closedBall_zero_iff.mpr hp)
  have hlow := (cepsNormal_weight_bounds dom hW hθ hD hμ hq hm).1
  change cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound) ≤ ‖F a.βm‖ at hlow
  have hlo0 : 0 < cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound) := by
    exact mul_pos (div_pos (cepsVarLo_pos hD) (by norm_num)) (Real.exp_pos _)
  have hFm : F a.βm ≠ 0 := norm_pos_iff.mp (hlo0.trans_le hlow)
  have hQm : a.Q a.βm ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq
    (mem_ball_zero_iff.mpr (by have := dom.c₀_le; have := dom.ρA_pos; linarith))
  have hpi : F a.βp / F a.βm = a.pi (dom.canonL ρW) μ q := by
    simpa only [CepsNormalData.decay, mul_zero, exp_zero, one_mul] using
      a.normalG_root_ratio (dom.canonL ρW) μ q (l := 0) hQm
  have hn : ‖a.pi (dom.canonL ρW) μ q - 1‖ * ‖F a.βm‖ =
      ‖F a.βp - F a.βm‖ := by
    rw [← hpi, div_sub_one hFm, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hFm)]
  have hfactor : dom.normalPiBound *
      (cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound)) =
      v * Real.exp (2 * dom.normalLogBound) * dom.normalDerivativeBudget := by
    have hexp : Real.exp (4 * dom.normalLogBound) * Real.exp (-2 * dom.normalLogBound) =
        Real.exp (2 * dom.normalLogBound) := by rw [← Real.exp_add]; congr 1; ring
    have hvlo := (cepsVarLo_pos hD).ne'
    unfold CepsCanonDomain.normalPiBound
    calc
      _ = (v * dom.normalDerivativeBudget) *
          (Real.exp (4 * dom.normalLogBound) * Real.exp (-2 * dom.normalLogBound)) := by
        field_simp
      _ = _ := by rw [hexp]; ring
  have hmul : ‖a.pi (dom.canonL ρW) μ q - 1‖ *
      (cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound)) ≤
      (dom.normalPiBound * ‖a.eta‖) *
        (cepsVarLo D / 4 * Real.exp (-2 * dom.normalLogBound)) := by
    calc
      _ ≤ ‖a.pi (dom.canonL ρW) μ q - 1‖ * ‖F a.βm‖ :=
        mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ = _ := hn
      _ ≤ _ := hdiff
      _ = _ := by
        change _ = dom.normalPiBound * ‖a.βp - a.βm‖ * _
        rw [mul_right_comm dom.normalPiBound, hfactor]
  exact le_of_mul_le_mul_right hmul hlo0

end PGM
