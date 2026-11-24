import PLAStochastic.Index.CEPS.Ident.CorollariesQ
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound

/-! # Uniform local logarithmic derivative budgets for the actual factors -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

/-- The canonical logarithm bound on the half-width root disc. -/
def normalLogBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.CL * (2 * D ^ 2 / θ + 3 / (2 * dom.c₀)) +
    (|Real.log (1 / 4)| + |Real.log 2| + Real.pi)

/-- A class budget for `Q'/Q - 2L'` near both small roots. -/
def normalDerivativeBudget {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  1 / dom.ρA + 16 * dom.normalLogBound / dom.c₀

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsQ_norm_ge_on_rootZone {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ < dom.ρA) :
    cepsVarLo D / 4 ≤ ‖cepsQ D θ ρW μ q ζ‖ := by
  have hnear := dom.norm_cepsQuotA_sub_le hW hθ hD hμ hq hζ.le
  rw [← CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμ hq
    (mem_ball_zero_iff.mpr hζ)] at hnear
  have hv := cepsStepVar_pos hW hθ hD
  have hvl := cepsVarLo_le hW hθ hD
  have hn : ‖(cepsStepVar ρW : ℂ) / 2‖ = cepsStepVar ρW / 2 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hv]; norm_num
  have ht := norm_sub_norm_le ((cepsStepVar ρW : ℂ) / 2) (cepsQ D θ ρW μ q ζ)
  rw [norm_sub_rev] at ht
  rw [hn] at ht
  have hvl0 := cepsVarLo_pos hD
  linarith

include hW hθ hD in
theorem cepsQ_logDerivative_le {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ < dom.ρA / 2) :
    ‖deriv (cepsQ D θ ρW μ q) ζ / cepsQ D θ ρW μ q ζ‖ ≤ 1 / dom.ρA := by
  have hQ : DifferentiableOn ℂ (cepsQ D θ ρW μ q) (ball 0 dom.ρA) :=
    fun z hz => (CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ hq hz).differentiableWithinAt
  have hbound : ∀ z ∈ ball (0 : ℂ) dom.ρA,
      ‖cepsQ D θ ρW μ q z - (cepsStepVar ρW : ℂ) / 2‖ ≤ cepsVarLo D / 16 := by
    intro z hz
    rw [CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμ hq hz]
    exact dom.norm_cepsQuotA_sub_le hW hθ hD hμ hq (mem_ball_zero_iff.mp hz).le
  have hd := norm_deriv_le_of_ball_half dom.ρA_pos (hQ.sub_const _) hbound
    (mem_ball_zero_iff.mpr hζ)
  rw [deriv_sub_const] at hd
  have hζ' : ‖ζ‖ < dom.ρA := by have := dom.ρA_pos; linarith
  have hlo := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ hq hζ'
  have hv0 : 0 < cepsVarLo D / 4 := by have := cepsVarLo_pos hD; positivity
  rw [norm_div]
  calc
    ‖deriv (cepsQ D θ ρW μ q) ζ‖ / ‖cepsQ D θ ρW μ q ζ‖ ≤
        (4 * (cepsVarLo D / 16) / dom.ρA) / (cepsVarLo D / 4) :=
      div_le_div₀ (by have := cepsVarLo_pos hD; have := dom.ρA_pos; positivity) hd hv0 hlo
    _ = 1 / dom.ρA := by
      have hvlne := (cepsVarLo_pos hD).ne'
      field_simp; ring

include hW hθ hD in
theorem canonL_spatialDerivative_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    ‖deriv (dom.canonL ρW μ q) ζ‖ ≤ 8 * dom.normalLogBound / dom.c₀ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hrad : 0 < dom.c₀ / 4 := by have := dom.c₀_pos; positivity
  have hmap : ∀ z ∈ ball ζ (dom.c₀ / 4), ‖z‖ ≤ dom.c₀ / 2 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have ht' := norm_add_le (z - ζ) ζ
    rw [sub_add_cancel] at ht'
    linarith
  have hL : DifferentiableOn ℂ (dom.canonL ρW μ q) (ball ζ (dom.c₀ / 4)) := by
    intro z hz
    have hzn := hmap z hz
    have hzr : z.re < dom.c₀ := by linarith [re_le_norm z, dom.c₀_pos]
    exact (CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq hzr).differentiableWithinAt
  have hb : ∀ z ∈ ball ζ (dom.c₀ / 4), ‖dom.canonL ρW μ q z‖ ≤ dom.normalLogBound := by
    intro z hz
    exact dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ) hq (hmap z hz)
  have hd := norm_iteratedDeriv_le_of_ball 1 hrad hL hb
  rw [iteratedDeriv_one] at hd
  convert hd using 1
  simp
  ring

include hW hθ hD in
theorem cepsNormal_actual_derivativeBudget {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 4) :
    ‖deriv (cepsQ D θ ρW μ q) ζ / cepsQ D θ ρW μ q ζ -
      2 * deriv (dom.canonL ρW μ q) ζ‖ ≤ dom.normalDerivativeBudget := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hζ' : ‖ζ‖ < dom.ρA / 2 := by
    have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hQ := cepsQ_logDerivative_le dom hW hθ hD hμ' hq hζ'
  have hL := canonL_spatialDerivative_le dom hW hθ hD hμ hq hζ
  calc
    _ ≤ ‖deriv (cepsQ D θ ρW μ q) ζ / cepsQ D θ ρW μ q ζ‖ +
        ‖2 * deriv (dom.canonL ρW μ q) ζ‖ := norm_sub_le _ _
    _ ≤ 1 / dom.ρA + 2 * (8 * dom.normalLogBound / dom.c₀) := by
      rw [norm_mul, norm_ofNat]; gcongr
    _ = dom.normalDerivativeBudget := by unfold CepsCanonDomain.normalDerivativeBudget; ring

end PGM
