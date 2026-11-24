import PLAStochastic.Index.CEPS.Scaled.CenterUnit
import PLAStochastic.Index.CEPS.Scaled.CanonScaleCurve

/-! # The removable scaled Morse center and its complex-scale signs -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledMorseCenter (D θ : ℝ) (ρW : Measure ℝ) (lam : ℝ) (b : ℂ) : ℂ :=
  (lam : ℂ) * cepsMorseCenterUnit D θ ρW (b * lam)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMorseCenter_actual (lam : ℝ) (b : ℂ) :
    b * cepsScaledMorseCenter D θ ρW lam b = cepsMorseCenter D θ ρW (b * lam) := by
  have h := sub_smul_dslope (cepsMorseCenter D θ ρW) 0 (b * lam)
  rw [sub_zero, smul_eq_mul, cepsMorseCenter_at_zero hW hθ hD, sub_zero] at h
  unfold cepsScaledMorseCenter cepsMorseCenterUnit
  simpa only [mul_assoc] using h

include hW hθ hD in
theorem cepsScaledMorseCenter_budget (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledMorseCenter D θ ρW lam)
      (ball 0 (dom.canonScaleRadius lam z)) ∧
      ∀ b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z),
        ‖cepsScaledMorseCenter D θ ρW lam b‖ ≤ 2 / cepsVarLo D * |lam| := by
  obtain ⟨hd, hm⟩ := cepsMorseCenterUnit_budget dom hW hθ hD
  have hmap : MapsTo (fun b : ℂ => b * (lam : ℂ)) (ball 0 (dom.canonScaleRadius lam z))
      (ball 0 dom.μ₀) := by
    intro b hb
    have hn := (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hb).1
    exact mem_ball_zero_iff.mpr (hn.trans (by linarith [dom.μ₀_pos]))
  refine ⟨?_, fun b hb => ?_⟩
  · simpa only [cepsScaledMorseCenter, Function.comp_apply] using!
      (hd.comp (differentiableOn_id.mul_const (lam : ℂ)) hmap).const_mul (lam : ℂ)
  · rw [cepsScaledMorseCenter, norm_mul, norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hm _ (hmap hb)) (abs_nonneg lam)).trans_eq (by ring)

include hW hθ hD in
theorem cepsScaledMorseCenter_zero (lam : ℝ) :
    cepsScaledMorseCenter D θ ρW lam 0 = -(lam : ℂ) / cepsStepVar ρW := by
  rw [cepsScaledMorseCenter, zero_mul, cepsMorseCenterUnit_zero hW hθ hD]
  ring

include hW hθ hD in
theorem cepsScaledMorseCenter_complex_signs (lam : ℝ) {b : ℂ}
    (hμ : b * (lam : ℂ) ∈ ball (0 : ℂ) dom.centerUnitSectorRadius) :
    (lam ≤ 0 → 0 ≤ (cepsScaledMorseCenter D θ ρW lam b).re) ∧
      (0 ≤ lam → (cepsScaledMorseCenter D θ ρW lam b).re ≤ 0) ∧
      ‖cepsScaledMorseCenter D θ ρW lam b‖ ≤ 3 * |lam| / (2 * cepsStepVar ρW) := by
  obtain ⟨hre, hnorm⟩ := cepsMorseCenterUnit_complex_sector dom hW hθ hD hμ
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hgre : (cepsMorseCenterUnit D θ ρW (b * lam)).re ≤ 0 :=
    hre.trans (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  have hreal : (cepsScaledMorseCenter D θ ρW lam b).re =
      lam * (cepsMorseCenterUnit D θ ρW (b * lam)).re := by simp [cepsScaledMorseCenter, mul_re]
  refine ⟨fun hl => ?_, fun hl => ?_, ?_⟩
  · rw [hreal]
    exact mul_nonneg_of_nonpos_of_nonpos hl hgre
  · rw [hreal]
    exact mul_nonpos_of_nonneg_of_nonpos hl hgre
  · rw [cepsScaledMorseCenter, norm_mul, norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hnorm (abs_nonneg lam)).trans_eq (by ring)

end PGM
