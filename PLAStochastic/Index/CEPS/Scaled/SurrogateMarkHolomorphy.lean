import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceHolomorphy
import PLAStochastic.Index.CEPS.Scaled.TrueMarkPrefactor

/-! # Scale holomorphy of the marked canonical surrogate prefactor -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateMarkLog_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (fun b => cepsCanonDriftTaylor dom ρW N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b ^ 2 * z))
      (ball 0 (dom.entranceScaleRadius N M lam z)) := by
  let U : Set ℂ := ball 0 (dom.entranceScaleRadius N M lam z)
  have hcurve : DifferentiableOn ℂ (fun b : ℂ =>
      (b * (lam : ℂ), (cepsComplexScaledDiscount lam z b, b ^ 2 * z))) U := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have hmap : MapsTo (fun b : ℂ =>
      (b * (lam : ℂ), (cepsComplexScaledDiscount lam z b, b ^ 2 * z))) U
      {x : ℂ × (ℂ × ℂ) | x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2} := by
    intro b hb
    have ht := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb
      (entranceScaleCurve_mark_mem dom hD N M lam hb)
    have hζ : ‖b ^ 2 * z‖ < dom.c₀ / 2 := by simpa only [pow_two, mul_assoc] using ht.2
    have hq := (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) ht.1).2.1
    exact ⟨(re_le_norm _).trans_lt (hζ.trans (by linarith [dom.c₀_pos])), hq⟩
  simpa only [Function.comp_apply] using!
    (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp hcurve hmap

include hW hθ hD in
theorem cepsScaledSurrogateMarkPrefactor_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateMarkPrefactor dom ρW N lam z)
      (ball 0 (dom.entranceScaleRadius N M lam z)) := by
  exact (cepsScaledSurrogateMarkLog_differentiableOn dom hW hθ hD hf hη N hN lam hz).cexp.div
    (cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz).1
    (fun b hb => norm_pos_iff.mp ((div_pos (cepsVarLo_pos hD) (by norm_num : (0 : ℝ) < 4)).trans_le
      ((cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz).2 b hb)))

end PGM
