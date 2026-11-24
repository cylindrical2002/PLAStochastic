import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceBudget

/-! # Half-line scale holomorphy on the positive subtraction range -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateHalfEntrance_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateHalfEntrance dom ρW N lam z)
      (ball 0 (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) := by
  let U : Set ℂ := ball 0 (dom.pairPolynomialScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))
  have hE : U ⊆ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z) :=
    ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam z).2
  have hbase : ∀ b ∈ U, b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) ∧ ‖b ^ 2 * z‖ < dom.c₀ / 2 := by
    intro b hb
    have h := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam (hE hb)
      (entranceScaleCurve_mark_mem dom hD N M lam (hE hb))
    simpa only [pow_two, mul_assoc] using h
  have hcurve : DifferentiableOn ℂ (fun b : ℂ =>
      (b * (lam : ℂ), (cepsComplexScaledDiscount lam z b, b ^ 2 * z))) U := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have hmap : MapsTo (fun b : ℂ =>
      (b * (lam : ℂ), (cepsComplexScaledDiscount lam z b, b ^ 2 * z))) U
      {x : ℂ × (ℂ × ℂ) | x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2} := by
    intro b hb
    have hζ := (hbase b hb).2
    have hq := (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) (hbase b hb).1).2.1
    exact ⟨(re_le_norm _).trans_lt (hζ.trans (by linarith [dom.c₀_pos])), hq⟩
  have hLc := (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp hcurve hmap
  have hL : DifferentiableOn ℂ (fun b =>
      cepsCanonDriftTaylor dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) U := by
    simpa only [Function.comp_apply] using! hLc
  have hQ := ((cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz).1).mono hE
  have hQ0 : ∀ b ∈ U, cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z) ≠ 0 := by
    intro b hb
    exact norm_pos_iff.mp ((div_pos (cepsVarLo_pos hD) (by norm_num : (0 : ℝ) < 4)).trans_le
      ((cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz).2 b (hE hb)))
  have hrootSub : U ⊆ ball (0 : ℂ) (dom.actualRootScaleRadius lam z) :=
    fun b hb => ball_subset_ball (min_le_left _ _) (hbase b hb).1
  have hm := ((cepsScaledSignedRoot_budget dom hW hθ hD lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)).1).mono hrootSub
  exact hL.cexp.div (hQ.mul ((differentiableOn_id.mul_const z).sub hm))
    (fun b hb => mul_ne_zero (hQ0 b hb) (sub_ne_zero.mpr
      (cepsScaledPositiveMarkerGap_ne_zero dom hW hθ hD N M lam hlam hz hb)))

end PGM
