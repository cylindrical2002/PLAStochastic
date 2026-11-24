import PLAStochastic.Index.CEPS.Scaled.SurrogateGJoint
import PLAStochastic.Index.CEPS.Scaled.SurrogateDividedDenominator

/-! # The genuinely removable scaled surrogate entrance -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateEntrance {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  -exp (cepsCanonDriftTaylor dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) *
    dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b)
      (cepsScaledSignedRoot D θ ρW lam z (-1) b))
        (cepsScaledSignedRoot D θ ρW lam z 1 b) (b * z) /
          (cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z) *
            cepsScaledSurrogateDenominator dom ρW N lam z b)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateMarkQuotient_budget (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (fun b => cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z))
      (ball 0 (dom.entranceScaleRadius N M lam z)) ∧
    ∀ b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z),
      cepsVarLo D / 4 ≤ ‖cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)‖ := by
  have hbase : ∀ b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z),
      b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) ∧ ‖b ^ 2 * z‖ < dom.c₀ / 2 := by
    intro b hb
    have h := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb
      (entranceScaleCurve_mark_mem dom hD N M lam hb)
    simpa only [pow_two, mul_assoc] using h
  have hmap : MapsTo (fun b : ℂ => (b, b ^ 2 * z))
      (ball 0 (dom.entranceScaleRadius N M lam z))
      (ball 0 (dom.canonScaleRadius lam z) ×ˢ ball 0 dom.ρA) := by
    intro b hb
    refine ⟨(hbase b hb).1, mem_ball_zero_iff.mpr ?_⟩
    have := (hbase b hb).2
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  have hc := (cepsScaledQuotient_differentiableOn dom hW hθ hD lam hz).comp
    (differentiableOn_id.prodMk ((differentiableOn_id.pow 2).mul_const z)) hmap
  refine ⟨hc.congr (fun b hb => (cepsScaledQuotient_eq_actual dom hW hθ hD lam hz (hbase b hb).1 (b ^ 2 * z)).symm), fun b hb => ?_⟩
  obtain ⟨hμ, hq, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) (hbase b hb).1
  exact cepsQ_norm_ge_on_rootZone dom hW hθ hD
    (hμ.le.trans (by linarith [dom.μ₀_pos])) (hq.le.trans (by linarith [dom.q₀_pos]))
      (mem_ball_zero_iff.mp (hmap hb).2)

include hW hθ hD in
theorem cepsScaledSurrogateEntrance_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateEntrance dom ρW N lam z)
      (ball 0 (dom.entranceScaleRadius N M lam z)) := by
  let U : Set ℂ := ball 0 (dom.entranceScaleRadius N M lam z)
  have hmapMark : MapsTo (fun b : ℂ => (b, b * z)) U
      (U ×ˢ ball 0 (dom.entranceSpatialScaleRadius lam z)) :=
    fun _ hb => ⟨hb, entranceScaleCurve_mark_mem dom hD N M lam hb⟩
  have hNc := (cepsScaledSurrogateG_second_dslope_differentiableOn_joint dom hW hθ hD hf hη N hN lam hz).comp
    (differentiableOn_id.prodMk (differentiableOn_id.mul_const z)) hmapMark
  have hNn : DifferentiableOn ℂ (fun b =>
      dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b)
        (cepsScaledSignedRoot D θ ρW lam z (-1) b))
          (cepsScaledSignedRoot D θ ρW lam z 1 b) (b * z)) U := by
    simpa only [Function.comp_apply] using! hNc
  have hbase : ∀ b ∈ U, b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) ∧ ‖b ^ 2 * z‖ < dom.c₀ / 2 := by
    intro b hb
    have h := entranceScaleCurve_spatial_bounds dom hW hθ hD N M lam hb (hmapMark hb).2
    simpa only [pow_two, mul_assoc] using h
  have hcurve : DifferentiableOn ℂ (fun b : ℂ =>
      (b * (lam : ℂ), (cepsComplexScaledDiscount lam z b, b ^ 2 * z))) U := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have hmapL : MapsTo (fun b : ℂ =>
      (b * (lam : ℂ), (cepsComplexScaledDiscount lam z b, b ^ 2 * z))) U
      {x : ℂ × (ℂ × ℂ) | x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2} := by
    intro b hb
    have hζ := (hbase b hb).2
    have hq := (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) (hbase b hb).1).2.1
    exact ⟨(re_le_norm _).trans_lt (hζ.trans (by linarith [dom.c₀_pos])), hq⟩
  have hLc := (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp hcurve hmapL
  have hL : DifferentiableOn ℂ (fun b =>
      cepsCanonDriftTaylor dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) U := by
    simpa only [Function.comp_apply] using! hLc
  obtain ⟨hQ, hQb⟩ := cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N M lam hz
  have hQ0 : ∀ b ∈ U, cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z) ≠ 0 := by
    intro b hb
    exact norm_pos_iff.mp ((div_pos (cepsVarLo_pos hD) (by norm_num)).trans_le (hQb b hb))
  have hsub : U ⊆ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z) := ball_subset_ball (min_le_left _ _)
  have hS := (cepsScaledSurrogateDenominator_differentiableOn dom hW hθ hD hf hη hM N hN lam hz).mono hsub
  exact (hL.cexp.neg.mul hNn).div (hQ.mul hS) (fun b hb => mul_ne_zero (hQ0 b hb)
    (cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz (hsub hb)))

end PGM
