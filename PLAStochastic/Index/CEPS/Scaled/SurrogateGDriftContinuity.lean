import PLAStochastic.Index.CEPS.Scaled.TrueGDriftContinuity
import PLAStochastic.Index.CEPS.Scaled.SurrogateGJoint

/-! # Joint real-drift and spatial continuity of the finite surrogate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateG_continuousOn_joint_drift_spatial {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    {U : Set ℝ} (hU : IsOpen U) (b : ℝ) (z : ℂ) {S : ℝ}
    (hS : ‖(b : ℂ)‖ * S < dom.c₀ / 2)
    (hcoords : ∀ lam ∈ U, |b * lam| < dom.μ₀ / 4 ∧
      ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀ / 2 ∧
      0 ≤ (cepsComplexScaledDiscount lam z b).re) :
    ContinuousOn (fun x : ℝ × ℂ => cepsScaledSurrogateG dom ρW N x.1 z b x.2)
      (U ×ˢ ball 0 S) := by
  have hqcont : Continuous (fun lam : ℝ => cepsComplexScaledDiscount lam z b) := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have hQ0 := cepsQ_continuousOn_joint_real_curve dom hW hθ hD hU
    (μ := fun lam => b * lam) (q := fun lam => cepsComplexScaledDiscount lam z b)
    (by fun_prop) hqcont.continuousOn
    (fun lam hlam => (hcoords lam hlam).1.le.trans (by linarith [dom.μ₀_pos]))
    (fun lam hlam => (hcoords lam hlam).2.1.le.trans (half_le_self dom.q₀_pos.le))
    (fun lam hlam => (hcoords lam hlam).2.2)
  have hsp : ∀ x ∈ U ×ˢ ball (0 : ℂ) S, ‖(b : ℂ) * x.2‖ < dom.c₀ / 2 := by
    intro x hx
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx.2).le (norm_nonneg _)).trans_lt hS
  have hQ : ContinuousOn (fun x : ℝ × ℂ =>
      cepsQ D θ ρW ((b : ℂ) * x.1) (cepsComplexScaledDiscount x.1 z b) ((b : ℂ) * x.2))
      (U ×ˢ ball 0 S) := by
    have hc := hQ0.comp
      (s := U ×ˢ ball (0 : ℂ) S) (f := fun x : ℝ × ℂ => (x.1, (b : ℂ) * x.2)) (by fun_prop) (by
        intro x hx
        refine ⟨hx.1, mem_ball_zero_iff.mpr ?_⟩
        have := hsp x hx
        have := dom.c₀_le
        have := dom.ρA_pos
        linarith)
    simpa only [ofReal_mul, Function.comp_def] using hc
  have hL : ContinuousOn (fun x : ℝ × ℂ => cepsCanonDriftTaylor dom ρW N
      ((b : ℂ) * x.1) (cepsComplexScaledDiscount x.1 z b) ((b : ℂ) * x.2))
      (U ×ˢ ball 0 S) :=
    (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).continuousOn.comp
      (f := fun x : ℝ × ℂ => ((b : ℂ) * x.1,
        (cepsComplexScaledDiscount x.1 z b, (b : ℂ) * x.2))) (by
          unfold cepsComplexScaledDiscount
          fun_prop) (fun x hx =>
            ⟨(re_le_norm _).trans_lt ((hsp x hx).trans (half_lt_self dom.c₀_pos)), (hcoords x.1 hx.1).2.1⟩)
  have hE : Continuous (fun x : ℝ × ℂ => exp (-x.2 * (1 + (b : ℂ) * x.1))) := by fun_prop
  exact hE.continuousOn.mul (hQ.mul (hL.const_mul (-2)).cexp)

include hW hθ hD in
theorem cepsScaledSurrogateG_spatial_differentiableOn_of_curve_bounds {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    (b lam : ℝ) (z : ℂ) {S : ℝ} (hS : ‖(b : ℂ)‖ * S < dom.c₀ / 2)
    (hμ : |b * lam| ≤ dom.μ₀) (hq : ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀ / 2) :
    DifferentiableOn ℂ (cepsScaledSurrogateG dom ρW N lam z b) (ball 0 S) := by
  have hμc : ‖(b : ℂ) * (lam : ℂ)‖ ≤ dom.μ₀ := by
    simpa only [← ofReal_mul, norm_real, Real.norm_eq_abs] using hμ
  have hζ : ∀ ξ ∈ ball (0 : ℂ) S, ‖(b : ℂ) * ξ‖ < dom.c₀ / 2 := by
    intro ξ hξ
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hξ).le (norm_nonneg _)).trans_lt hS
  have hQ : DifferentiableOn ℂ (fun ξ : ℂ => cepsQ D θ ρW
      ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) * ξ)) (ball 0 S) := by
    intro ξ hξ
    have hA : (b : ℂ) * ξ ∈ ball (0 : ℂ) dom.ρA := by
      apply mem_ball_zero_iff.mpr
      have := hζ ξ hξ
      have := dom.c₀_le
      have := dom.ρA_pos
      linarith
    exact ((CepsC6.differentiableAt_cepsQ dom hW hθ hD hμc
      (hq.le.trans (half_le_self dom.q₀_pos.le)) hA).comp ξ (by fun_prop)).differentiableWithinAt
  have hL := (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp
    (s := ball (0 : ℂ) S) (f := fun ξ : ℂ => ((b : ℂ) * lam,
      (cepsComplexScaledDiscount lam z b, (b : ℂ) * ξ))) (by fun_prop)
    (fun ξ hξ => ⟨(re_le_norm _).trans_lt ((hζ ξ hξ).trans (half_lt_self dom.c₀_pos)), hq⟩)
  have hw : DifferentiableOn ℂ (fun ξ : ℂ => cepsCanonSurrogateWeight dom ρW N
      ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) * ξ)) (ball 0 S) :=
    hQ.mul (hL.const_mul (-2)).cexp
  have hE : DifferentiableOn ℂ (fun ξ : ℂ => exp (-ξ * (1 + (b : ℂ) * lam))) (ball 0 S) := by fun_prop
  exact hE.mul hw

end PGM
