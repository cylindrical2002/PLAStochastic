import PLAStochastic.Index.CEPS.Normal.ActualQuotientContinuity
import PLAStochastic.Index.CEPS.Canonical.JointDifferential
import PLAStochastic.Index.CEPS.Scaled.TrueSpatialError

/-! # Joint real-drift and spatial continuity of the actual scaled family -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueG_continuousOn_joint_drift_spatial {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {U : Set ℝ} (hU : IsOpen U) (b : ℝ) (z : ℂ) {S : ℝ}
    (hS : ‖(b : ℂ)‖ * S < dom.c₀ / 2)
    (hcoords : ∀ lam ∈ U, |b * lam| < dom.μ₀ / 4 ∧
      ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀ / 2 ∧
      0 ≤ (cepsComplexScaledDiscount lam z b).re) :
    ContinuousOn (fun x : ℝ × ℂ => cepsScaledTrueG dom ρW x.1 z b x.2)
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
      cepsQ D θ ρW ((b * x.1 : ℝ) : ℂ) (cepsComplexScaledDiscount x.1 z b) ((b : ℂ) * x.2))
      (U ×ˢ ball 0 S) := hQ0.comp
    (s := U ×ˢ ball (0 : ℂ) S) (f := fun x : ℝ × ℂ => (x.1, (b : ℂ) * x.2)) (by fun_prop) (by
      intro x hx
      refine ⟨hx.1, mem_ball_zero_iff.mpr ?_⟩
      have hn := hsp x hx
      have := dom.c₀_le
      have := dom.ρA_pos
      linarith)
  have hL : ContinuousOn (fun x : ℝ × ℂ =>
      dom.canonL ρW ((b * x.1 : ℝ) : ℂ) (cepsComplexScaledDiscount x.1 z b) ((b : ℂ) * x.2))
      (U ×ˢ ball 0 S) := by
    intro x hx
    have hc := (dom.differentiableAt_canonL_real_joint hW hθ hD hf hm hη
      (hcoords x.1 hx.1).1 (hcoords x.1 hx.1).2.1
      ((re_le_norm _).trans_lt ((hsp x hx).trans (half_lt_self dom.c₀_pos)))).continuousAt
    exact (hc.comp (x := x) (f := fun x : ℝ × ℂ =>
      (b * x.1, (cepsComplexScaledDiscount x.1 z b, (b : ℂ) * x.2))) (by
        unfold cepsComplexScaledDiscount
        fun_prop)).continuousWithinAt
  have hE : Continuous (fun x : ℝ × ℂ => exp (-x.2 * (1 + (b : ℂ) * x.1))) := by fun_prop
  exact hE.continuousOn.mul (hQ.mul (hL.const_mul (-2)).cexp)

include hW hθ hD in
theorem cepsScaledTrueG_spatial_differentiableOn_of_curve_bounds
    (b lam : ℝ) (z : ℂ) {S : ℝ} (hS : ‖(b : ℂ)‖ * S < dom.c₀ / 2)
    (hμ : |b * lam| ≤ dom.μ₀) (hq : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀) :
    DifferentiableOn ℂ (cepsScaledTrueG dom ρW lam z b) (ball 0 S) := by
  have hw := (cepsCanonTrueWeight_spatial_differentiableOn dom hW hθ hD hμ hq).comp
    (s := ball (0 : ℂ) S) (f := fun ξ : ℂ => (b : ℂ) * ξ) (by fun_prop) (by
      intro ξ hξ
      apply mem_ball_zero_iff.mpr
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hξ).le (norm_nonneg _)).trans_lt hS)
  have hE : DifferentiableOn ℂ (fun ξ : ℂ => exp (-ξ * (1 + (b : ℂ) * lam))) (ball 0 S) := by fun_prop
  exact hE.mul hw

end PGM
