import PLAStochastic.Index.CEPS.Scaled.TrueGDriftContinuity
import PLAStochastic.Index.CEPS.Scaled.TrueMarkPrefactor

/-! # Surrogate marked-prefactor continuity in real drift -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateMarkPrefactor_continuousOn_drift {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    {U : Set ℝ} (hU : IsOpen U) (b : ℝ) (z : ℂ)
    (hmark : ‖(b : ℂ) ^ 2 * z‖ < dom.c₀ / 2)
    (hcoords : ∀ lam ∈ U, |b * lam| < dom.μ₀ / 4 ∧
      ‖cepsComplexScaledDiscount lam z b‖ < dom.q₀ / 2 ∧
      0 ≤ (cepsComplexScaledDiscount lam z b).re) :
    ContinuousOn (fun lam => cepsScaledSurrogateMarkPrefactor dom ρW N lam z b) U := by
  have hqcont : Continuous (fun lam : ℝ => cepsComplexScaledDiscount lam z b) := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have hQ0 := cepsQ_continuousOn_joint_real_curve dom hW hθ hD hU
    (μ := fun lam => b * lam) (q := fun lam => cepsComplexScaledDiscount lam z b)
    (by fun_prop) hqcont.continuousOn
    (fun lam hlam => (hcoords lam hlam).1.le.trans (by linarith [dom.μ₀_pos]))
    (fun lam hlam => (hcoords lam hlam).2.1.le.trans (half_le_self dom.q₀_pos.le))
    (fun lam hlam => (hcoords lam hlam).2.2)
  have hmarkA : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) dom.ρA := by
    apply mem_ball_zero_iff.mpr
    have := dom.c₀_le
    have := dom.ρA_pos
    linarith
  have hQ : ContinuousOn (fun lam : ℝ =>
      cepsQ D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)) U := by
    simpa only [Function.comp_def, ofReal_mul] using
      hQ0.comp (s := U) (f := fun lam : ℝ => (lam, (b : ℂ) ^ 2 * z))
        (by fun_prop) (fun lam hlam => ⟨hlam, hmarkA⟩)
  have hL : ContinuousOn (fun lam : ℝ => cepsCanonDriftTaylor dom ρW N
      ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z)) U :=
    (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).continuousOn.comp
      (f := fun lam : ℝ => ((b : ℂ) * lam,
        (cepsComplexScaledDiscount lam z b, (b : ℂ) ^ 2 * z))) (by
          unfold cepsComplexScaledDiscount
          fun_prop) (fun lam hlam =>
            ⟨(re_le_norm _).trans_lt (hmark.trans (half_lt_self dom.c₀_pos)), (hcoords lam hlam).2.1⟩)
  have hQne : ∀ lam ∈ U,
      cepsQ D θ ρW ((b : ℂ) * lam) (cepsComplexScaledDiscount lam z b) ((b : ℂ) ^ 2 * z) ≠ 0 := by
    intro lam hlam
    have hμ : ‖(b : ℂ) * (lam : ℂ)‖ ≤ dom.μ₀ := by
      rw [← ofReal_mul, norm_real, Real.norm_eq_abs]
      linarith [(hcoords lam hlam).1, dom.μ₀_pos]
    exact norm_pos_iff.mp ((div_pos (cepsVarLo_pos hD) (by norm_num)).trans_le
      (cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ
        ((hcoords lam hlam).2.1.le.trans (half_le_self dom.q₀_pos.le)) (mem_ball_zero_iff.mp hmarkA)))
  exact hL.cexp.div hQ hQne

end PGM
