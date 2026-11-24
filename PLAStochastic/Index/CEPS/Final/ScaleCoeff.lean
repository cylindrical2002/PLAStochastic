import PLAStochastic.Index.CEPS.Final.KernelComplexForm
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound

/-! # Scale coefficients of jointly analytic families

If `(q, z, b) ↦ F q z b` is jointly analytic for all small `b` (`‖b‖ ≤ ρ`) and bounded there,
then the `n`-th scale coefficient `(n!)⁻¹ ∂_bⁿ F q z 0` is jointly analytic in `(q, z)` and
bounded by the same bound times `(2/ρ)ⁿ`.
-/

noncomputable section
open Complex Metric Set Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cepsScaleCoeff_analyticAt {F : E → ℂ → ℂ → ℂ} {q : E} {z : ℂ}
    (hF : AnalyticAt ℂ (fun v : E × ℂ × ℂ => F v.1 v.2.1 v.2.2) (q, z, 0)) (n : ℕ) :
    AnalyticAt ℂ (fun v : E × ℂ => cepsScaleCoeff n (F v.1 v.2)) (q, z) := by
  let P : (E × ℂ) × ℂ → ℂ := fun w => F w.1.1 w.1.2 w.2
  have hP : AnalyticAt ℂ P ((q, z), 0) := by
    have hm : AnalyticAt ℂ (fun w : (E × ℂ) × ℂ => (w.1.1, w.1.2, w.2)) ((q, z), 0) :=
      (analyticAt_fst.comp analyticAt_fst).prod ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)
    exact hF.comp (x := ((q, z), (0 : ℂ))) hm
  have h := (hP.iteratedDeriv_snd n).comp (x := (q, z))
    (f := fun v : E × ℂ => (v, (0 : ℂ))) (analyticAt_id.prod analyticAt_const)
  exact analyticAt_const.mul h

theorem cepsScaleCoeff_norm_le {f : ℂ → ℂ} {ρ B : ℝ} (hρ : 0 < ρ)
    (hf : ∀ b : ℂ, ‖b‖ < ρ → DifferentiableAt ℂ f b) (hB : ∀ b : ℂ, ‖b‖ < ρ → ‖f b‖ ≤ B)
    (n : ℕ) : ‖cepsScaleCoeff n f‖ ≤ B * (2 / ρ) ^ n := by
  have hdf : DifferentiableOn ℂ f (ball 0 ρ) := fun b hb =>
    (hf b (mem_ball_zero_iff.mp hb)).differentiableWithinAt
  have hC := norm_iteratedDeriv_le_of_ball n hρ hdf fun b hb => hB b (mem_ball_zero_iff.mp hb)
  unfold cepsScaleCoeff
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f 0‖
      ≤ (n.factorial : ℝ)⁻¹ * (n.factorial * B / (ρ / 2) ^ n) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = _ := by
        have h2 : ρ / 2 = (2 / ρ)⁻¹ := by field_simp
        rw [h2, inv_pow, div_inv_eq_mul]
        field_simp

/-- Joint analyticity and the Cauchy bound for a family analytic on a scale disc. -/
theorem cepsScaleCoeff_of_family {F : E → ℂ → ℂ → ℂ} {q : E} {z : ℂ} {ρ B : ℝ} (hρ : 0 < ρ)
    (hF : ∀ b : ℂ, ‖b‖ < ρ → AnalyticAt ℂ (fun v : E × ℂ × ℂ => F v.1 v.2.1 v.2.2) (q, z, b))
    (hB : ∀ b : ℂ, ‖b‖ < ρ → ‖F q z b‖ ≤ B) (n : ℕ) :
    AnalyticAt ℂ (fun v : E × ℂ => cepsScaleCoeff n (F v.1 v.2)) (q, z) ∧
    ‖cepsScaleCoeff n (F q z)‖ ≤ B * (2 / ρ) ^ n := by
  refine ⟨cepsScaleCoeff_analyticAt (hF 0 (by simpa using hρ)) n, ?_⟩
  refine cepsScaleCoeff_norm_le hρ (fun b hb => ?_) hB n
  have hl : AnalyticAt ℂ (fun t : ℂ => (q, z, t)) b :=
    analyticAt_const.prod (analyticAt_const.prod analyticAt_id)
  exact ((hF b hb).comp (x := b) hl).differentiableAt

end PGM
