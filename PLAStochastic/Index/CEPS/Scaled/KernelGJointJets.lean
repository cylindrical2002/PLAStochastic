import PLAStochastic.Index.CEPS.Scaled.KernelGJetModel

/-! # Fixed spatial-disc holomorphy of the actual kernel and its finite jet model -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

theorem cepsKernelGJetModel_differentiableOn_joint (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ DifferentiableOn ℂ
      (fun x : ℂ × ℂ => cepsKernelGJetModel p N lam z x.1 x.2) (ball 0 B ×ˢ ball 0 R) := by
  obtain ⟨B, hB, hQ⟩ := cepsCumulantJetQuotient_differentiableOn_joint p N lam z hR
  have hcurve : Differentiable ℂ (fun x : ℂ × ℂ =>
      (x.1 * (lam : ℂ), (cepsComplexScaledDiscount lam z x.1, x.1 * x.2))) := by
    unfold cepsComplexScaledDiscount; fun_prop
  have hPoly : Differentiable ℂ (fun x : ℂ × (ℂ × ℂ) => cepsCanonJetPolynomial p N x.1 x.2.1 x.2.2) :=
    fun x => (cepsCanonJetPolynomial_joint_analyticAt p N x).differentiableAt
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonJetPolynomial p N
      (x.1 * lam) (cepsComplexScaledDiscount lam z x.1) (x.1 * x.2)) (ball 0 B ×ˢ ball 0 R) := by
    simpa only [Function.comp_apply] using! (hPoly.comp hcurve).differentiableOn
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-x.2 * (1 + x.1 * lam)))
      (ball 0 B ×ˢ ball 0 R) := by fun_prop
  exact ⟨B, hB, hE.mul (hQ.mul ((hL.const_mul (-2)).cexp))⟩

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledSurrogateG_fixedSpatial_differentiableOn_joint {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ DifferentiableOn ℂ
      (fun x : ℂ × ℂ => cepsScaledSurrogateG dom ρW N lam z x.1 x.2) (ball 0 B ×ˢ ball 0 R) := by
  obtain ⟨BQ, hBQ, hQc⟩ := cepsScaledQuotient_spatial_differentiableOn_joint dom hW hθ hD lam hz hR
  let B : ℝ := min BQ (min (dom.canonScaleRadius lam z) (dom.c₀ / (2 * R)))
  have hB : 0 < B := by dsimp [B]; positivity [canonScaleRadius_pos dom hW hθ hD lam z, dom.c₀_pos]
  have hbase : ∀ x ∈ ball (0 : ℂ) B ×ˢ ball (0 : ℂ) R,
      x.1 ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) ∧ ‖x.1 * x.2‖ < dom.c₀ := by
    intro x hx
    have hb := mem_ball_zero_iff.mp hx.1
    have hξ := mem_ball_zero_iff.mp hx.2
    have hBR : B * R ≤ dom.c₀ / 2 := by
      have hlimit : B ≤ dom.c₀ / (2 * R) :=
        (min_le_right BQ _).trans (min_le_right (dom.canonScaleRadius lam z) _)
      have hh := mul_le_mul_of_nonneg_right hlimit hR.le
      have he : dom.c₀ / (2 * R) * R = dom.c₀ / 2 := by field_simp [hR.ne']
      exact hh.trans_eq he
    refine ⟨ball_subset_ball ((min_le_right BQ _).trans (min_le_left _ _)) hx.1, ?_⟩
    calc
      ‖x.1 * x.2‖ = ‖x.1‖ * ‖x.2‖ := norm_mul _ _
      _ ≤ B * R := mul_le_mul hb.le hξ.le (norm_nonneg _) hB.le
      _ ≤ dom.c₀ / 2 := hBR
      _ < dom.c₀ := half_lt_self dom.c₀_pos
  have hQ : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsQ D θ ρW (x.1 * lam)
      (cepsComplexScaledDiscount lam z x.1) (x.1 * x.2)) (ball 0 B ×ˢ ball 0 R) := by
    apply (hQc.mono (fun x hx => ⟨ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩)).congr
    intro x hx
    exact (cepsScaledQuotient_eq_actual dom hW hθ hD lam hz (hbase x hx).1 (x.1 * x.2)).symm
  have hcurve : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      (x.1 * (lam : ℂ), (cepsComplexScaledDiscount lam z x.1, x.1 * x.2)))
      (ball 0 B ×ˢ ball 0 R) := by unfold cepsComplexScaledDiscount; fun_prop
  have hmap : MapsTo (fun x : ℂ × ℂ =>
      (x.1 * (lam : ℂ), (cepsComplexScaledDiscount lam z x.1, x.1 * x.2)))
      (ball 0 B ×ˢ ball 0 R) {x : ℂ × (ℂ × ℂ) | x.2.2.re < dom.c₀ ∧ ‖x.2.1‖ < dom.q₀ / 2} := by
    intro x hx
    obtain ⟨hb, hξ⟩ := hbase x hx
    exact ⟨(re_le_norm _).trans_lt hξ,
      (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hb).2.1⟩
  have hLc := (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp hcurve hmap
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonDriftTaylor dom ρW N
      (x.1 * lam) (cepsComplexScaledDiscount lam z x.1) (x.1 * x.2)) (ball 0 B ×ˢ ball 0 R) := by
    simpa only [Function.comp_apply] using! hLc
  have hE : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (-x.2 * (1 + x.1 * lam)))
      (ball 0 B ×ˢ ball 0 R) := by fun_prop
  exact ⟨B, hB, hE.mul (hQ.mul ((hL.const_mul (-2)).cexp))⟩

end PGM
