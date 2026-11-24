import PLAStochastic.Index.CEPS.Scaled.QuotientSpatialJets
import PLAStochastic.Index.CEPS.Scaled.DiscountFrequencyTaylor
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesCongr

/-! # Explicit finite cumulant-jet model of the genuine marked discount -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

def cepsKernelMarkedDiscountJetModel (p : ℕ → ℝ) (N : ℕ) (z b : ℂ) : ℂ :=
  -cepsCumulantQuotientSpatialUnit p N 0 z b (b * z)

theorem cepsKernelMarkedDiscountJetModel_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) (z : ℂ) :
    cepsKernelMarkedDiscountJetModel p N z = cepsKernelMarkedDiscountJetModel p' N z := by
  funext b
  simp only [cepsKernelMarkedDiscountJetModel, cepsCumulantQuotientSpatialUnit_congr N hp]

theorem cepsKernelMarkedDiscountJetModel_analyticAt (p : ℕ → ℝ) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (cepsKernelMarkedDiscountJetModel p N z) 0 := by
  have hc : AnalyticAt ℂ (fun b : ℂ => (b, b * z)) 0 := analyticAt_id.prod (analyticAt_id.mul analyticAt_const)
  have hU : AnalyticAt ℂ (fun x : ℂ × ℂ => cepsCumulantQuotientSpatialUnit p N 0 z x.1 x.2) (0, 0 * z) := by
    simpa only [zero_mul] using cepsCumulantQuotientSpatialUnit_joint_analyticAt p N 0 z (0, 0)
  exact (hU.comp
    (x := (0 : ℂ)) (f := fun b : ℂ => (b, b * z)) hc).neg

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMarkedDiscount_eq_spatialUnit (z b : ℂ)
    (hbz : ‖b * (b * z)‖ < cepsCgfRadius D θ) :
    cepsScaledMarkedDiscount ρW z b = -cepsScaledQuotientSpatialUnit ρW 0 z b (b * z) := by
  by_cases hb : b = 0
  · subst b
    simp [cepsScaledMarkedDiscount_zero hW hθ hD, cepsScaledQuotientSpatialUnit,
      quadraticExpUnit_zero, cepsScaledQuadraticEquation]
  · rw [cepsScaledMarkedDiscount_eq_div hW hθ hD z hb]
    have he := cepsD_scaled_eq_quadraticSpatialUnit hW hθ hD 0 z b (b * z) hbz
    have hDD : cepsD ρW (b * (0 : ℝ)) (b ^ 2 * z * (1 + b * (0 : ℝ))) (b * (b * z)) =
        cepsMarkedDiscount ρW (b ^ 2 * z) := by
      simp [cepsD, cepsMarkedDiscount, pow_two, mul_assoc]
    rw [hDD] at he
    apply (div_eq_iff (pow_ne_zero 2 hb)).mpr
    calc
      cepsMarkedDiscount ρW (b ^ 2 * z) = -(-cepsMarkedDiscount ρW (b ^ 2 * z)) := by ring
      _ = -(b ^ 2 * cepsScaledQuotientSpatialUnit ρW 0 z b (b * z)) := by rw [he]
      _ = -cepsScaledQuotientSpatialUnit ρW 0 z b (b * z) * b ^ 2 := by ring

include hW hθ hD in
theorem cepsScaledMarkedDiscount_taylorJets_eq_finite_model (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (z : ℂ) : ∀ j ≤ N,
    coeff j (complexTaylorSeries (cepsScaledMarkedDiscount ρW z) 0) =
      coeff j (complexTaylorSeries (cepsKernelMarkedDiscountJetModel (cepsJet f) N z) 0) := by
  obtain ⟨C, B, hC, hB, he⟩ := cepsScaledQuotientSpatialUnit_jet_budget hW hθ hD hfW N 0 z (by norm_num : (0 : ℝ) < 1)
  have hx : ContinuousAt (fun b : ℂ => b * z) 0 := by fun_prop
  have hq : ContinuousAt (fun b : ℂ => b * (b * z)) 0 := by fun_prop
  have hx0 : (0 : ℂ) * z ∈ ball (0 : ℂ) 1 := by rw [zero_mul]; exact mem_ball_self one_pos
  have hq0 : (0 : ℂ) * (0 * z) ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
    rw [zero_mul]; exact mem_ball_self (cepsCgfRadius_pos hD hθ)
  have hev : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B ∧ b * z ∈ ball (0 : ℂ) 1 ∧
      b * (b * z) ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
    exact (show ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B from ball_mem_nhds _ hB).and
      ((hx.eventually (isOpen_ball.mem_nhds hx0)).and
        (hq.eventually (isOpen_ball.mem_nhds hq0)))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hRA : 0 < cepsDiscountFrequencyBase D θ / (1 + Real.sqrt ‖z‖) := by
    positivity [cepsDiscountFrequencyBase_pos hD hθ]
  apply complexTaylorSeries_coeff_eq_of_difference_le
    ((cepsScaledMarkedDiscount_frequency_differentiableOn hW hθ hD z).analyticAt (ball_mem_nhds _ hRA))
    (cepsKernelMarkedDiscountJetModel_analyticAt (cepsJet f) N z) N hR hC
  intro b hb hbR
  have hbc : (b : ℂ) ∈ ball (0 : ℂ) R := by simpa [mem_ball_zero_iff, norm_real, abs_of_pos hb] using hbR
  obtain ⟨hbB, hbξ, hbq⟩ := hball hbc
  rw [cepsScaledMarkedDiscount_eq_spatialUnit hW hθ hD z b (mem_ball_zero_iff.mp hbq), cepsKernelMarkedDiscountJetModel]
  simpa only [neg_sub_neg, norm_sub_rev, norm_real, Real.norm_eq_abs, abs_of_pos hb] using he hbB hbξ

end PGM
