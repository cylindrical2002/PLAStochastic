import PLAStochastic.Index.CEPS.Scaled.QuotientJointJets
import PLAStochastic.Index.CEPS.Scaled.CanonRootJets
import PLAStochastic.Index.CEPS.Scaled.SurrogateOrigin
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetAlgebra

/-! # Explicit finite mixed-jet model for the entire scaled spatial kernel -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries Asymptotics
open PGM.WienerHopf
namespace PGM

def cepsKernelGJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  exp (-ξ * (1 + b * lam)) * (cepsCumulantJetQuotient p N lam z b ξ *
    exp (-2 * cepsCanonJetPolynomial p N (b * lam) (cepsComplexScaledDiscount lam z b) (b * ξ)))

theorem cepsKernelGJetModel_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) (lam : ℝ) (z : ℂ) :
    cepsKernelGJetModel p N lam z = cepsKernelGJetModel p' N lam z := by
  have hQ := cepsCumulantJetQuotient_congr N
    (fun i hi => hp i (hi.trans_le (cepsJetDim_monotone (by omega : N ≤ 4 * N)))) lam z
  funext b ξ
  simp only [cepsKernelGJetModel, hQ, cepsCanonJetPolynomial_congr N hp]

theorem cepsKernelGJetModel_curve_analyticAt (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z : ℂ) {ξ : ℂ → ℂ} (hξ : AnalyticAt ℂ ξ 0) :
    AnalyticAt ℂ (fun b => cepsKernelGJetModel p N lam z b (ξ b)) 0 := by
  have hμ : AnalyticAt ℂ (fun b : ℂ => b * lam) 0 := by fun_prop
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount lam z) 0 := by
    unfold cepsComplexScaledDiscount; fun_prop
  have hζ := analyticAt_id.mul hξ
  have hL := cepsCanonJetPolynomial_curve_analyticAt p N hμ hq hζ
  have hQ := cepsCumulantJetQuotient_curve_analyticAt p N lam z hξ
  have hE : AnalyticAt ℂ (fun b : ℂ => exp (-ξ b * (1 + b * lam))) 0 := by fun_prop
  exact hE.mul (hQ.mul ((analyticAt_const.mul hL).cexp))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledSurrogateG_curve_analyticAt {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {ξ : ℂ → ℂ} (hξ : AnalyticAt ℂ ξ 0) :
    AnalyticAt ℂ (fun b => cepsScaledSurrogateG dom ρW N lam z b (ξ b)) 0 := by
  have hμ : AnalyticAt ℂ (fun b : ℂ => b * lam) 0 := by fun_prop
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount lam z) 0 := by
    unfold cepsComplexScaledDiscount; fun_prop
  have hζ := analyticAt_id.mul hξ
  have hL := cepsCanonDriftTaylor_curve_analyticAt dom hW hθ hD hf hη N hN
    hμ hq hζ (by simp [cepsComplexScaledDiscount]) (by simp)
  have hQ := cepsScaledQuotient_curve_analyticAt dom hW hθ hD lam hz hξ
  have hE : AnalyticAt ℂ (fun b : ℂ => exp (-ξ b * (1 + b * lam))) 0 := by fun_prop
  have ha := hE.mul (hQ.mul (((analyticAt_const (v := (-2 : ℂ))).mul hL).cexp))
  apply ha.congr
  filter_upwards [ball_mem_nhds (0 : ℂ) (canonScaleRadius_pos dom hW hθ hD lam z)] with b hb
  simp only [Pi.mul_apply, Function.comp_apply, cepsScaledSurrogateG, cepsCanonSurrogateWeight,
    cepsScaledQuotient_eq_actual dom hW hθ hD lam hz hb]
  rfl

include hθ hD in
theorem cepsScaledSurrogateG_curve_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re →
      ∀ {ξ : ℂ → ℂ}, AnalyticAt ℂ ξ 0 → ∀ j ≤ N,
        coeff j (complexTaylorSeries (fun b => cepsScaledSurrogateG dom ρW N lam z b (ξ b)) 0) =
        coeff j (complexTaylorSeries (fun b => cepsKernelGJetModel (cepsJet f) N lam z b (ξ b)) 0) := by
  obtain ⟨r, hr, he⟩ := cepsCanonDriftTaylor_taylorJets_eq_jetPolynomial dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz ξ hξ
  have hμ : AnalyticAt ℂ (fun b : ℂ => b * lam) 0 := by fun_prop
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount lam z) 0 := by
    unfold cepsComplexScaledDiscount; fun_prop
  have hζ := analyticAt_id.mul hξ
  have hLA := cepsCanonDriftTaylor_curve_analyticAt dom hW hθ hD hfS hηc N (by omega)
    hμ hq hζ (by simp [cepsComplexScaledDiscount]) (by simp)
  have hLM := cepsCanonJetPolynomial_curve_analyticAt (cepsJet f) N hμ hq hζ
  have heL := he hW hfW hneg hη hf hfS hηc hclose N hN hμ hq hζ
    (by simp [cepsComplexScaledDiscount]) (by simp)
  have heExp := complexTaylorSeries_coeff_eq_composition hLA hLM
    (F := fun x : ℂ => exp (-2 * x)) (by fun_prop) N heL
  have hEA : AnalyticAt ℂ (fun b => exp (-2 * cepsCanonDriftTaylor dom ρW N
      (b * lam) (cepsComplexScaledDiscount lam z b) (b * ξ b))) 0 :=
    (analyticAt_const.mul hLA).cexp
  have hEM : AnalyticAt ℂ (fun b => exp (-2 * cepsCanonJetPolynomial (cepsJet f) N
      (b * lam) (cepsComplexScaledDiscount lam z b) (b * ξ b))) 0 :=
    (analyticAt_const.mul hLM).cexp
  have hQA := cepsScaledQuotient_curve_analyticAt dom hW hθ hD lam hz hξ
  have hQM := cepsCumulantJetQuotient_curve_analyticAt (cepsJet f) N lam z hξ
  have heQ := cepsScaledQuotient_curve_taylorJets_eq_finite_model dom hW hθ hD hfW N lam hz hξ
  have heW := complexTaylorSeries_coeff_eq_mul hQA hEA hQM hEM N heQ heExp
  have hE : AnalyticAt ℂ (fun b : ℂ => exp (-ξ b * (1 + b * lam))) 0 := by fun_prop
  have heG := complexTaylorSeries_coeff_eq_mul hE (hQA.mul hEA) hE (hQM.mul hEM) N
    (fun _ _ => rfl) heW
  have haG := cepsScaledSurrogateG_curve_analyticAt dom hW hθ hD hfS hηc N (by omega) lam hz hξ
  have hmG := cepsKernelGJetModel_curve_analyticAt (cepsJet f) N lam z hξ
  have herr := isBigO_difference_of_complexTaylorSeries_coeff_eq
    (hE.mul (hQA.mul hEA)) (hE.mul (hQM.mul hEM)) N heG
  have herr' : (fun b => cepsScaledSurrogateG dom ρW N lam z b (ξ b) -
      cepsKernelGJetModel (cepsJet f) N lam z b (ξ b)) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    apply herr.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [ball_mem_nhds (0 : ℂ) (canonScaleRadius_pos dom hW hθ hD lam z)] with b hb
    simp only [Pi.mul_apply, cepsScaledSurrogateG, cepsCanonSurrogateWeight,
      cepsKernelGJetModel,
      cepsScaledQuotient_eq_actual dom hW hθ hD lam hz hb]
  exact complexTaylorSeries_coeff_eq_of_isBigO haG hmG N herr'

end PGM
