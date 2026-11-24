import PLAStochastic.Index.CEPS.Scaled.KernelFiniteSlopeJets
import PLAStochastic.Index.CEPS.Scaled.MarkQuotientJets
import PLAStochastic.Index.CEPS.Scaled.SurrogateEntrance
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetDivision

/-! # Exact finite mixed-jet coefficients of the genuine removable entrance -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledSurrogateEntranceSlope_analyticAt {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (fun b => dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b)
      (cepsScaledSignedRoot D θ ρW lam z (-1) b)) (cepsScaledSignedRoot D θ ρW lam z 1 b) (b * z)) 0 := by
  let M : ℝ := cepsSobolev m η fW
  let U : Set ℂ := ball 0 (dom.entranceScaleRadius N M lam z)
  have hmap : MapsTo (fun b : ℂ => (b, b * z)) U
      (U ×ˢ ball 0 (dom.entranceSpatialScaleRadius lam z)) :=
    fun _ hb => ⟨hb, entranceScaleCurve_mark_mem dom hD N M lam hb⟩
  have hNc := (cepsScaledSurrogateG_second_dslope_differentiableOn_joint dom hW hθ hD hf hη N hN lam hz).comp
    (differentiableOn_id.prodMk (differentiableOn_id.mul_const z)) hmap
  have hNs : DifferentiableOn ℂ (fun b => dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b)
      (cepsScaledSignedRoot D θ ρW lam z (-1) b)) (cepsScaledSignedRoot D θ ρW lam z 1 b) (b * z)) U := by
    simpa only [Function.comp_apply] using! hNc
  exact hNs.analyticAt (ball_mem_nhds _ (entranceScale_constants dom hW hθ hD N M lam z).1)

include hθ hD in
theorem cepsScaledSurrogateEntrance_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → ∀ j ≤ N,
        coeff j (complexTaylorSeries (cepsScaledSurrogateEntrance dom ρW N lam z) 0) =
        coeff j (complexTaylorSeries (cepsKernelEntranceJetModel (cepsJet f) N lam z) 0) := by
  obtain ⟨rL, hrL, heL⟩ := cepsCanonDriftTaylor_taylorJets_eq_jetPolynomial dom hθ hD
  obtain ⟨rS, hrS, heS⟩ := cepsScaledSurrogate_finite_slope_jets dom hθ hD
  refine ⟨min rL rS, lt_min hrL hrS, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz
  have hμ : AnalyticAt ℂ (fun b : ℂ => b * lam) 0 := by fun_prop
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount lam z) 0 := by unfold cepsComplexScaledDiscount; fun_prop
  have hζ : AnalyticAt ℂ (fun b : ℂ => b ^ 2 * z) 0 := by fun_prop
  have hLA := cepsCanonDriftTaylor_curve_analyticAt dom hW hθ hD hfS hηc N (by omega)
    hμ hq hζ (by simp [cepsComplexScaledDiscount]) (by simp)
  have hLM := cepsCanonJetPolynomial_curve_analyticAt (cepsJet f) N hμ hq hζ
  have heLc := heL hW hfW hneg hη hf hfS hηc (hclose.trans (min_le_left rL rS)) N hN
    hμ hq hζ (by simp [cepsComplexScaledDiscount]) (by simp)
  have heE := complexTaylorSeries_coeff_eq_composition hLA hLM (F := fun x : ℂ => -exp x)
    (by fun_prop) N heLc
  have hQS := cepsMarkedQuotient_analyticAt_and_finite_jets dom hW hθ hD hfW N lam hz
  have hmark : AnalyticAt ℂ (fun b : ℂ => b * z) 0 := by fun_prop
  have hQM := cepsCumulantJetQuotient_curve_analyticAt (cepsJet f) N lam z hmark
  have hAS := cepsScaledSurrogateEntranceSlope_analyticAt dom hW hθ hD hfS hηc N (by omega) lam hz
  have hMS := cepsKernelFiniteSlopes_analyticAt (cepsJet f) N lam z
  have heSS := heS hW hfW hneg hη hf hfS hηc (hclose.trans (min_le_right rL rS)) N hN lam hz
  have heNum := complexTaylorSeries_coeff_eq_mul hLA.cexp.neg hAS hLM.cexp.neg hMS.2 N heE heSS.2
  have hRadius := surrogateRegularScaleRadius_pos dom hW hθ hD N (cepsSobolev m η fW) lam z
  have hDA := (cepsScaledSurrogateDenominator_differentiableOn dom hW hθ hD hfS hηc
    le_rfl N (by omega) lam hz).analyticAt (ball_mem_nhds _ hRadius)
  have hD0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hfS hηc le_rfl N (by omega)
    lam hz (mem_ball_self hRadius)
  have hEntranceRadius := (entranceScale_constants dom hW hθ hD N (cepsSobolev m η fW) lam z).1
  have hQbound := (cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N (cepsSobolev m η fW) lam hz).2
    0 (mem_ball_self hEntranceRadius)
  have hQ0 : cepsQ D θ ρW (0 * lam) (cepsComplexScaledDiscount lam z 0) (0 ^ 2 * z) ≠ 0 :=
    norm_pos_iff.mp ((by positivity [cepsVarLo_pos hD] : 0 < cepsVarLo D / 4).trans_le hQbound)
  have heDen := complexTaylorSeries_coeff_eq_mul hQS.1 hDA hQM hMS.1 N hQS.2 heSS.1
  exact complexTaylorSeries_coeff_eq_div (hLA.cexp.neg.mul hAS) (hQS.1.mul hDA)
    (hLM.cexp.neg.mul hMS.2) (hQM.mul hMS.1) (mul_ne_zero hQ0 hD0) N heNum heDen

end PGM
