import PLAStochastic.Index.CEPS.Normal.Defs

/-! # Compatibility of the existing Morse-root quotient with the normal data -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

theorem cepsNormalData_root_compatibility (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ q : ℂ}
    (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    (cepsNormalData D θ ρW μ q).ψp =
      (cepsNormalData D θ ρW μ q).eta * (cepsNormalData D θ ρW μ q).Q
        (cepsNormalData D θ ρW μ q).βp ∧
    (cepsNormalData D θ ρW μ q).ψm =
      -(cepsNormalData D θ ρW μ q).eta * (cepsNormalData D θ ρW μ q).Q
        (cepsNormalData D θ ρW μ q).βm := by
  let bp := cepsRootPlus D θ ρW μ q
  let bm := cepsRootMinus D θ ρW μ q
  let H := cepsRootQuot D θ ρW μ q
  have hH := differentiableOn_cepsRootQuot hW hθ hD hμ hr
  have hbp := rootPlus_mem_ball hW hθ hD hμ hr
  have hbm := rootMinus_mem_ball hW hθ hD hμ hr
  have hHp := ((hH bp hbp).differentiableAt (isOpen_ball.mem_nhds hbp)).hasDerivAt
  have hHm := ((hH bm hbm).differentiableAt (isOpen_ball.mem_nhds hbm)).hasDerivAt
  have hQp : cepsQuotA D θ ρW μ q bp = H bp := by
    rw [cepsQuotA, cepsRootEq_rootPlus hW hθ hD hμ hr, dslope_same]
    rw [(Complex.hasDerivAt_exp 0).deriv, exp_zero, mul_one]
  have hQm : cepsQuotA D θ ρW μ q bm = H bm := by
    rw [cepsQuotA, cepsRootEq_rootMinus hW hθ hD hμ hr, dslope_same]
    rw [(Complex.hasDerivAt_exp 0).deriv, exp_zero, mul_one]
  have hqp := ((hasDerivAt_id bp).sub_const bp).mul ((hasDerivAt_id bp).sub_const bm)
  have hqm := ((hasDerivAt_id bm).sub_const bp).mul ((hasDerivAt_id bm).sub_const bm)
  have heq : (fun z => (z - bp) * (z - bm) * H z) =ᶠ[nhds bp]
      cepsRootEq ρW μ q := Filter.Eventually.of_forall fun z =>
    (cepsRootEq_eq_quad_mul hW hθ hD hμ hr z).symm
  have heq' : (fun z => (z - bp) * (z - bm) * H z) =ᶠ[nhds bm]
      cepsRootEq ρW μ q := Filter.Eventually.of_forall fun z =>
    (cepsRootEq_eq_quad_mul hW hθ hD hμ hr z).symm
  have hΦp := (hqp.mul hHp).congr_of_eventuallyEq (Filter.EventuallyEq.symm heq)
  have hΦm := (hqm.mul hHm).congr_of_eventuallyEq (Filter.EventuallyEq.symm heq')
  have hdp := ((differentiableOn_cepsRootEq hW hθ hD μ q bp hbp).differentiableAt
    (isOpen_ball.mem_nhds hbp)).hasDerivAt
  have hdm := ((differentiableOn_cepsRootEq hW hθ hD μ q bm hbm).differentiableAt
    (isOpen_ball.mem_nhds hbm)).hasDerivAt
  have hp := hdp.unique hΦp
  have hm := hdm.unique hΦm
  simp at hp hm
  change deriv (cepsCgfShift ρW μ) bp = (bp - bm) * cepsQuotA D θ ρW μ q bp ∧
    deriv (cepsCgfShift ρW μ) bm = -(bp - bm) * cepsQuotA D θ ρW μ q bm
  rw [hQp, hQm]
  have hderiv : ∀ z, deriv (cepsRootEq ρW μ q) z = deriv (cepsCgfShift ρW μ) z := by
    intro z
    exact deriv_sub_const q
  rw [hderiv] at hp hm
  exact ⟨hp, by linear_combination hm⟩

end PGM
