import PLAStochastic.Index.CEPS.Normal.ZeroHalfBridge
import PLAStochastic.ForMathlib.Analysis.Complex.ImplicitSecondDerivative

/-! # Actual first and second discount jets of the zero root -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM

def cepsRootPlusDiscountRegion (D θ : ℝ) (ρW : Measure ℝ) (μ : ℂ) : Set ℂ :=
  {q | (μ, q) ∈ cepsSPRegion D θ ρW ∧ q - cepsMorseMin D θ ρW μ ∈ slitPlane}

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem isOpen_cepsRootPlusDiscountRegion (μ : ℂ) :
    IsOpen (cepsRootPlusDiscountRegion D θ ρW μ) :=
  ((isOpen_cepsSPRegion hW hθ hD).preimage (by fun_prop)).inter
    (isOpen_slitPlane.preimage (by fun_prop))

include hW hθ hD in
theorem cepsRootPlus_q_differentiableOn (μ : ℂ) :
    DifferentiableOn ℂ (cepsRootPlus D θ ρW μ) (cepsRootPlusDiscountRegion D θ ρW μ) := by
  intro q hq
  have hj := cepsRootPlus_differentiableAt_joint hW hθ hD hq.1.1
    (norm_sqrt_lt (cepsChartRho_pos hD hθ) hq.1.2) hq.2
  simpa only [Function.comp_def] using
    (hj.comp q ((differentiableAt_const μ).prodMk differentiableAt_id)).differentiableWithinAt

include hW hθ hD in
theorem cepsRootPlus_zeroDiscount_mem_discountRegion {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    (0 : ℂ) ∈ cepsRootPlusDiscountRegion D θ ρW μ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hq : ‖(0 : ℂ)‖ ≤ dom.q₀ := by simpa using dom.q₀_pos.le
  have hr := cepsRootR_zeroDiscount_ne_zero dom hW hθ hD hμ hp.ne'
  have hne : (0 : ℂ) - cepsMorseMin D θ ρW μ ≠ 0 := by
    intro hz
    apply hr
    rw [cepsRootR, hz, sqrt_zero]
  exact ⟨dom.mem_SPRegion hW hθ hD hμ' hq,
    cepsRootR_mem_slitPlane hW hθ hD dom hμ (by simp) hne⟩

include hW hθ hD in
theorem cepsRootPlus_analyticAt_zeroDiscount {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    AnalyticAt ℂ (cepsRootPlus D θ ρW μ) 0 :=
  (cepsRootPlus_q_differentiableOn hW hθ hD μ).analyticAt
    ((isOpen_cepsRootPlusDiscountRegion hW hθ hD μ).mem_nhds
      (cepsRootPlus_zeroDiscount_mem_discountRegion dom hW hθ hD hμ hp))

include hW hθ hD in
theorem cepsRootPlus_hasDerivAt_zeroDiscount {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    HasDerivAt (cepsRootPlus D θ ρW μ) (1 / (μ : ℂ)) 0 := by
  have hr := cepsRootR_zeroDiscount_ne_zero dom hW hθ hD hμ hp.ne'
  have hne : (0 : ℂ) - cepsMorseMin D θ ρW μ ≠ 0 := by
    intro hz
    apply hr
    rw [cepsRootR, hz, sqrt_zero]
  have hq : ‖(0 : ℂ)‖ ≤ dom.q₀ := by simpa using dom.q₀_pos.le
  have hj := cepsRootPlus_actual_path_jets hW hθ hD dom
    (Qcurve := fun _ : ℝ => (0 : ℂ)) hμ hq (by simp) hne (hasDerivAt_const μ 0)
  have hd := hj.2.2.2.1
  simpa only [cepsNormalRootSlope_zeroDiscount_of_pos dom hW hθ hD hμ hp] using hd

include hW hθ hD in
theorem cepsRootPlus_hasDerivAt_deriv_zeroDiscount {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    HasDerivAt (deriv (cepsRootPlus D θ ρW μ))
      (-(cepsStepVar ρW : ℂ) / (μ : ℂ) ^ 3) 0 := by
  let U := cepsRootPlusDiscountRegion D θ ρW μ
  let V := ball (0 : ℂ) (cepsCgfRadius D θ)
  let B := cepsRootPlus D θ ρW μ
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hq : ‖(0 : ℂ)‖ ≤ dom.q₀ := by simpa using dom.q₀_pos.le
  have hr := cepsRootR_zeroDiscount_ne_zero dom hW hθ hD hμ hp.ne'
  have hne : (0 : ℂ) - cepsMorseMin D θ ρW μ ≠ 0 := by
    intro hz
    apply hr
    rw [cepsRootR, hz, sqrt_zero]
  have h0 : (0 : ℂ) ∈ U := ⟨dom.mem_SPRegion hW hθ hD hμ' hq,
    cepsRootR_mem_slitPlane hW hθ hD dom hμ (by simp) hne⟩
  have hmap : MapsTo B U V := by
    intro q hq
    exact rootPlus_mem_ball hW hθ hD hq.1.1
      (norm_sqrt_lt (cepsChartRho_pos hD hθ) hq.1.2)
  have hB0 : B 0 = 0 := (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1
  have hP : deriv (cepsCgf ρW) (B 0) + (μ : ℂ) ≠ 0 := by
    rw [hB0, deriv_cepsCgf_zero hW hθ hD, zero_add]
    exact ofReal_ne_zero.mpr hp.ne'
  have hd := hasDerivAt_deriv_of_implicit (isOpen_cepsRootPlusDiscountRegion hW hθ hD μ)
    isOpen_ball (cepsRootPlus_q_differentiableOn hW hθ hD μ)
    (differentiableOn_cepsCgf hW hθ hD) hmap h0
    (fun q hq => cepsRootPlus_equation_of_mem_SPRegion hW hθ hD hq.1) hP
  change cepsRootPlus D θ ρW μ 0 = 0 at hB0
  rw [hB0, deriv_deriv_cepsCgf_zero hW hθ hD, deriv_cepsCgf_zero hW hθ hD, zero_add] at hd
  exact hd

end PGM
