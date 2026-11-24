import PLAStochastic.Index.CEPS.Normal.ZeroRootNumerator

/-! # The marked half-line root numerator at zero marker -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsNormalMarkedRootNumerator (D θ : ℝ) (ρW : Measure ℝ) (μ : ℝ) (t : ℂ) : ℂ :=
  let q := t * (1 + (μ : ℂ))
  cepsNormalRootNumerator D θ ρW μ q - t *
    cepsNormalRootSlope (cepsCgf ρW) (fun (x : ℝ) q => cepsRootPlus D θ ρW x q) μ q

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormalMarkedRootNumerator_analyticAt {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    AnalyticAt ℂ (cepsNormalMarkedRootNumerator D θ ρW μ) 0 := by
  have hQ : AnalyticAt ℂ (fun t : ℂ => t * (1 + (μ : ℂ))) 0 := by fun_prop
  have hN : AnalyticAt ℂ (cepsNormalRootNumerator D θ ρW μ) (0 * (1 + (μ : ℂ))) := by
    simpa only [zero_mul] using cepsNormalRootNumerator_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  have hP : AnalyticAt ℂ
      (cepsNormalRootSlope (cepsCgf ρW) (fun (x : ℝ) q => cepsRootPlus D θ ρW x q) μ)
      (0 * (1 + (μ : ℂ))) := by
    simpa only [zero_mul] using cepsNormalRootSlope_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  exact (hN.comp (f := fun t : ℂ => t * (1 + (μ : ℂ))) hQ).sub
    (analyticAt_id.mul (hP.comp (f := fun t : ℂ => t * (1 + (μ : ℂ))) hQ))

include hW hθ hD in
theorem cepsNormalMarkedRootNumerator_zero_jets {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    cepsNormalMarkedRootNumerator D θ ρW μ 0 = 0 ∧
      deriv (cepsNormalMarkedRootNumerator D θ ρW μ) 0 = 1 ∧
      deriv (deriv (cepsNormalMarkedRootNumerator D θ ρW μ)) 0 =
        (cepsStepVar ρW : ℂ) * (1 - (μ : ℂ) ^ 2) / (μ : ℂ) ^ 2 := by
  let N := cepsNormalRootNumerator D θ ρW μ
  let P := cepsNormalRootSlope (cepsCgf ρW) (fun (x : ℝ) q => cepsRootPlus D θ ρW x q) μ
  let c : ℂ := 1 + (μ : ℂ)
  have hN : AnalyticAt ℂ N 0 := cepsNormalRootNumerator_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  have hP : AnalyticAt ℂ P 0 := cepsNormalRootSlope_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  obtain ⟨hN0, hN1, hN2⟩ := cepsNormalRootNumerator_zeroDiscount_jets dom hW hθ hD hμ hp
  change N 0 = 0 at hN0
  change deriv N 0 = 1 at hN1
  change deriv (deriv N) 0 = (cepsStepVar ρW : ℂ) / (μ : ℂ) ^ 2 at hN2
  have hP0 : P 0 = μ := cepsNormalRootSlope_zeroDiscount_of_pos dom hW hθ hD hμ hp
  have hPq := cepsNormalRootSlope_hasDerivAt_zeroDiscount dom hW hθ hD hμ hp
  have hNc : AnalyticAt ℂ (fun t : ℂ => N (c * t)) 0 := by
    have hh : AnalyticAt ℂ N (c * 0) := by simpa only [mul_zero] using hN
    exact hh.comp (by fun_prop)
  have hPc : AnalyticAt ℂ (fun t : ℂ => P (c * t)) 0 := by
    have hh : AnalyticAt ℂ P (c * 0) := by simpa only [mul_zero] using hP
    exact hh.comp (by fun_prop)
  have hNqd : HasDerivAt N 1 (c * 0) := by
    simpa only [mul_zero, hN1] using hN.differentiableAt.hasDerivAt
  have hPqd : HasDerivAt P ((cepsStepVar ρW : ℂ) / (μ : ℂ)) (c * 0) := by
    simpa only [mul_zero] using hPq
  have hNcD := hNqd.comp 0 (hasDerivAt_const_mul c)
  have hPcD := hPqd.comp 0 (hasDerivAt_const_mul c)
  have he : cepsNormalMarkedRootNumerator D θ ρW μ = fun t => N (c * t) - t * P (c * t) := by
    funext t
    simp only [cepsNormalMarkedRootNumerator, c, mul_comm t]
    rfl
  rw [he]
  refine ⟨?_, ?_, ?_⟩
  · simp only [mul_zero, hN0, zero_mul, sub_self]
  · have hd := hNcD.fun_sub ((hasDerivAt_id (0 : ℂ)).fun_mul hPcD)
    simp only [Function.comp_def, id_eq] at hd
    rw [hd.deriv]
    simp only [mul_zero, zero_mul, hP0, one_mul, add_zero]
    dsimp [c]
    ring
  · have hG : AnalyticAt ℂ (fun t => t * P (c * t)) 0 := analyticAt_id.mul hPc
    have hi : AnalyticAt ℂ (fun t : ℂ => t) 0 := analyticAt_id
    rw [deriv_deriv_sub_of_analyticAt hNc hG,
      deriv_deriv_comp_const_mul_of_analyticAt hN c,
      deriv_deriv_mul_of_analyticAt hi hPc]
    have hPcDeriv : deriv (fun t => P (c * t)) 0 = (cepsStepVar ρW : ℂ) / (μ : ℂ) * c := by
      simpa only [Function.comp_def] using hPcD.deriv
    rw [hN2, hPcDeriv]
    simp only [deriv_id'', deriv_const, zero_mul, zero_add]
    dsimp [c]
    field_simp [ofReal_ne_zero.mpr hp.ne']
    ring

end PGM
