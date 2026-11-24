import PLAStochastic.Index.CEPS.Normal.ZeroRootDiscountJets
import PLAStochastic.ForMathlib.Analysis.Complex.SecondDerivativeAlgebra

/-! # The zero-discount jets of the actual half-line numerator -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM

def cepsNormalRootNumerator (D θ : ℝ) (ρW : Measure ℝ) (μ : ℝ) (q : ℂ) : ℂ :=
  cepsRootPlus D θ ρW μ q *
    cepsNormalRootSlope (cepsCgf ρW) (fun (t : ℝ) q => cepsRootPlus D θ ρW t q) μ q

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormalRootSlope_analyticAt_zeroDiscount {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    AnalyticAt ℂ
      (cepsNormalRootSlope (cepsCgf ρW) (fun (t : ℝ) q => cepsRootPlus D θ ρW t q) μ) 0 := by
  have hB := cepsRootPlus_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  have hψ : AnalyticAt ℂ (cepsCgf ρW) 0 :=
    (differentiableOn_cepsCgf hW hθ hD).analyticAt
      (ball_mem_nhds 0 (cepsCgfRadius_pos hD hθ))
  have hψ' : AnalyticAt ℂ (deriv (cepsCgf ρW)) (cepsRootPlus D θ ρW μ 0) := by
    rw [(cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1]
    exact hψ.deriv
  exact (hψ'.comp hB).add analyticAt_const

include hW hθ hD in
theorem cepsNormalRootSlope_hasDerivAt_zeroDiscount {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    HasDerivAt
      (cepsNormalRootSlope (cepsCgf ρW) (fun (t : ℝ) q => cepsRootPlus D θ ρW t q) μ)
      ((cepsStepVar ρW : ℂ) / (μ : ℂ)) 0 := by
  have hψ' := (((differentiableOn_cepsCgf hW hθ hD).deriv isOpen_ball) 0
    (mem_ball_self (cepsCgfRadius_pos hD hθ))).differentiableAt
      (ball_mem_nhds 0 (cepsCgfRadius_pos hD hθ))
  have hψB : HasDerivAt (deriv (cepsCgf ρW)) (cepsStepVar ρW)
      (cepsRootPlus D θ ρW μ 0) := by
    rw [(cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1]
    simpa only [deriv_deriv_cepsCgf_zero hW hθ hD] using hψ'.hasDerivAt
  simpa only [cepsNormalRootSlope, mul_one_div, Function.comp_def] using!
    (hψB.comp 0 (cepsRootPlus_hasDerivAt_zeroDiscount dom hW hθ hD hμ hp)).add_const (μ : ℂ)

include hW hθ hD in
theorem cepsNormalRootNumerator_analyticAt_zeroDiscount {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    AnalyticAt ℂ (cepsNormalRootNumerator D θ ρW μ) 0 :=
  (cepsRootPlus_analyticAt_zeroDiscount dom hW hθ hD hμ hp).mul
    (cepsNormalRootSlope_analyticAt_zeroDiscount dom hW hθ hD hμ hp)

include hW hθ hD in
theorem cepsNormalRootNumerator_zeroDiscount_jets {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    cepsNormalRootNumerator D θ ρW μ 0 = 0 ∧
      deriv (cepsNormalRootNumerator D θ ρW μ) 0 = 1 ∧
      deriv (deriv (cepsNormalRootNumerator D θ ρW μ)) 0 =
        (cepsStepVar ρW : ℂ) / (μ : ℂ) ^ 2 := by
  let B := cepsRootPlus D θ ρW μ
  let P := cepsNormalRootSlope (cepsCgf ρW) (fun (t : ℝ) q => cepsRootPlus D θ ρW t q) μ
  have hB0 : B 0 = 0 := (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1
  have hP0 : P 0 = μ := cepsNormalRootSlope_zeroDiscount_of_pos dom hW hθ hD hμ hp
  have hBq := cepsRootPlus_hasDerivAt_zeroDiscount dom hW hθ hD hμ hp
  have hPq := cepsNormalRootSlope_hasDerivAt_zeroDiscount dom hW hθ hD hμ hp
  have hBqq := cepsRootPlus_hasDerivAt_deriv_zeroDiscount dom hW hθ hD hμ hp
  have hB := cepsRootPlus_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  have hP := cepsNormalRootSlope_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  have hmne : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  refine ⟨?_, ?_, ?_⟩
  · change B 0 * P 0 = 0
    rw [hB0, zero_mul]
  · change deriv (fun q => B q * P q) 0 = 1
    have hdN := hBq.fun_mul hPq
    change HasDerivAt (fun q => B q * P q)
      (1 / (μ : ℂ) * P 0 + B 0 * ((cepsStepVar ρW : ℂ) / (μ : ℂ))) 0 at hdN
    rw [hdN.deriv]
    rw [hB0, hP0]
    field_simp [hmne]
    ring
  · change deriv (deriv (fun q => B q * P q)) 0 = _
    rw [deriv_deriv_mul_of_analyticAt hB hP]
    change deriv (deriv B) 0 * P 0 + 2 * deriv B 0 * deriv P 0 + B 0 * deriv (deriv P) 0 = _
    rw [hB0, hP0, hBq.deriv, hPq.deriv, hBqq.deriv]
    field_simp [hmne]
    ring

end PGM
