import PLAStochastic.Index.CEPS.Scaled.InverseFrequencyBudget
import PLAStochastic.Index.CEPS.Scaled.RootValueFrequencyBudget
import PLAStochastic.Index.CEPS.Scaled.ProductDerivativeBudget

/-! # A common class constant for the root and inverse frequency profiles -/

noncomputable section
open Complex Set Metric MeasureTheory
namespace PGM

def CepsCanonDomain.kernelFrequencyConstants {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : Finset ℝ :=
  {v * Real.exp (2 * dom.normalLogBound),
    v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)),
    dom.canonWeightErrorBound N M, dom.rootEvaluationFrequencyErrorConstant N M,
    (v * Real.exp (2 * dom.normalLogBound)) * dom.rootFrequencyChainConstant,
    (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) * dom.rootFrequencyChainConstant,
    2 * dom.surrogateSlopePolynomialConstant 0 M,
    dom.trueDenominatorRelativeConstant N M * (2 * dom.surrogateSlopePolynomialConstant 0 M),
    dom.trueInverseFrequencyConstant M, dom.inverseFrequencyErrorConstant N M}

def CepsCanonDomain.kernelFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  1 + ∑ c ∈ dom.kernelFrequencyConstants N M, |c|

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

theorem kernelFrequencyConstant_pos (N : ℕ) (M : ℝ) : 0 < dom.kernelFrequencyConstant N M := by
  have h := Finset.sum_nonneg (fun c (_ : c ∈ dom.kernelFrequencyConstants N M) => abs_nonneg c)
  unfold CepsCanonDomain.kernelFrequencyConstant
  linarith

theorem kernelFrequencyConstant_le (N : ℕ) (M : ℝ) {c : ℝ}
    (hc : c ∈ dom.kernelFrequencyConstants N M) : c ≤ dom.kernelFrequencyConstant N M := by
  have h := Finset.single_le_sum (fun c (_ : c ∈ dom.kernelFrequencyConstants N M) => abs_nonneg c) hc
  apply (le_abs_self c).trans (h.trans _)
  unfold CepsCanonDomain.kernelFrequencyConstant
  linarith

theorem cepsDrift_square_weight_of_linear_weight {d L C K E e X : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hC : C ≤ K) (hLX : L ≤ X) (h1LX : 1 + L ≤ X)
    (h : d * L ≤ C * (1 + L) * E * e) : d * L ^ 2 ≤ K * X ^ 2 * E * e := by
  have hX : 0 ≤ X := hL.trans hLX
  have h' : d * L ≤ K * (1 + L) * E * e := h.trans (by gcongr)
  calc
    _ = (d * L) * L := by ring
    _ ≤ (K * (1 + L) * E * e) * L := mul_le_mul_of_nonneg_right h' hL
    _ ≤ (K * X * E * e) * X := by gcongr
    _ = _ := by ring

end PGM
