import PLAStochastic.Index.CEPS.Normal.NegativeDenominator
import PLAStochastic.Index.CEPS.Normal.RegularEven

/-! # Nonvanishing for either signed lift of an extended discount point -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseNormalData_dslope_ne_zero_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q r : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hr : r ^ 2 = q - cepsMorseMin D θ ρW μ)
    {l : ℝ} (hl : dom.normalNegativeWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    dslope ((cepsMorseNormalData D θ ρW μ r).normalG (dom.canonL ρW) μ
      (cepsMorseDiscount D θ ρW μ r) l)
        (cepsMorseNormalData D θ ρW μ r).βm (cepsMorseNormalData D θ ρW μ r).βp ≠ 0 := by
  have hqr : cepsMorseDiscount D θ ρW μ r = q := by
    unfold cepsMorseDiscount
    rw [hr]
    ring
  rw [hqr]
  have hS := cepsNormal_actual_dslope_ne_zero_negative dom hW hθ hD hμ hq hl hre
  have hs : r ^ 2 = (Complex.sqrt (q - cepsMorseMin D θ ρW μ)) ^ 2 := by
    rw [sqrt_sq_eq, hr]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
  · rw [he, cepsMorseNormalData_sqrt_eq]
    exact hS
  · rw [he, cepsMorseNormalData_neg, cepsMorseNormalData_sqrt_eq]
    change dslope ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)
      (cepsRootPlus D θ ρW μ q) (cepsRootMinus D θ ρW μ q) ≠ 0
    rw [cepsNormal_dslope_swap]
    exact hS

end PGM
