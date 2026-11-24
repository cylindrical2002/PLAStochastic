import PLAStochastic.Index.CEPS.Normal.ZeroHalfBridge
import PLAStochastic.Index.CEPS.Normal.HalfLineRegular
import PLAStochastic.Index.CEPS.Normal.RootCompatibility

/-! # The actual regular half-line occupation pair at zero discount -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_regularHalfEntrance_zeroDiscount {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    (cepsNormalData D θ ρW μ 0).regularHalfEntrance (dom.canonL ρW) μ 0 0 =
      exp (dom.canonEll ρW μ 0) / (μ : ℂ) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hq : ‖(0 : ℂ)‖ ≤ dom.q₀ := by simpa using dom.q₀_pos.le
  have hc := (cepsNormalData_root_compatibility hW hθ hD
    (dom.μ_lt_chart hμ') (dom.norm_cepsRootR_lt hW hθ hD hμ' hq)).1
  have he := CepsNormalData.regularHalfEntrance_at_upperRoot
    (cepsNormalData D θ ρW μ 0) (dom.canonL ρW) μ 0 hc
  change (cepsNormalData D θ ρW μ 0).regularHalfEntrance (dom.canonL ρW) μ 0
    (cepsRootPlus D θ ρW μ 0) =
      exp (dom.canonL ρW μ 0 (cepsRootPlus D θ ρW μ 0)) / (cepsNormalData D θ ρW μ 0).ψp at he
  rw [(cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1,
    cepsNormalData_psiPlus_zeroDiscount_of_pos dom hW hθ hD hμ hp] at he
  exact he

include hW hθ hD in
theorem cepsNormal_regularHalfPair_zeroDiscount {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    cepsNormalRegularHalfPairAt (cepsNormalData D θ ρW) (dom.canonL ρW) μ 0 0 w =
      -(cepsStepVar ρW : ℂ) / (μ : ℂ) ^ 3 + w / (μ : ℂ) ^ 2 +
        2 * deriv (dom.canonL ρW μ 0) 0 / (μ : ℂ) ^ 2 +
        2 * deriv (fun q => dom.canonL ρW μ q 0) 0 / (μ : ℂ) := by
  unfold cepsNormalRegularHalfPairAt
  dsimp only
  rw [cepsNormal_regularHalfEntrance_zeroDiscount dom hW hθ hD hμ hp,
    (cepsNormal_halfBridge_hasDerivAt_zeroDiscount dom hW hθ hD hμ hp _).deriv,
    cepsNormal_halfBridge_zeroDiscount dom hW hθ hD hμ hp]
  simp only [zero_mul, exp_zero, one_mul, div_pow]
  have hex : exp (dom.canonEll ρW μ 0) ^ 2 * exp (-2 * dom.canonEll ρW μ 0) = 1 := by
    rw [← exp_nat_mul _ 2, ← exp_add]
    convert exp_zero using 1
    congr 1
    ring
  have hmne : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  field_simp [hmne]
  simp only [neg_mul] at hex
  linear_combination
    (-(cepsStepVar ρW : ℂ) + w * (μ : ℂ) +
        2 * deriv (dom.canonL ρW μ 0) 0 * (μ : ℂ) +
        2 * deriv (fun q => dom.canonL ρW μ q 0) 0 * (μ : ℂ) ^ 2) * hex

end PGM
