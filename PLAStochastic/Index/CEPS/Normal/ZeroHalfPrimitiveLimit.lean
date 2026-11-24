import PLAStochastic.Index.CEPS.Normal.ZeroHalfExponential
import PLAStochastic.Index.CEPS.Normal.ZeroHalfTransport
import PLAStochastic.ForMathlib.Analysis.Complex.DoubleZeroQuotient

/-! # The actual half-line primitive after subtracting its common discount pole -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {D θ v : ℝ}

def halfZeroPoleRemoved (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (μ : ℝ) (w q : ℂ) : ℂ :=
  cepsNormalHalfPrimitive (cepsCgf ρW)
    (fun (t : ℝ) q => cepsRootPlus D θ ρW t q)
    (fun (t : ℝ) q z => cepsD ρW t q z) (dom.canonL ρW) μ q 0 w -
      1 / (1 - exp (-q))

variable {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- The finite endpoint is proved as the actual punctured complex-discount limit. -/
theorem tendsto_halfZeroPoleRemoved {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    Tendsto (dom.halfZeroPoleRemoved ρW μ w) (𝓝[≠] 0)
      (𝓝 (dom.halfZeroEndpoint ρW μ w)) := by
  let N := cepsNormalRootNumerator D θ ρW μ
  let E := dom.halfZeroExponential ρW μ w
  let d := fun q : ℂ => 1 - exp (-q)
  let F := fun q => N q * E q - d q
  have hN := cepsNormalRootNumerator_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  obtain ⟨hN0, hN1, hN2⟩ := cepsNormalRootNumerator_zeroDiscount_jets dom hW hθ hD hμ hp
  have hE := dom.halfZeroExponential_analyticAt hW hθ hD hμ hp w
  have hE0 := dom.halfZeroExponential_zero hW hθ hD hμ hp w
  have hEq := dom.halfZeroExponential_hasDerivAt hW hθ hD hμ hp w
  change AnalyticAt ℂ N 0 at hN
  change N 0 = 0 at hN0
  change deriv N 0 = 1 at hN1
  change deriv (deriv N) 0 = (cepsStepVar ρW : ℂ) / (μ : ℂ) ^ 2 at hN2
  change AnalyticAt ℂ E 0 at hE
  change E 0 = 1 at hE0
  change HasDerivAt E
    (-(2 * deriv (dom.canonL ρW μ 0) 0 + w * (1 + (μ : ℂ))) / (μ : ℂ)) 0 at hEq
  have hd : AnalyticAt ℂ d 0 := analyticAt_const.sub (analyticAt_id.neg.cexp)
  have hdAll : ∀ q : ℂ, HasDerivAt d (exp (-q)) q := by
    intro q
    have hh := ((hasDerivAt_id q).neg.cexp).const_sub 1
    simpa only [d, Pi.neg_apply, id_eq, mul_neg, mul_one, neg_neg] using! hh
  have hd0 : d 0 = 0 := by simp [d]
  have hd1 : deriv d 0 = 1 := by rw [(hdAll 0).deriv, neg_zero, exp_zero]
  have hd2 : deriv (deriv d) 0 = -1 := by
    have he : deriv d = fun q : ℂ => exp (-q) := funext fun q => (hdAll q).deriv
    rw [he]
    simpa only [Pi.neg_apply, id_eq, neg_zero, exp_zero, one_mul] using!
      ((hasDerivAt_id (0 : ℂ)).neg.cexp).deriv
  have hF : AnalyticAt ℂ F 0 := (hN.mul hE).sub hd
  have hF0 : F 0 = 0 := by change N 0 * E 0 - d 0 = 0; rw [hN0, zero_mul, hd0, sub_self]
  have hFd := (hN.differentiableAt.hasDerivAt.fun_mul hEq).fun_sub (hdAll 0)
  have hF1 : deriv F 0 = 0 := by
    change HasDerivAt F (deriv N 0 * E 0 + N 0 *
      (-(2 * deriv (dom.canonL ρW μ 0) 0 + w * (1 + (μ : ℂ))) / (μ : ℂ)) - exp (-0)) 0 at hFd
    rw [hFd.deriv]
    rw [hN0, hN1, hE0]
    simp
  have hlim := tendsto_doubleZeroQuotient_of_analyticAt hF hd hF0 hF1 hd0
    (by rw [hd1]; exact one_ne_zero)
  have hF2 : deriv (deriv F) 0 =
      (cepsStepVar ρW : ℂ) / (μ : ℂ) ^ 2 -
        2 * (2 * deriv (dom.canonL ρW μ 0) 0 + w * (1 + (μ : ℂ))) / (μ : ℂ) + 1 := by
    change deriv (deriv (fun q => N q * E q - d q)) 0 = _
    have hNE : AnalyticAt ℂ (fun q => N q * E q) 0 := hN.mul hE
    rw [deriv_deriv_sub_of_analyticAt hNE hd,
      deriv_deriv_mul_of_analyticAt hN hE]
    change deriv (deriv N) 0 * E 0 + 2 * deriv N 0 * deriv E 0 +
      N 0 * deriv (deriv E) 0 - deriv (deriv d) 0 = _
    rw [hN0, hN1, hN2, hE0, hEq.deriv, hd2]
    ring
  have hval : deriv (deriv F) 0 / (2 * deriv d 0 ^ 2) = dom.halfZeroEndpoint ρW μ w := by
    rw [hF2, hd1]
    unfold halfZeroEndpoint
    ring
  rw [hval] at hlim
  have he : ∀ q : ℂ, dom.halfZeroPoleRemoved ρW μ w q = F q / d q ^ 2 := by
    intro q
    have hden : cepsD ρW μ q 0 = d q := by simp [cepsD, stepTransform_zero hW, d]
    unfold halfZeroPoleRemoved cepsNormalHalfPrimitive
    dsimp only
    simp only [sub_zero]
    rw [hden]
    change cepsRootPlus D θ ρW μ q *
      cepsNormalRootSlope (cepsCgf ρW) (fun (t : ℝ) q => cepsRootPlus D θ ρW t q) μ q /
        d q ^ 2 * E q - 1 / d q = (N q * E q - d q) / d q ^ 2
    change N q / d q ^ 2 * E q - 1 / d q = (N q * E q - d q) / d q ^ 2
    by_cases hne : d q = 0
    · simp [hne]
    · field_simp [hne]
  exact hlim.congr fun q => (he q).symm

end PGM.CepsCanonDomain
