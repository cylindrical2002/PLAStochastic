import PLAStochastic.Index.CEPS.Normal.ZeroMarkedExponential
import PLAStochastic.Index.CEPS.Normal.ZeroMarkedNumerator
import PLAStochastic.Index.CEPS.Normal.ZeroMarkedDiscount
import PLAStochastic.Index.CEPS.Normal.ZeroHalfPrimitiveLimit

/-! # The actual marked half-line primitive after removing the common pole -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {D θ v : ℝ}

def halfMarkedPoleRemoved (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (μ : ℝ) (w t : ℂ) : ℂ :=
  cepsNormalHalfPrimitive (cepsCgf ρW)
    (fun (x : ℝ) q => cepsRootPlus D θ ρW x q)
    (fun (x : ℝ) q z => cepsD ρW x q z) (dom.canonL ρW)
    μ (t * (1 + (μ : ℂ))) t w - 1 / cepsMarkedDiscount ρW t

variable {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem tendsto_halfMarkedPoleRemoved {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    Tendsto (dom.halfMarkedPoleRemoved ρW μ w) (𝓝[≠] 0)
      (𝓝 (dom.halfZeroEndpoint ρW μ w)) := by
  let N := cepsNormalMarkedRootNumerator D θ ρW μ
  let E := dom.halfMarkedExponential ρW μ w
  let d := cepsMarkedDiscount ρW
  let F := fun t => N t * E t - d t
  have hN : AnalyticAt ℂ N 0 := cepsNormalMarkedRootNumerator_analyticAt dom hW hθ hD hμ hp
  obtain ⟨hN0, hN1, hN2⟩ := cepsNormalMarkedRootNumerator_zero_jets dom hW hθ hD hμ hp
  change N 0 = 0 at hN0
  change deriv N 0 = 1 at hN1
  change deriv (deriv N) 0 = (cepsStepVar ρW : ℂ) * (1 - (μ : ℂ) ^ 2) / (μ : ℂ) ^ 2 at hN2
  have hE : AnalyticAt ℂ E 0 := dom.halfMarkedExponential_analyticAt hW hθ hD hμ hp w
  have hE0 : E 0 = 1 := dom.halfMarkedExponential_zero hW hθ hD hμ hp w
  have hEq : HasDerivAt E
      (-(2 * deriv (dom.canonL ρW μ 0) 0 + w * (1 + (μ : ℂ))) / (μ : ℂ)) 0 :=
    dom.halfMarkedExponential_hasDerivAt hW hθ hD hμ hp w
  have hd : AnalyticAt ℂ d 0 := cepsMarkedDiscount_analyticAt_zero hW hθ hD
  obtain ⟨hd0, hd1, hd2⟩ := cepsMarkedDiscount_zero_jets hW hθ hD
  change d 0 = 0 at hd0
  change deriv d 0 = 1 at hd1
  change deriv (deriv d) 0 = -(cepsStepVar ρW : ℂ) - 1 at hd2
  have hF : AnalyticAt ℂ F 0 := (hN.mul hE).sub hd
  have hF0 : F 0 = 0 := by change N 0 * E 0 - d 0 = 0; rw [hN0, zero_mul, hd0, sub_self]
  have hFd := (hN.differentiableAt.hasDerivAt.fun_mul hEq).fun_sub hd.differentiableAt.hasDerivAt
  change HasDerivAt F (deriv N 0 * E 0 + N 0 *
    (-(2 * deriv (dom.canonL ρW μ 0) 0 + w * (1 + (μ : ℂ))) / (μ : ℂ)) - deriv d 0) 0 at hFd
  have hF1 : deriv F 0 = 0 := by
    rw [hFd.deriv, hN0, hN1, hE0, hd1]
    ring
  have hlim := tendsto_doubleZeroQuotient_of_analyticAt hF hd hF0 hF1 hd0
    (by rw [hd1]; exact one_ne_zero)
  have hF2 : deriv (deriv F) 0 =
      (cepsStepVar ρW : ℂ) / (μ : ℂ) ^ 2 -
        2 * (2 * deriv (dom.canonL ρW μ 0) 0 + w * (1 + (μ : ℂ))) / (μ : ℂ) + 1 := by
    change deriv (deriv (fun t => N t * E t - d t)) 0 = _
    have hNE : AnalyticAt ℂ (fun t => N t * E t) 0 := hN.mul hE
    rw [deriv_deriv_sub_of_analyticAt hNE hd, deriv_deriv_mul_of_analyticAt hN hE]
    change deriv (deriv N) 0 * E 0 + 2 * deriv N 0 * deriv E 0 +
      N 0 * deriv (deriv E) 0 - deriv (deriv d) 0 = _
    rw [hN0, hN1, hN2, hE0, hEq.deriv, hd2]
    field_simp [ofReal_ne_zero.mpr hp.ne']
    ring
  have hval : deriv (deriv F) 0 / (2 * deriv d 0 ^ 2) = dom.halfZeroEndpoint ρW μ w := by
    rw [hF2, hd1]
    unfold halfZeroEndpoint
    ring
  rw [hval] at hlim
  have he : ∀ t : ℂ, dom.halfMarkedPoleRemoved ρW μ w t = F t / d t ^ 2 := by
    intro t
    let q := t * (1 + (μ : ℂ))
    let P := cepsNormalRootSlope (cepsCgf ρW) (fun (x : ℝ) q => cepsRootPlus D θ ρW x q) μ
    have hnum : (cepsRootPlus D θ ρW μ q - t) * P q = N t := by
      dsimp [N, cepsNormalMarkedRootNumerator, cepsNormalRootNumerator, q, P]
      ring
    unfold halfMarkedPoleRemoved cepsNormalHalfPrimitive
    dsimp only
    rw [cepsD_marked_eq]
    change (cepsRootPlus D θ ρW μ q - t) * P q / d t ^ 2 * E t - 1 / d t = F t / d t ^ 2
    rw [hnum]
    change N t / d t ^ 2 * E t - 1 / d t = (N t * E t - d t) / d t ^ 2
    by_cases hne : d t = 0
    · simp [hne]
    · field_simp [hne]
  exact hlim.congr fun t => (he t).symm

end PGM.CepsCanonDomain
