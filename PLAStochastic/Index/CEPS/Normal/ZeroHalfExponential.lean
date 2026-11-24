import PLAStochastic.Index.CEPS.Normal.ZeroRootNumerator
import PLAStochastic.Index.CEPS.Canonical.AnalyticSlices

/-! # The exponential part of the actual zero-discount half-line primitive -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {D θ v : ℝ}

def halfZeroExponential (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (μ : ℝ) (w q : ℂ) : ℂ :=
  let B := cepsRootPlus D θ ρW μ q
  exp (2 * dom.canonL ρW μ q 0 - 2 * dom.canonL ρW μ q B - B * (w * (1 + (μ : ℂ))))

variable {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem halfZeroExponential_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    dom.halfZeroExponential ρW μ w 0 = 1 := by
  simp only [halfZeroExponential, (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1,
    zero_mul, sub_self, exp_zero]

include hW hθ hD in
theorem halfZeroExponential_analyticAt {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    AnalyticAt ℂ (dom.halfZeroExponential ρW μ w) 0 := by
  have hB := cepsRootPlus_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  have hq : ‖(0 : ℂ)‖ < dom.q₀ := by simpa using dom.q₀_pos
  have h0 : (0 : ℂ).re < dom.c₀ := by simpa using dom.c₀_pos
  have ht := dom.analyticAt_canonL_comp_spatial hW hθ hD hμ
    (Z := fun _ : ℂ => (0 : ℂ)) analyticAt_const hq h0
  have hb := dom.analyticAt_canonL_comp_spatial hW hθ hD hμ hB hq
    (by rw [(cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1]; exact h0)
  have h2 : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) 0 := analyticAt_const
  have hl : AnalyticAt ℂ (fun _ : ℂ => w * (1 + (μ : ℂ))) 0 := analyticAt_const
  exact (((h2.mul ht).sub (h2.mul hb)).sub (hB.mul hl)).cexp

include hW hθ hD in
theorem halfZeroExponential_hasDerivAt {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    HasDerivAt (dom.halfZeroExponential ρW μ w)
      (-(2 * deriv (dom.canonL ρW μ 0) 0 + w * (1 + (μ : ℂ))) / (μ : ℂ)) 0 := by
  let B := cepsRootPlus D θ ρW μ
  have hB0 : B 0 = 0 := (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1
  have hBq := cepsRootPlus_hasDerivAt_zeroDiscount dom hW hθ hD hμ hp
  have h0 : (0 : ℂ).re < dom.c₀ := by simpa using dom.c₀_pos
  have hq : ‖(0 : ℂ)‖ < dom.q₀ := by simpa using dom.q₀_pos
  have hqz := dom.hasFDerivAt_canonL_qz hW hθ hD hμ (q := 0) (ζ := B 0) hq
    (by rw [hB0]; exact h0)
  have hCq := cepsNormal_factor_q_jet (dom.canonL ρW) hqz hBq
  change HasDerivAt (fun q => dom.canonL ρW μ q (B q))
    (deriv (fun q => dom.canonL ρW μ q (B 0)) 0 + deriv (dom.canonL ρW μ 0) (B 0) / (μ : ℂ)) 0 at hCq
  rw [hB0] at hCq
  have ht := (dom.analyticAt_canonL_comp_spatial hW hθ hD hμ
    (Z := fun _ : ℂ => (0 : ℂ)) analyticAt_const hq h0).differentiableAt.hasDerivAt
  have hd := (((ht.const_mul 2).sub (hCq.const_mul 2)).sub
    (hBq.mul_const (w * (1 + (μ : ℂ))))).cexp
  have hmne : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  refine hd.congr_deriv ?_
  change exp (2 * dom.canonL ρW μ 0 0 - 2 * dom.canonL ρW μ 0 (B 0) -
      B 0 * (w * (1 + (μ : ℂ)))) *
    (2 * deriv (fun q => dom.canonL ρW μ q 0) 0 -
      2 * (deriv (fun q => dom.canonL ρW μ q 0) 0 + deriv (dom.canonL ρW μ 0) 0 / (μ : ℂ)) -
      1 / (μ : ℂ) * (w * (1 + (μ : ℂ)))) = _
  rw [hB0]
  simp only [sub_self, zero_mul, exp_zero, one_mul]
  field_simp [hmne]; ring

end PGM.CepsCanonDomain
