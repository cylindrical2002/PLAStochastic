import PLAStochastic.Index.CEPS.Normal.ZeroDiscountRoots
import PLAStochastic.Index.CEPS.Normal.ActualHalfLineIdentity

/-! # Actual half-line bridge and its discount derivative at zero discount -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormalRootSlope_zeroDiscount_of_pos {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    cepsNormalRootSlope (cepsCgf ρW) (fun (t : ℝ) q => cepsRootPlus D θ ρW t q) μ 0 = μ := by
  rw [cepsNormalRootSlope, (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1,
    deriv_cepsCgf_zero hW hθ hD, zero_add]

include hW hθ hD in
theorem cepsNormalData_psiPlus_zeroDiscount_of_pos {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) :
    (cepsNormalData D θ ρW μ 0).ψp = μ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  rw [cepsNormalData_psiPlus_eq hW hθ hD
    (dom.mem_SPRegion hW hθ hD hμ' (by simp; exact dom.q₀_pos.le)),
    (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1,
    deriv_cepsCgf_zero hW hθ hD, zero_add]

include hW hθ hD in
theorem cepsNormal_halfBridge_zeroDiscount {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (l : ℂ) :
    (cepsNormalData D θ ρW μ 0).halfBridge (dom.canonL ρW) μ 0 l =
      (μ : ℂ) * exp (-2 * dom.canonEll ρW μ 0) := by
  rw [CepsNormalData.halfBridge, cepsNormalData_psiPlus_zeroDiscount_of_pos dom hW hθ hD hμ hp]
  change (μ : ℂ) * exp (-cepsRootPlus D θ ρW μ 0 * l -
    2 * dom.canonL ρW μ 0 (cepsRootPlus D θ ρW μ 0)) = _
  rw [(cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1]
  simp [CepsCanonDomain.canonEll]

include hW hθ hD in
theorem cepsNormal_halfBridge_hasDerivAt_zeroDiscount {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (l : ℂ) :
    HasDerivAt
      (fun q : ℂ => (cepsNormalData D θ ρW μ q).halfBridge (dom.canonL ρW) μ q l)
      (exp (-2 * dom.canonEll ρW μ 0) *
        ((cepsStepVar ρW : ℂ) / μ - l - 2 * ((μ : ℂ) * deriv (fun q => dom.canonL ρW μ q 0) 0 +
          deriv (dom.canonL ρW μ 0) 0))) 0 := by
  let B := fun (t : ℝ) q => cepsRootPlus D θ ρW t q
  let P := cepsNormalRootSlope (cepsCgf ρW) B
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hq : ‖(0 : ℂ)‖ ≤ dom.q₀ := by simpa using dom.q₀_pos.le
  have hx := dom.mem_SPRegion hW hθ hD hμ' hq
  have hB0 : B μ 0 = 0 := (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1
  have hP0 : P μ 0 = μ := cepsNormalRootSlope_zeroDiscount_of_pos dom hW hθ hD hμ hp
  have hr := cepsRootR_zeroDiscount_ne_zero dom hW hθ hD hμ hp.ne'
  have hne : (0 : ℂ) - cepsMorseMin D θ ρW μ ≠ 0 := by
    intro hz
    apply hr
    rw [cepsRootR, hz, sqrt_zero]
  obtain ⟨hPne, -, -, hBq, hPq⟩ := cepsRootPlus_actual_path_jets hW hθ hD dom
    (Qcurve := fun _ : ℝ => (0 : ℂ)) hμ hq (by simp) hne (hasDerivAt_const μ 0)
  change HasDerivAt (B μ) (1 / P μ 0) 0 at hBq
  change HasDerivAt (P μ) (deriv (deriv (cepsCgf ρW)) (B μ 0) / P μ 0) 0 at hPq
  rw [hB0, deriv_deriv_cepsCgf_zero hW hθ hD] at hPq
  have hF := dom.hasFDerivAt_canonL_qz hW hθ hD hμ
    (q := 0) (ζ := B μ 0) (by simpa using dom.q₀_pos) (by rw [hB0]; simpa using dom.c₀_pos)
  have hCq := cepsNormal_factor_q_jet (dom.canonL ρW) hF hBq
  have hd := cepsNormal_halfBridge_hasDerivAt hBq hPq hCq hPne (l := l)
  have he : (fun q : ℂ => (cepsNormalData D θ ρW μ q).halfBridge (dom.canonL ρW) μ q l) =ᶠ[𝓝 0]
      (fun q => P μ q * exp (-B μ q * l - 2 * dom.canonL ρW μ q (B μ q))) := by
    have hpath : ContinuousAt (fun q : ℂ => ((μ : ℂ), q)) 0 := by fun_prop
    filter_upwards [hpath.preimage_mem_nhds ((isOpen_cepsSPRegion hW hθ hD).mem_nhds hx)] with q hqx
    rw [CepsNormalData.halfBridge, cepsNormalData_psiPlus_eq hW hθ hD hqx]
    rfl
  have hmne : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  refine (hd.congr_of_eventuallyEq he).congr_deriv ?_
  change P μ 0 * exp (-B μ 0 * l - 2 * dom.canonL ρW μ 0 (B μ 0)) *
    ((cepsStepVar ρW : ℂ) / P μ 0 ^ 2 - l / P μ 0 -
      2 * (deriv (fun q => dom.canonL ρW μ q (B μ 0)) 0 +
        deriv (dom.canonL ρW μ 0) (B μ 0) / P μ 0)) = _
  rw [hB0, hP0]
  simp only [neg_zero, zero_mul, zero_sub, neg_mul, CepsCanonDomain.canonEll]
  field_simp [hmne]

end PGM
