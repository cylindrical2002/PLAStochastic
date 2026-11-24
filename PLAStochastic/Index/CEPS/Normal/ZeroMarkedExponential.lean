import PLAStochastic.Index.CEPS.Normal.ZeroHalfExponential

/-! # The marked exponential and its first zero jet -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {D θ v : ℝ}

def halfMarkedExponential (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ)
    (μ : ℝ) (w t : ℂ) : ℂ :=
  let q := t * (1 + (μ : ℂ))
  let B := cepsRootPlus D θ ρW μ q
  exp (2 * dom.canonL ρW μ q t - 2 * dom.canonL ρW μ q B -
    (B - t) * (w * (1 + (μ : ℂ))))

variable {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem halfMarkedExponential_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    dom.halfMarkedExponential ρW μ w 0 = 1 := by
  simp only [halfMarkedExponential, zero_mul,
    (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1, sub_self, exp_zero]

include hW hθ hD in
theorem halfMarkedExponential_analyticAt {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    AnalyticAt ℂ (dom.halfMarkedExponential ρW μ w) 0 := by
  let Q := fun t : ℂ => t * (1 + (μ : ℂ))
  let B := cepsRootPlus D θ ρW μ
  have hQ : AnalyticAt ℂ Q 0 := by fun_prop
  have hB : AnalyticAt ℂ B (Q 0) := by
    simpa only [Q, zero_mul] using cepsRootPlus_analyticAt_zeroDiscount dom hW hθ hD hμ hp
  have hB0 : B (Q 0) = 0 := by
    simpa only [Q, zero_mul] using (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1
  have hpath : AnalyticAt ℂ (fun t => B (Q t)) 0 := hB.comp (f := Q) hQ
  have hq : ‖Q 0‖ < dom.q₀ := by simpa [Q] using dom.q₀_pos
  have h0 : (0 : ℂ).re < dom.c₀ := by simpa using dom.c₀_pos
  have ht := dom.analyticAt_canonL_comp_qz hW hθ hD hμ hQ analyticAt_id hq h0
  have hb := dom.analyticAt_canonL_comp_qz hW hθ hD hμ hQ hpath hq (by rw [hB0]; exact h0)
  have h2 : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) 0 := analyticAt_const
  have hl : AnalyticAt ℂ (fun _ : ℂ => w * (1 + (μ : ℂ))) 0 := analyticAt_const
  exact (((h2.mul ht).sub (h2.mul hb)).sub ((hpath.sub analyticAt_id).mul hl)).cexp

include hW hθ hD in
theorem halfMarkedExponential_hasDerivAt {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) (hp : 0 < μ) (w : ℂ) :
    HasDerivAt (dom.halfMarkedExponential ρW μ w)
      (-(2 * deriv (dom.canonL ρW μ 0) 0 + w * (1 + (μ : ℂ))) / (μ : ℂ)) 0 := by
  let c : ℂ := 1 + (μ : ℂ)
  let Q := fun t : ℂ => t * c
  let B := cepsRootPlus D θ ρW μ
  have hQ0 : Q 0 = 0 := by simp [Q]
  have hB0 : B (Q 0) = 0 := by rw [hQ0]; exact (cepsRoots_zeroDiscount_of_pos dom hW hθ hD hμ hp).1
  have hQd : HasDerivAt Q c 0 := by simpa only [Q, id_eq, one_mul] using! (hasDerivAt_id (0 : ℂ)).mul_const c
  have hBq : HasDerivAt B (1 / (μ : ℂ)) (Q 0) := by
    rw [hQ0]
    exact cepsRootPlus_hasDerivAt_zeroDiscount dom hW hθ hD hμ hp
  have hBd := hBq.comp 0 hQd
  have hq : ‖Q 0‖ < dom.q₀ := by rw [hQ0]; simpa using dom.q₀_pos
  have h0 : (0 : ℂ).re < dom.c₀ := by simpa using dom.c₀_pos
  have hT := dom.hasFDerivAt_canonL_qz hW hθ hD hμ (q := Q 0) (ζ := 0) hq h0
  have htD := hT.comp_hasDerivAt (f := fun t : ℂ => (Q t, t)) 0
    (hQd.prodMk (hasDerivAt_id (0 : ℂ)))
  have hC := dom.hasFDerivAt_canonL_qz hW hθ hD hμ (q := Q 0) (ζ := B (Q 0)) hq
    (by rw [hB0]; exact h0)
  have hcD := (cepsNormal_factor_q_jet (dom.canonL ρW) hC hBq).comp 0 hQd
  have hd := (((htD.const_mul 2).sub (hcD.const_mul 2)).sub
    ((hBd.fun_sub (hasDerivAt_id (0 : ℂ))).mul_const (w * c))).cexp
  refine hd.congr_deriv ?_
  change exp (2 * dom.canonL ρW μ (Q 0) 0 - 2 * dom.canonL ρW μ (Q 0) (B (Q 0)) -
      (B (Q 0) - 0) * (w * c)) *
    (2 * (deriv (fun q' => dom.canonL ρW μ q' 0) (Q 0) * c +
        deriv (fun ζ' => dom.canonL ρW μ (Q 0) ζ') 0 * 1) -
      2 * ((deriv (fun q' => dom.canonL ρW μ q' (B (Q 0))) (Q 0) +
        deriv (fun ζ' => dom.canonL ρW μ (Q 0) ζ') (B (Q 0)) / (μ : ℂ)) * c) -
      (1 / (μ : ℂ) * c - 1) * (w * c)) = _
  rw [hB0, hQ0]
  simp only [sub_self, zero_mul, exp_zero, one_mul, mul_one]
  dsimp [c]
  field_simp [ofReal_ne_zero.mpr hp.ne']
  ring

end PGM.CepsCanonDomain
