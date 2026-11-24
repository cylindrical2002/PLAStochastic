import PLAStochastic.Index.CEPS.Normal.ActualRootDifferential
import PLAStochastic.Index.CEPS.Normal.ActualFactorDifferential
import PLAStochastic.Index.CEPS.Normal.HalfLineTransport
import PLAStochastic.Index.CEPS.Normal.DiscountInvariant
import PLAStochastic.Index.CEPS.Canonical.TransportSobolev

/-! # Actual half-line transport away from the discount and root merger

All root and canonical-factor differential hypotheses are discharged. The
marked and fixed-discount specializations also discharge the invariant
discount derivative. Removable zero-discount endpoints are separate.
-/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem actual_halfPair_of_transport {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {Qcurve : ℝ → ℂ} {μ : ℝ} {t w : ℂ}
    (hμ : |μ| < dom.μ₀ / 4) (hq : ‖Qcurve μ‖ < dom.q₀ / 4)
    (hre : 0 ≤ (Qcurve μ).re) (ht : t.re < dom.c₀)
    (hne : Qcurve μ - cepsMorseMin D θ ρW μ ≠ 0)
    (hQ : HasDerivAt Qcurve t μ)
    (hd : HasDerivAt (fun x : ℝ => cepsD ρW x (Qcurve x) t) 0 μ)
    (hd0 : cepsD ρW μ (Qcurve μ) t ≠ 0) :
    HasDerivAt
      (fun x : ℝ => cepsNormalHalfPrimitive (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW) x (Qcurve x) t w)
      (cepsNormalHalfPairComponents (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW) μ (Qcurve μ) t w) μ := by
  let B := fun (y : ℝ) q => cepsRootPlus D θ ρW y q
  let P := cepsNormalRootSlope (cepsCgf ρW) B
  let L := dom.canonL ρW
  let e := deriv (fun x : ℝ => L x (Qcurve μ) 0) μ
  let bβ := deriv (fun q' => L μ q' (B μ (Qcurve μ))) (Qcurve μ)
  let cβ := deriv (fun z => L μ (Qcurve μ) z) (B μ (Qcurve μ))
  have hμle : |μ| ≤ dom.μ₀ := by linarith [dom.μ₀_pos]
  have hqle : ‖Qcurve μ‖ ≤ dom.q₀ := by linarith [dom.q₀_pos]
  have hqhalf : ‖Qcurve μ‖ < dom.q₀ / 2 := by linarith [dom.q₀_pos]
  have hβ : (B μ (Qcurve μ)).re < dom.c₀ := by
    have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
    have hb := dom.norm_rootPlus_le hW hθ hD hμ' hqle
    have hr := re_le_norm (B μ (Qcurve μ))
    dsimp only [B] at hr
    linarith [dom.c₀_pos]
  obtain ⟨hp, hBd, hPd, hBqd, hPqd⟩ :=
    cepsRootPlus_actual_path_jets hW hθ hD dom hμle hqle hre hne hQ
  have hLt := dom.hasFDerivAt_canonL_normal hW hθ hD hf hm hη hμ hqhalf ht
  have hLb := dom.hasFDerivAt_canonL_normal hW hθ hD hf hm hη hμ hqhalf hβ
  have hLqz := dom.hasFDerivAt_canonL_qz hW hθ hD hμle
    (show ‖Qcurve μ‖ < dom.q₀ by linarith [dom.q₀_pos]) hβ
  have htransport : ∀ z : ℂ, z.re < dom.c₀ →
      deriv (fun x : ℝ => L x (Qcurve μ) z) μ +
        z * deriv (fun q' => L μ q' z) (Qcurve μ) = e := by
    intro z hz
    exact dom.cepsCanonL_transport_of_sobolev hW hθ hD hf hm hη
      (γ := 1) (by norm_num) le_rfl (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos])
      (show |μ| < dom.μ₀ / 2 by linarith [dom.μ₀_pos]) hq hz
  obtain ⟨hTd, hCd⟩ := cepsNormal_marked_factor_jets L hQ hBd hp hLt hLb
    (htransport t ht) (htransport (B μ (Qcurve μ)) hβ)
  have hCqd := cepsNormal_factor_q_jet L hLqz hBqd
  exact cepsNormal_halfPair_totalDerivative B P (fun (y : ℝ) q z => cepsD ρW y q z) L
    Qcurve μ t w (deriv (deriv (cepsCgf ρW)) (B μ (Qcurve μ)))
    (bβ + cβ / P μ (Qcurve μ)) e hBd hPd hTd hCd hd hBqd hPqd hCqd hp hd0

include hW hθ hD in
/-- Actual marked (P12), with no assumed root or factor jets. -/
theorem actual_halfPair_marked {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} {t w : ℂ} (hμ : |μ| < dom.μ₀ / 4)
    (hq : ‖t * (1 + (μ : ℂ))‖ < dom.q₀ / 4)
    (hre : 0 ≤ (t * (1 + (μ : ℂ))).re) (ht : t.re < dom.c₀)
    (hne : t * (1 + (μ : ℂ)) - cepsMorseMin D θ ρW μ ≠ 0)
    (hd0 : cepsD ρW μ (t * (1 + (μ : ℂ))) t ≠ 0) :
    HasDerivAt
      (fun x : ℝ => cepsNormalHalfPrimitive (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW)
        x (t * (1 + (x : ℂ))) t w)
      (cepsNormalHalfPairComponents (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW)
        μ (t * (1 + (μ : ℂ))) t w) μ := by
  have hQ : HasDerivAt (fun x : ℝ => t * (1 + (x : ℂ))) t μ := by
    simpa using (((hasDerivAt_id μ).ofReal_comp).const_add 1).const_mul t
  exact dom.actual_halfPair_of_transport hW hθ hD hf hm hη hμ hq hre ht hne hQ
    (cepsNormal_discount_marked_hasDerivAt ρW μ t) hd0

include hW hθ hD in
/-- Actual fixed-discount (F10), independent of the marked curve. -/
theorem actual_halfPair_fixed {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} {q w : ℂ} (hμ : |μ| < dom.μ₀ / 4)
    (hq : ‖q‖ < dom.q₀ / 4) (hre : 0 ≤ q.re)
    (hne : q - cepsMorseMin D θ ρW μ ≠ 0) (hd0 : cepsD ρW μ q 0 ≠ 0) :
    HasDerivAt
      (fun x : ℝ => cepsNormalHalfPrimitive (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW) x q 0 w)
      (cepsNormalHalfPairComponents (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW) μ q 0 w) μ :=
  dom.actual_halfPair_of_transport hW hθ hD hf hm hη hμ hq hre dom.c₀_pos hne
    (hasDerivAt_const μ q) (cepsNormal_discount_fixed_hasDerivAt ρW μ q) hd0

end PGM.CepsCanonDomain
