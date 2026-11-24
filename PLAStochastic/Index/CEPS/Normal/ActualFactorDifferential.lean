import PLAStochastic.Index.CEPS.Canonical.JointDifferential
import PLAStochastic.ForMathlib.Analysis.Calculus.ComplexProdDifferential
import PLAStochastic.Index.CEPS.Normal.RootDifferential

/-! # Actual canonical factor differentials for C-8 -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem hasFDerivAt_canonL_qz {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ}
    (hq : ‖q‖ < dom.q₀) (hζ : ζ.re < dom.c₀) :
    HasFDerivAt (fun x : ℂ × ℂ => dom.canonL ρW μ x.1 x.2)
      (cepsNormalFactorQZDifferential
        (deriv (fun q' => dom.canonL ρW μ q' ζ) q)
        (deriv (fun ζ' => dom.canonL ρW μ q ζ') ζ)) (q, ζ) :=
  (dom.differentiableAt_canonL_qz hW hθ hD hμ hq hζ).hasFDerivAt_complex_prod

include hW hθ hD in
theorem hasFDerivAt_canonL_normal {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q ζ : ℂ}
    (hq : ‖q‖ < dom.q₀ / 2) (hζ : ζ.re < dom.c₀) :
    HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => dom.canonL ρW x.1 x.2.1 x.2.2)
      (cepsNormalFactorDifferential
        (deriv (fun μ' : ℝ => dom.canonL ρW μ' q ζ) μ)
        (deriv (fun q' : ℂ => dom.canonL ρW μ q' ζ) q)
        (deriv (fun ζ' : ℂ => dom.canonL ρW μ q ζ') ζ)) (μ, (q, ζ)) := by
  have hd := dom.hasFDerivAt_canonL_real_joint hW hθ hD hf hm hη hμ hq hζ
  have hqz := dom.hasFDerivAt_canonL_qz hW hθ hD
    (show |μ| ≤ dom.μ₀ by linarith [dom.μ₀_pos])
    (show ‖q‖ < dom.q₀ by linarith [dom.q₀_pos]) hζ
  have hmu := dom.hasDerivAt_cepsCanonL_mu_jet hW hθ hD hf hm hη
    (γ := 1) (by norm_num) le_rfl (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos])
    (show |μ| < dom.μ₀ / 2 by linarith [dom.μ₀_pos]) hq.le hζ
  rw [hqz.fderiv] at hd
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro x
  simp [cepsNormalFactorDifferential, cepsNormalFactorQZDifferential,
    CepsCanonDomain.canonL, hmu.deriv, smul_eq_mul, add_assoc]

end PGM.CepsCanonDomain
