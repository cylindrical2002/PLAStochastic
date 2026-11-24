import PLAStochastic.Index.CEPS.Normal.FactorDifferential

/-! # The root and `ψ'` jets used by the half-line total derivative -/

noncomputable section
open Complex Filter Topology
namespace PGM

def cepsNormalRootSlope (ψ : ℂ → ℂ) (B : ℝ → ℂ → ℂ) (μ : ℝ) (q : ℂ) : ℂ :=
  deriv ψ (B μ q) + (μ : ℂ)

/-- All four root jets follow from the two root equations and actual
differentiability. `Qcurve' = t` covers both marked and fixed discount.
-/
theorem cepsNormal_root_jets (ψ : ℂ → ℂ) (B : ℝ → ℂ → ℂ) (Qcurve : ℝ → ℂ)
    {μ : ℝ} {t b' bq p₂ : ℂ}
    (hB : HasDerivAt (fun x : ℝ => B x (Qcurve x)) b' μ)
    (hBq : HasDerivAt (B μ) bq (Qcurve μ))
    (hψ : HasDerivAt ψ (deriv ψ (B μ (Qcurve μ))) (B μ (Qcurve μ)))
    (hψ' : HasDerivAt (deriv ψ) p₂ (B μ (Qcurve μ)))
    (hQ : HasDerivAt Qcurve t μ)
    (hroot : ∀ᶠ (x : ℝ) in 𝓝 μ, ψ (B x (Qcurve x)) + (x : ℂ) * B x (Qcurve x) = Qcurve x)
    (hrootq : ∀ᶠ (q' : ℂ) in 𝓝 (Qcurve μ), ψ (B μ q') + (μ : ℂ) * B μ q' = q')
    (hp : cepsNormalRootSlope ψ B μ (Qcurve μ) ≠ 0) :
    HasDerivAt (fun x : ℝ => B x (Qcurve x))
        (-(B μ (Qcurve μ) - t) / cepsNormalRootSlope ψ B μ (Qcurve μ)) μ ∧
      HasDerivAt (fun x : ℝ => cepsNormalRootSlope ψ B x (Qcurve x))
        (1 - (B μ (Qcurve μ) - t) * p₂ / cepsNormalRootSlope ψ B μ (Qcurve μ)) μ ∧
      HasDerivAt (B μ) (1 / cepsNormalRootSlope ψ B μ (Qcurve μ)) (Qcurve μ) ∧
      HasDerivAt (cepsNormalRootSlope ψ B μ)
        (p₂ / cepsNormalRootSlope ψ B μ (Qcurve μ)) (Qcurve μ) := by
  let p := cepsNormalRootSlope ψ B μ (Qcurve μ)
  have hm : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 μ := (hasDerivAt_id μ).ofReal_comp
  have hrootd := ((hψ.comp μ hB).add (hm.mul hB)).congr_of_eventuallyEq
    (EventuallyEq.symm hroot)
  have he := hrootd.unique hQ
  have hb' : b' = -(B μ (Qcurve μ) - t) / p := by
    apply (eq_div_iff hp).2
    dsimp [p, cepsNormalRootSlope]
    linear_combination he
  have hBd := hB.congr_deriv hb'
  have hrootqd := ((hψ.comp (Qcurve μ) hBq).add (hBq.const_mul (μ : ℂ))).congr_of_eventuallyEq
    (EventuallyEq.symm hrootq)
  have heq := hrootqd.unique (hasDerivAt_id (Qcurve μ))
  have hbq : bq = 1 / p := by
    apply (eq_div_iff hp).2
    dsimp [p, cepsNormalRootSlope]
    linear_combination heq
  have hBqd := hBq.congr_deriv hbq
  refine ⟨hBd, ?_, hBqd, ?_⟩
  · refine ((hψ'.comp μ hBd).add hm).congr_deriv ?_
    dsimp [p]
    field_simp [hp]
    ring
  · refine ((hψ'.comp (Qcurve μ) hBqd).add_const (μ : ℂ)).congr_deriv ?_
    dsimp [p]
    ring

/-- The complex discount/space differential of the factor. -/
def cepsNormalFactorQZDifferential (b c : ℂ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  b • ContinuousLinearMap.fst ℂ ℂ ℂ + c • ContinuousLinearMap.snd ℂ ℂ ℂ

/-- Joint holomorphy in discount/space gives the `q` jet along the root. -/
theorem cepsNormal_factor_q_jet (L : ℂ → ℂ → ℂ → ℂ) {B : ℂ → ℂ}
    {μ q b c p : ℂ}
    (hL : HasFDerivAt (fun x : ℂ × ℂ => L μ x.1 x.2)
      (cepsNormalFactorQZDifferential b c) (q, B q))
    (hB : HasDerivAt B (1 / p) q) :
    HasDerivAt (fun q' => L μ q' (B q')) (b + c / p) q := by
  refine (hL.comp_hasDerivAt q ((hasDerivAt_id q).prodMk hB)).congr_deriv ?_
  simp [cepsNormalFactorQZDifferential, smul_eq_mul, div_eq_mul_inv]

end PGM
