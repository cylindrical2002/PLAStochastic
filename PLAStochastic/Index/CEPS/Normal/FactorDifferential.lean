import PLAStochastic.Index.CEPS.Normal.HalfLineDerivative

/-! # Real drift / complex discount / complex space differential of an abstract factor -/

noncomputable section
open Complex
namespace PGM

/-- The real differential with the three indicated partial derivatives. -/
def cepsNormalFactorDifferential (a b c : ℂ) : (ℝ × (ℂ × ℂ)) →L[ℝ] ℂ :=
  (a • Complex.ofRealCLM).comp (ContinuousLinearMap.fst ℝ ℝ (ℂ × ℂ)) +
    (b • (1 : ℂ →L[ℝ] ℂ)).comp
      ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℂ))) +
    (c • (1 : ℂ →L[ℝ] ℂ)).comp
      ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℂ)))

theorem cepsNormalFactorDifferential_apply (a b c : ℂ) (x : ℝ × (ℂ × ℂ)) :
    cepsNormalFactorDifferential a b c x = a * x.1 + b * x.2.1 + c * x.2.2 := by
  simp [cepsNormalFactorDifferential, smul_eq_mul]

/-- Chain rule under a joint real differential; no complex drift regularity is used. -/
theorem cepsNormal_factor_chain (L : ℂ → ℂ → ℂ → ℂ) {Q B : ℝ → ℂ}
    {μ : ℝ} {a b c q' β' : ℂ}
    (hL : HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => L x.1 x.2.1 x.2.2)
      (cepsNormalFactorDifferential a b c) (μ, (Q μ, B μ)))
    (hQ : HasDerivAt Q q' μ) (hB : HasDerivAt B β' μ) :
    HasDerivAt (fun x : ℝ => L x (Q x) (B x)) (a + b * q' + c * β') μ := by
  have hpath := (hasDerivAt_id μ).prodMk (hQ.prodMk hB)
  refine (hL.comp_hasDerivAt μ hpath).congr_deriv ?_
  rw [cepsNormalFactorDifferential_apply]
  simp

/-- The transport identity produces the path jets consumed by (P12). -/
theorem cepsNormal_marked_factor_jets (L : ℂ → ℂ → ℂ → ℂ) {Q B : ℝ → ℂ}
    {μ : ℝ} {t p e aₜ bₜ cₜ aᵦ bᵦ cᵦ : ℂ}
    (hQ : HasDerivAt Q t μ)
    (hB : HasDerivAt B (-(B μ - t) / p) μ) (hp : p ≠ 0)
    (hLt : HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => L x.1 x.2.1 x.2.2)
      (cepsNormalFactorDifferential aₜ bₜ cₜ) (μ, (Q μ, t)))
    (hLb : HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => L x.1 x.2.1 x.2.2)
      (cepsNormalFactorDifferential aᵦ bᵦ cᵦ) (μ, (Q μ, B μ)))
    (htransportₜ : aₜ + t * bₜ = e) (htransportᵦ : aᵦ + B μ * bᵦ = e) :
    HasDerivAt (fun x : ℝ => L x (Q x) t) e μ ∧
      HasDerivAt (fun x : ℝ => L x (Q x) (B x))
        (e - (B μ - t) * (bᵦ + cᵦ / p)) μ := by
  have ht := cepsNormal_factor_chain L hLt hQ (hasDerivAt_const μ t)
  have hb := cepsNormal_factor_chain L hLb hQ hB
  constructor
  · refine ht.congr_deriv ?_
    simp only [mul_zero, add_zero]
    linear_combination htransportₜ
  · refine hb.congr_deriv ?_
    field_simp
    linear_combination p * htransportᵦ

/-- Constant discount is the unmarked `t = 0` specialization of the same transport rule. -/
theorem cepsNormal_fixed_factor_jets (L : ℂ → ℂ → ℂ → ℂ) {B : ℝ → ℂ}
    {μ : ℝ} {q p e a₀ b₀ c₀ aᵦ bᵦ cᵦ : ℂ}
    (hB : HasDerivAt B (-B μ / p) μ) (hp : p ≠ 0)
    (hL0 : HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => L x.1 x.2.1 x.2.2)
      (cepsNormalFactorDifferential a₀ b₀ c₀) (μ, (q, 0)))
    (hLb : HasFDerivAt (fun x : ℝ × (ℂ × ℂ) => L x.1 x.2.1 x.2.2)
      (cepsNormalFactorDifferential aᵦ bᵦ cᵦ) (μ, (q, B μ)))
    (htransport₀ : a₀ = e) (htransportᵦ : aᵦ + B μ * bᵦ = e) :
    HasDerivAt (fun x : ℝ => L x q 0) e μ ∧
      HasDerivAt (fun x : ℝ => L x q (B x)) (e - B μ * (bᵦ + cᵦ / p)) μ := by
  have h := cepsNormal_marked_factor_jets L (Q := fun _ => q) (t := 0)
    (hasDerivAt_const μ q) (by simpa using hB) hp hL0 hLb
    (by simpa using htransport₀) htransportᵦ
  simpa using h

end PGM
