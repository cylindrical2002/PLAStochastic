import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetAlgebra

/-! # Preservation of finite analytic Taylor jets under division -/

noncomputable section
open Complex PowerSeries
namespace PGM

theorem complexTaylorSeries_coeff_eq_div {f g a c : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (ha : AnalyticAt ℂ a 0) (hc : AnalyticAt ℂ c 0) (hg0 : g 0 ≠ 0) (N : ℕ)
    (hfa : ∀ j ≤ N, coeff j (complexTaylorSeries f 0) = coeff j (complexTaylorSeries a 0))
    (hgc : ∀ j ≤ N, coeff j (complexTaylorSeries g 0) = coeff j (complexTaylorSeries c 0)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => f b / g b) 0) =
      coeff j (complexTaylorSeries (fun b => a b / c b) 0) := by
  have h0 : g 0 = c 0 := by simpa [complexTaylorSeries] using hgc 0 (Nat.zero_le N)
  have hc0 : c 0 ≠ 0 := h0 ▸ hg0
  have hIG : AnalyticAt ℂ (fun b => (g b)⁻¹) 0 := hg.inv hg0
  have hIC : AnalyticAt ℂ (fun b => (c b)⁻¹) 0 := hc.inv hc0
  have heInv := complexTaylorSeries_coeff_eq_composition hg hc
    (F := fun x : ℂ => x⁻¹) (by fun_prop) N hgc
  simpa only [div_eq_mul_inv] using complexTaylorSeries_coeff_eq_mul hf hIG ha hIC N hfa heInv

end PGM
