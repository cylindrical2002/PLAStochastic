import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetAlgebra

/-! # Exact finite analytic Taylor-jet subtraction -/

noncomputable section
open Complex Filter Topology PowerSeries Asymptotics
namespace PGM

theorem complexTaylorSeries_coeff_eq_sub {f g a c : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (ha : AnalyticAt ℂ a 0) (hc : AnalyticAt ℂ c 0) (N : ℕ)
    (hfa : ∀ j ≤ N, coeff j (complexTaylorSeries f 0) = coeff j (complexTaylorSeries a 0))
    (hgc : ∀ j ≤ N, coeff j (complexTaylorSeries g 0) = coeff j (complexTaylorSeries c 0)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => f b - g b) 0) =
      coeff j (complexTaylorSeries (fun b => a b - c b) 0) := by
  have heF := isBigO_difference_of_complexTaylorSeries_coeff_eq hf ha N hfa
  have heG := isBigO_difference_of_complexTaylorSeries_coeff_eq hg hc N hgc
  have herr : (fun b => (f b - g b) - (a b - c b)) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    apply (heF.sub heG).congr' (Eventually.of_forall fun b => ?_) Filter.EventuallyEq.rfl
    ring
  exact complexTaylorSeries_coeff_eq_of_isBigO (hf.sub hg) (ha.sub hc) N herr

end PGM
