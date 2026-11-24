import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesBudget
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Exact Taylor-series equality of genuine complex germs -/

noncomputable section
open Complex Filter Topology PowerSeries
namespace PGM

theorem complexTaylorSeries_eq_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (he : f =ᶠ[𝓝 z] g) : complexTaylorSeries f z = complexTaylorSeries g z := by
  ext j
  simp only [complexTaylorSeries, coeff_mk, he.iteratedDeriv_eq j]

end PGM
