import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesCongr
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Preservation of finite curve jets under genuine analytic composition -/

noncomputable section
open Complex Set Metric Filter Topology PowerSeries Asymptotics
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isBigO_analytic_curve_difference {F : E → ℂ} {a b : ℂ → E} {x : E}
    (hF : AnalyticAt ℂ F x) (ha : Tendsto a (𝓝 (0 : ℂ)) (𝓝 x))
    (hb : Tendsto b (𝓝 (0 : ℂ)) (𝓝 x)) (N : ℕ)
    (hab : (fun u => a u - b u) =O[𝓝 0] (fun u : ℂ => u ^ (N + 1))) :
    (fun u => F (a u) - F (b u)) =O[𝓝 0] (fun u : ℂ => u ^ (N + 1)) := by
  have hc : ContDiffAt ℂ 1 F x := hF.contDiffAt
  have hstrict := hc.hasStrictFDerivAt (by norm_num)
  exact (hstrict.isBigO_sub.comp_tendsto (ha.prodMk_nhds hb)).trans hab

theorem complexTaylorSeries_coeff_eq_of_analytic_composition {F : E → ℂ} {a b : ℂ → E} {x : E}
    (hF : AnalyticAt ℂ F x) (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0)
    (ha0 : a 0 = x) (hb0 : b 0 = x) (N : ℕ)
    (hab : (fun u => a u - b u) =O[𝓝 0] (fun u : ℂ => u ^ (N + 1))) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun u => F (a u)) 0) =
      coeff j (complexTaylorSeries (fun u => F (b u)) 0) := by
  have hfa := hF.comp_of_eq ha ha0
  have hfb := hF.comp_of_eq hb hb0
  apply complexTaylorSeries_coeff_eq_of_isBigO hfa hfb N
  exact isBigO_analytic_curve_difference hF
    (by simpa only [ha0] using ha.continuousAt.tendsto)
    (by simpa only [hb0] using hb.continuousAt.tendsto) N hab

end PGM
