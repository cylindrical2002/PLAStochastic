import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Second-derivative algebra for scalar analytic functions -/

noncomputable section
open Filter Topology
namespace PGM

theorem deriv_deriv_mul_of_analyticAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    deriv (deriv (fun x => f x * g x)) z =
      deriv (deriv f) z * g z + 2 * deriv f z * deriv g z + f z * deriv (deriv g) z := by
  have hh := iteratedDeriv_fun_mul (n := 2) hf.contDiffAt hg.contDiffAt
  simpa [Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero, mul_comm,
    add_comm, add_left_comm] using hh

theorem deriv_deriv_sub_of_analyticAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    deriv (deriv (fun x => f x - g x)) z = deriv (deriv f) z - deriv (deriv g) z := by
  have hh := iteratedDeriv_fun_sub (n := 2) hf.contDiffAt hg.contDiffAt
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hh

theorem deriv_deriv_comp_const_mul_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (c : ℂ) :
    deriv (deriv (fun x => f (c * x))) 0 = deriv (deriv f) 0 * c ^ 2 := by
  have hlin : HasDerivAt (fun x : ℂ => c * x) c 0 := hasDerivAt_const_mul c
  have heN : ∀ᶠ x in 𝓝 (0 : ℂ), AnalyticAt ℂ f (c * x) := by
    have hh : Tendsto (fun x : ℂ => c * x) (𝓝 0) (𝓝 0) := by simpa using hlin.continuousAt.tendsto
    exact hh.eventually hf.eventually_analyticAt
  have he : deriv (fun x => f (c * x)) =ᶠ[𝓝 (0 : ℂ)]
      (fun x => deriv f (c * x) * c) := by
    filter_upwards [heN] with x hx
    exact (hx.differentiableAt.hasDerivAt.comp x (hasDerivAt_const_mul c)).deriv
  have hdf : HasDerivAt (deriv f) (deriv (deriv f) 0) (c * 0) := by
    simpa only [mul_zero] using hf.deriv.differentiableAt.hasDerivAt
  have hd := (hdf.comp 0 hlin).mul_const c
  change HasDerivAt (fun x => deriv f (c * x) * c) (deriv (deriv f) 0 * c * c) 0 at hd
  rw [he.deriv_eq, hd.deriv]
  ring

end PGM
