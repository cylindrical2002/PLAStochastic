import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic

/-! # Actual scalar derivatives in analytic Banach parameter families -/

noncomputable section
open Complex Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A genuine partial derivative in the scalar variable remains analytic jointly with
arbitrary Banach-space parameters. -/
theorem AnalyticAt.deriv_snd {H : E × ℂ → F} {x : E × ℂ} (hH : AnalyticAt ℂ H x) :
    AnalyticAt ℂ (fun v : E × ℂ => deriv (fun z => H (v.1, z)) v.2) x := by
  have hd := ((ContinuousLinearMap.apply ℂ F ((0, 1) : E × ℂ)).analyticAt _).comp hH.fderiv
  apply hd.congr
  filter_upwards [hH.eventually_analyticAt] with v hv
  have hp : HasDerivAt (fun z : ℂ => (v.1, z)) (0, 1) v.2 := by
    exact (hasDerivAt_const v.2 v.1).prodMk (hasDerivAt_id v.2)
  exact (hv.differentiableAt.hasFDerivAt.comp_hasDerivAt v.2 hp).deriv.symm

/-- Every iterated scalar derivative is analytic in the same genuine parameter germ. -/
theorem AnalyticAt.iteratedDeriv_snd {H : E × ℂ → F} {x : E × ℂ}
    (hH : AnalyticAt ℂ H x) (n : ℕ) :
    AnalyticAt ℂ (fun v : E × ℂ => iteratedDeriv n (fun z => H (v.1, z)) v.2) x := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, Prod.mk.eta] using hH
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv_snd

/-- Actual frequency jets can be evaluated on moving parameter and frequency curves. -/
theorem AnalyticAt.iteratedDeriv_snd_comp {H : E × ℂ → F} {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] {a : A} {u : A → E} {z : A → ℂ}
    (hH : AnalyticAt ℂ H (u a, z a)) (hu : AnalyticAt ℂ u a) (hz : AnalyticAt ℂ z a)
    (n : ℕ) :
    AnalyticAt ℂ (fun v => iteratedDeriv n (fun w => H (u v, w)) (z v)) a :=
  (hH.iteratedDeriv_snd n).comp (x := a) (f := fun v => (u v, z v)) (hu.prod hz)
