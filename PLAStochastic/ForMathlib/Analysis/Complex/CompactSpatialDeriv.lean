import PLAStochastic.ForMathlib.Analysis.Complex.CompactIntegralAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Genuine spatial derivatives of analytic continuous-function families -/

noncomputable section
open Complex Set
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace K] [CompactSpace K]

/-- Differentiation in the constant spatial direction of a functional lift. -/
def compactSpatialDeriv (H : E × C(K, ℂ) → C(K, ℂ)) (v : E × C(K, ℂ)) : C(K, ℂ) :=
  fderiv ℂ H v (0, 1)

theorem compactSpatialDeriv_analyticAt {H : E × C(K, ℂ) → C(K, ℂ)}
    {v : E × C(K, ℂ)} (hH : AnalyticAt ℂ H v) :
    AnalyticAt ℂ (compactSpatialDeriv H) v := by
  exact ((ContinuousLinearMap.apply ℂ C(K, ℂ) ((0, 1) : E × C(K, ℂ))).analyticAt _).comp hH.fderiv

/-- A functional spatial derivative evaluates to the actual scalar derivative. -/
theorem compactSpatialDeriv_apply {H : E × C(K, ℂ) → C(K, ℂ)}
    {f : E → ℂ → ℂ} {x : E} {X : C(K, ℂ)} (hH : AnalyticAt ℂ H (x, X))
    (he : ∀ X : C(K, ℂ), ∀ k, H (x, X) k = f x (X k))
    (hf : Differentiable ℂ (f x)) (k : K) :
    compactSpatialDeriv H (x, X) k = deriv (f x) (X k) := by
  have hp : HasDerivAt (fun t : ℂ => (x, X + t • (1 : C(K, ℂ))))
      (0, 1) 0 := by
    simpa only [zero_smul, add_zero, one_smul, id_eq] using!
      (hasDerivAt_const (0 : ℂ) x).prodMk
        (((hasDerivAt_id (0 : ℂ)).smul_const (1 : C(K, ℂ))).const_add X)
  have hh := (hH.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp))
  have hd := (ContinuousMap.evalCLM ℂ k).hasFDerivAt.comp_hasDerivAt 0 hh
  have heq : (fun t : ℂ => H (x, X + t • (1 : C(K, ℂ))) k) =
      (fun t : ℂ => f x (X k + t)) := by
    funext t
    rw [he]
    simp
  have hfd := (hf (X k)).hasDerivAt.comp_of_eq 0 ((hasDerivAt_id (0 : ℂ)).const_add (X k)) (by simp)
  have hfd' : HasDerivAt (fun t : ℂ => f x (X k + t)) (deriv (f x) (X k)) 0 := by
    simpa only [add_zero, mul_one, Function.comp_apply] using! hfd
  change (fderiv ℂ H (x, X) (0, 1)) k = _
  exact (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => (congrFun heq t).symm))).unique hfd'

end PGM
