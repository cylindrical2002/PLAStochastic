import PLAStochastic.ForMathlib.Analysis.Complex.CompactSpatialDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Actual spatial derivatives of local compact-function germs -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace K] [CompactSpace K]

/-- Local pointwise agreement suffices; scalar differentiability is obtained from
the actual functional derivative, without an entire-function assumption. -/
theorem hasDerivAt_compact_lift_local {H : E × C(K, ℂ) → C(K, ℂ)}
    {f : E → ℂ → ℂ} {x : E} {X : C(K, ℂ)}
    (hH : DifferentiableAt ℂ H (x, X))
    (he : ∀ᶠ u in 𝓝 (x, X), ∀ k, H u k = f u.1 (u.2 k)) (k : K) :
    HasDerivAt (f x) (compactSpatialDeriv H (x, X) k) (X k) := by
  let c : ℂ → E × C(K, ℂ) := fun t => (x, X + (t - X k) • (1 : C(K, ℂ)))
  have hp : HasDerivAt c (0, 1) (X k) := by
    simpa [c, sub_self, zero_smul, add_zero, one_smul, id_eq] using!
      (hasDerivAt_const (X k) x).prodMk
        ((((hasDerivAt_id (X k)).sub_const (X k)).smul_const
          (1 : C(K, ℂ))).const_add X)
  have hc₀ : c (X k) = (x, X) := by simp [c]
  have ht : Tendsto c (𝓝 (X k)) (𝓝 (x, X)) := by
    simpa only [hc₀] using hp.continuousAt.tendsto
  have hd := (ContinuousMap.evalCLM ℂ k).hasFDerivAt.comp_hasDerivAt (X k)
    (hH.hasFDerivAt.comp_hasDerivAt_of_eq (X k) hp hc₀.symm)
  apply hd.congr_of_eventuallyEq
  filter_upwards [ht.eventually he] with t ht
  change f x t = H (c t) k
  rw [ht k]
  simp [c]

theorem compactSpatialDeriv_apply_local {H : E × C(K, ℂ) → C(K, ℂ)}
    {f : E → ℂ → ℂ} {x : E} {X : C(K, ℂ)}
    (hH : DifferentiableAt ℂ H (x, X))
    (he : ∀ᶠ u in 𝓝 (x, X), ∀ k, H u k = f u.1 (u.2 k)) (k : K) :
    compactSpatialDeriv H (x, X) k = deriv (f x) (X k) :=
  (hasDerivAt_compact_lift_local hH he k).deriv.symm

def compactSpatialIteratedDeriv (n : ℕ) (H : E × C(K, ℂ) → C(K, ℂ)) :
    E × C(K, ℂ) → C(K, ℂ) :=
  n.rec H (fun _ D => compactSpatialDeriv D)

theorem compactSpatialIteratedDeriv_analyticAt {H : E × C(K, ℂ) → C(K, ℂ)}
    {v : E × C(K, ℂ)} (hH : AnalyticAt ℂ H v) (n : ℕ) :
    AnalyticAt ℂ (compactSpatialIteratedDeriv n H) v := by
  induction n with
  | zero => exact hH
  | succ n ih => exact compactSpatialDeriv_analyticAt ih

/-- All actual scalar derivatives agree on a common functional neighborhood for
each requested order, even when the scalar germ has no global continuation. -/
theorem compactSpatialIteratedDeriv_eventually_apply
    {H : E × C(K, ℂ) → C(K, ℂ)} {f : E → ℂ → ℂ} {v : E × C(K, ℂ)}
    (hH : AnalyticAt ℂ H v)
    (he : ∀ᶠ u in 𝓝 v, ∀ k, H u k = f u.1 (u.2 k)) (n : ℕ) :
    ∀ᶠ u in 𝓝 v, ∀ k,
      compactSpatialIteratedDeriv n H u k = iteratedDeriv n (f u.1) (u.2 k) := by
  induction n with
  | zero => simpa only [compactSpatialIteratedDeriv, Nat.rec_zero, iteratedDeriv_zero] using he
  | succ n ih =>
    filter_upwards [(compactSpatialIteratedDeriv_analyticAt hH n).eventually_analyticAt,
      eventually_eventually_nhds.mpr ih] with u hu he
    intro k
    change compactSpatialDeriv (compactSpatialIteratedDeriv n H) u k = _
    have he' : ∀ᶠ w in 𝓝 (u.1, u.2), ∀ k,
        compactSpatialIteratedDeriv n H w k = iteratedDeriv n (f w.1) (w.2 k) := by
      simpa only [Prod.mk.eta] using he
    simpa only [iteratedDeriv_succ] using!
      compactSpatialDeriv_apply_local (f := fun p => iteratedDeriv n (f p))
        hu.differentiableAt he' k

end PGM
