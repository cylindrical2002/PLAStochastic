import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-! # Cancellation of a scalar power on genuine parameter neighborhoods -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- A scalar power factor can be cancelled throughout an actual neighborhood,
including its zero section, by continuity in the scalar coordinate. -/
theorem eventually_zero_of_scalar_pow_mul {R : E × ℂ → ℂ} {v : E × ℂ} (n : ℕ)
    (hC : ∀ᶠ u in 𝓝 v, ContinuousAt R u)
    (hP : ∀ᶠ u in 𝓝 v, u.2 ^ n * R u = 0) : ∀ᶠ u in 𝓝 v, R u = 0 := by
  filter_upwards [hC, hP.eventually_nhds] with u hu hp
  by_cases hz : u.2 = 0
  · let c : ℂ → E × ℂ := fun t => (u.1, t)
    have hc : ContinuousAt c 0 := continuousAt_const.prodMk continuousAt_id
    have hc₀ : c 0 = u := by simp [c, ← hz]
    have ht : Tendsto c (𝓝 (0 : ℂ)) (𝓝 u) := by simpa only [hc₀] using hc.tendsto
    by_contra hR
    have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), R (c t) ≠ 0 := ht.eventually (hu.eventually_ne hR)
    have hzero : ∀ᶠ t in 𝓝 (0 : ℂ), t ^ n * R (c t) = 0 := ht.eventually hp
    have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ≠ 0 := by
      filter_upwards [(self_mem_nhdsWithin : {0}ᶜ ∈ 𝓝[≠] (0 : ℂ))] with t ht
      exact ht
    have hfalse : ∀ᶠ t in 𝓝[≠] (0 : ℂ), False := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
        hzero.filter_mono nhdsWithin_le_nhds, hne] with t ht hz hn
      exact mul_ne_zero (pow_ne_zero n hn) ht hz
    obtain ⟨t, ht⟩ := hfalse.exists
    exact ht
  · exact (mul_eq_zero.mp hp.self_of_nhds).resolve_left (pow_ne_zero n hz)

theorem analyticAt_eventually_zero_of_scalar_pow_mul {R : E × ℂ → ℂ} {v : E × ℂ}
    (hR : AnalyticAt ℂ R v) (n : ℕ) (hP : ∀ᶠ u in 𝓝 v, u.2 ^ n * R u = 0) :
    ∀ᶠ u in 𝓝 v, R u = 0 :=
  eventually_zero_of_scalar_pow_mul n
    (hR.eventually_analyticAt.mono (fun _ h => h.continuousAt)) hP

end PGM
