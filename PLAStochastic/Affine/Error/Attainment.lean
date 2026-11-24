import PLAStochastic.Affine.Error.Pathwise
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Attainment of the pathwise fitting errors

The minimization takes place in a finite-dimensional fitting subspace. The
ambient continuous-path space is not assumed to be proper. A compact ball in
the fitting subspace contains a global minimizer, because points outside that
ball cannot improve on the zero fit.

The residual characterizations use `T ≥ 0` to ensure that the time interval is
nonempty. They allow any real tolerance, and cover `T = 0` explicitly.
-/

noncomputable section

namespace BrownianAffine

/-- Distance to any finite-dimensional real fitting subspace is attained.
Only the fitting subspace, not the ambient normed space, is proper. -/
theorem bestError_attained {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) [FiniteDimensional ℝ V] (f : E) :
    ∃ v ∈ V, bestError V f = dist f v := by
  let K : Set V := Metric.closedBall 0 (2 * ‖f‖)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hK₀ : (0 : V) ∈ K := by
    change dist (0 : V) 0 ≤ 2 * ‖f‖
    simp only [dist_self]
    positivity
  have hc : Continuous (fun v : V => dist f (v : E)) :=
    continuous_const.dist continuous_subtype_val
  obtain ⟨v, _, hmin⟩ := hK.exists_isMinOn ⟨0, hK₀⟩ hc.continuousOn
  refine ⟨v, v.property, le_antisymm (Metric.infDist_le_dist_of_mem v.property) ?_⟩
  apply (Metric.le_infDist ⟨0, V.zero_mem⟩).mpr
  intro y hy
  by_cases hyK : (⟨y, hy⟩ : V) ∈ K
  · exact hmin hyK
  · have hylarge : 2 * ‖f‖ < ‖y‖ := by
      simpa only [K, Metric.mem_closedBall, dist_zero_right,
        not_le] using! hyK
    have hv₀ : dist f (v : E) ≤ ‖f‖ := by simpa using hmin hK₀
    have htriangle : ‖y‖ ≤ dist f y + ‖f‖ := by
      simpa only [dist_zero_right, dist_comm y f] using dist_triangle y f (0 : E)
    linarith

/-- Attainment turns a weak error bound into an actual fit with that bound. -/
theorem bestError_le_iff_exists_fit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) [FiniteDimensional ℝ V] (f : E) (ε : ℝ) :
    bestError V f ≤ ε ↔ ∃ v ∈ V, dist f v ≤ ε := by
  constructor
  · intro h
    obtain ⟨v, hv, heq⟩ := bestError_attained V f
    exact ⟨v, hv, heq ▸ h⟩
  · rintro ⟨v, hv, hε⟩
    exact (Metric.infDist_le_dist_of_mem hv).trans hε

instance anchoredSubspace_finiteDimensional (T : ℝ) :
    FiniteDimensional ℝ (anchoredSubspace T) := by
  unfold anchoredSubspace
  exact FiniteDimensional.span_of_finite ℝ (by simp)

instance affineSubspace_finiteDimensional (T : ℝ) :
    FiniteDimensional ℝ (affineSubspace T) := by
  unfold affineSubspace
  exact FiniteDimensional.span_of_finite ℝ (by simp)

/-- Some slope realizes the anchored fitting error. -/
theorem exists_anchored_minimizer {T : ℝ} (f : Path T) :
    ∃ a : ℝ, anchoredError f = dist f (a • timePath T) := by
  obtain ⟨v, hv, heq⟩ := bestError_attained (anchoredSubspace T) f
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  exact ⟨a, heq⟩

/-- Some slope and intercept realize the unrestricted affine fitting error. -/
theorem exists_affine_minimizer {T : ℝ} (f : Path T) :
    ∃ a b : ℝ, optimalError f = dist f (a • timePath T + b • (1 : Path T)) := by
  obtain ⟨v, hv, heq⟩ := bestError_attained (affineSubspace T) f
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  exact ⟨a, b, heq⟩

/-- The anchored infimum of supremum residuals is a minimum. -/
theorem anchoredError_attained {T : ℝ} (f : Path T) :
    ∃ a : ℝ, anchoredError f =
      ⨆ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ)| := by
  obtain ⟨a, ha⟩ := exists_anchored_minimizer f
  exact ⟨a, ha.trans (dist_anchored_fit f a)⟩

/-- The unrestricted infimum of supremum residuals is a minimum. -/
theorem optimalError_attained {T : ℝ} (f : Path T) :
    ∃ a b : ℝ, optimalError f =
      ⨆ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ) - b| := by
  obtain ⟨a, b, hab⟩ := exists_affine_minimizer f
  exact ⟨a, b, hab.trans (dist_affine_fit f a b)⟩

/-- Weak anchored feasibility is equivalent to an actual line whose residual
is bounded at every time, including both endpoints. -/
theorem anchoredError_le_iff_exists_fit {T ε : ℝ} (hT : 0 ≤ T) (f : Path T) :
    anchoredError f ≤ ε ↔
      ∃ a : ℝ, ∀ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ)| ≤ ε := by
  let : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_anchored_minimizer f
    have hd : dist f (a • timePath T) ≤ ε := ha ▸ h
    exact ⟨a, by simpa [Real.dist_eq, timePath] using
      (ContinuousMap.dist_le_iff_of_nonempty.mp hd)⟩
  · rintro ⟨a, ha⟩
    have hd : dist f (a • timePath T) ≤ ε :=
      ContinuousMap.dist_le_iff_of_nonempty.mpr (by simpa [Real.dist_eq, timePath] using ha)
    exact (Metric.infDist_le_dist_of_mem
      (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩ : a • timePath T ∈ anchoredSubspace T)).trans hd

/-- Weak affine feasibility is equivalent to an actual line with a uniform
residual bound, with no open/closed tolerance gap. -/
theorem optimalError_le_iff_exists_fit {T ε : ℝ} (hT : 0 ≤ T) (f : Path T) :
    optimalError f ≤ ε ↔
      ∃ a b : ℝ, ∀ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ) - b| ≤ ε := by
  let : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := exists_affine_minimizer f
    have hd : dist f (a • timePath T + b • (1 : Path T)) ≤ ε := hab ▸ h
    exact ⟨a, b, by simpa [Real.dist_eq, timePath, sub_sub] using
      (ContinuousMap.dist_le_iff_of_nonempty.mp hd)⟩
  · rintro ⟨a, b, hab⟩
    have hd : dist f (a • timePath T + b • (1 : Path T)) ≤ ε :=
      ContinuousMap.dist_le_iff_of_nonempty.mpr (by
        simpa [Real.dist_eq, timePath, sub_sub] using hab)
    exact (Metric.infDist_le_dist_of_mem
      (Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩ :
        a • timePath T + b • (1 : Path T) ∈ affineSubspace T)).trans hd

/-- At duration zero, the anchored error is the absolute initial value. -/
theorem anchoredError_at_zero (f : Path 0) :
    anchoredError f = |f ⟨0, by simp⟩| := by
  apply le_antisymm
  · apply (anchoredError_le_iff_exists_fit le_rfl f).mpr
    refine ⟨0, fun t => ?_⟩
    have ht : t = ⟨0, by simp⟩ := Subtype.ext (le_antisymm t.property.2 t.property.1)
    subst t
    simp
  · obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit le_rfl f).mp le_rfl
    simpa using ha ⟨0, by simp⟩

/-- At duration zero, a constant affine fit is exact for any initial value. -/
theorem optimalError_at_zero (f : Path 0) : optimalError f = 0 := by
  apply le_antisymm ?_ (bestError_nonneg (affineSubspace 0) f)
  apply (optimalError_le_iff_exists_fit le_rfl f).mpr
  refine ⟨0, f ⟨0, by simp⟩, fun t => ?_⟩
  have ht : t = ⟨0, by simp⟩ := Subtype.ext (le_antisymm t.property.2 t.property.1)
  subst t
  simp

/-- The manuscript's origin condition makes both errors zero at duration zero. -/
theorem anchoredError_at_zero_of_origin (f : Path 0) (hf : f ⟨0, by simp⟩ = 0) :
    anchoredError f = 0 := by
  rw [anchoredError_at_zero, hf, abs_zero]

end BrownianAffine
