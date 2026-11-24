import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic

/-!
# Pathwise affine approximation

The path domain is the compact interval [0,T]. Its continuous-map distance is
the uniform distance, so distance to the one- and two-dimensional fitting
subspaces gives exactly the two infimum-of-supremum errors in the manuscript.
These results do not yet construct or evaluate any Brownian lifetime.
-/

noncomputable section

namespace BrownianAffine

abbrev Path (T : ℝ) := C(Set.Icc (0 : ℝ) T, ℝ)

/-- The time-coordinate path on the compact interval. -/
def timePath (T : ℝ) : Path T := ⟨fun t => (t : ℝ), continuous_subtype_val⟩

/-- Lines through the true origin. -/
def anchoredSubspace (T : ℝ) : Submodule ℝ (Path T) :=
  Submodule.span ℝ {timePath T}

/-- Unrestricted affine lines. -/
def affineSubspace (T : ℝ) : Submodule ℝ (Path T) :=
  Submodule.span ℝ {timePath T, (1 : Path T)}

/-- Distance to a linear space of fits. -/
def bestError {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) (f : E) : ℝ := Metric.infDist f (V : Set E)

def anchoredError {T : ℝ} (f : Path T) : ℝ := bestError (anchoredSubspace T) f

def optimalError {T : ℝ} (f : Path T) : ℝ := bestError (affineSubspace T) f

theorem bestError_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) (f : E) : 0 ≤ bestError V f := Metric.infDist_nonneg

theorem bestError_le_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) (f : E) : bestError V f ≤ ‖f‖ := by
  simpa [bestError] using Metric.infDist_le_dist_of_mem (x := f) V.zero_mem

theorem bestError_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) : LipschitzWith 1 (bestError V) :=
  Metric.lipschitz_infDist_pt (V : Set E)

theorem bestError_add_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) (f : E) {g : E} (hg : g ∈ V) :
    bestError V (f + g) ≤ bestError V f := by
  apply (Metric.le_infDist ⟨0, V.zero_mem⟩).mpr
  intro y hy
  have h := Metric.infDist_le_dist_of_mem (x := f + g) (V.add_mem hy hg)
  simpa only [bestError, dist_add_right] using h

/-- Adding any fitting function leaves the optimum error unchanged. -/
theorem bestError_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) (f : E) {g : E} (hg : g ∈ V) :
    bestError V (f + g) = bestError V f := by
  apply le_antisymm (bestError_add_le V f hg)
  simpa using bestError_add_le V (f + g) (V.neg_mem hg)

theorem anchoredSubspace_le_affine (T : ℝ) : anchoredSubspace T ≤ affineSubspace T := by
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  simp [hx]

theorem optimalError_le_anchoredError {T : ℝ} (f : Path T) :
    optimalError f ≤ anchoredError f :=
  Metric.infDist_le_infDist_of_subset (anchoredSubspace_le_affine T)
    ⟨0, (anchoredSubspace T).zero_mem⟩

theorem anchoredError_lipschitz (T : ℝ) :
    LipschitzWith 1 (anchoredError (T := T)) := bestError_lipschitz _

theorem optimalError_lipschitz (T : ℝ) :
    LipschitzWith 1 (optimalError (T := T)) := bestError_lipschitz _

theorem continuous_anchoredError (T : ℝ) : Continuous (anchoredError (T := T)) :=
  (anchoredError_lipschitz T).continuous

theorem continuous_optimalError (T : ℝ) : Continuous (optimalError (T := T)) :=
  (optimalError_lipschitz T).continuous

/-- The manuscript's invariance under adding linear drift, in the anchored model. -/
theorem anchoredError_add_drift {T : ℝ} (f : Path T) (a : ℝ) :
    anchoredError (f + a • timePath T) = anchoredError f := by
  apply bestError_add
  exact Submodule.mem_span_singleton.mpr ⟨a, rfl⟩

/-- The unrestricted error is invariant under adding any affine function. -/
theorem optimalError_add_affine {T : ℝ} (f : Path T) (a b : ℝ) :
    optimalError (f + (a • timePath T + b • (1 : Path T))) = optimalError f := by
  apply bestError_add
  exact Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩

theorem dist_anchored_fit {T : ℝ} (f : Path T) (a : ℝ) :
    dist f (a • timePath T) = ⨆ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ)| := by
  simp [ContinuousMap.dist_eq_iSup, Real.dist_eq, timePath]

theorem dist_affine_fit {T : ℝ} (f : Path T) (a b : ℝ) :
    dist f (a • timePath T + b • (1 : Path T)) =
      ⨆ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ) - b| := by
  simp [ContinuousMap.dist_eq_iSup, Real.dist_eq, timePath, sub_sub]

/-- Exact greatest-lower-bound characterization by the paper's anchored residuals. -/
theorem anchoredError_isGLB {T : ℝ} (f : Path T) :
    IsGLB (Set.range fun a : ℝ => ⨆ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ)|)
      (anchoredError f) := by
  have hset : (fun g : Path T => dist f g) '' (anchoredSubspace T : Set (Path T)) =
      Set.range (fun a : ℝ => ⨆ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ)|) := by
    ext r
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
      exact ⟨a, (dist_anchored_fit f a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a • timePath T, Submodule.mem_span_singleton.mpr ⟨a, rfl⟩,
        dist_anchored_fit f a⟩
  rw [← hset]
  exact Metric.isGLB_infDist ⟨0, (anchoredSubspace T).zero_mem⟩

/-- Exact greatest-lower-bound characterization by the paper's affine residuals. -/
theorem optimalError_isGLB {T : ℝ} (f : Path T) :
    IsGLB (Set.range fun ab : ℝ × ℝ =>
      ⨆ t : Set.Icc (0 : ℝ) T, |f t - ab.1 * (t : ℝ) - ab.2|) (optimalError f) := by
  have hset : (fun g : Path T => dist f g) '' (affineSubspace T : Set (Path T)) =
      Set.range (fun ab : ℝ × ℝ =>
        ⨆ t : Set.Icc (0 : ℝ) T, |f t - ab.1 * (t : ℝ) - ab.2|) := by
    ext r
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hg
      exact ⟨(a, b), (dist_affine_fit f a b).symm⟩
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a • timePath T + b • (1 : Path T),
        Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩, dist_affine_fit f a b⟩
  rw [← hset]
  exact Metric.isGLB_infDist ⟨0, (affineSubspace T).zero_mem⟩

theorem anchoredError_eq_sInf {T : ℝ} (f : Path T) :
    anchoredError f = sInf (Set.range fun a : ℝ =>
      ⨆ t : Set.Icc (0 : ℝ) T, |f t - a * (t : ℝ)|) :=
  ((anchoredError_isGLB f).csInf_eq (Set.range_nonempty _)).symm

theorem optimalError_eq_sInf {T : ℝ} (f : Path T) :
    optimalError f = sInf (Set.range fun ab : ℝ × ℝ =>
      ⨆ t : Set.Icc (0 : ℝ) T, |f t - ab.1 * (t : ℝ) - ab.2|) :=
  ((optimalError_isGLB f).csInf_eq (Set.range_nonempty _)).symm

end BrownianAffine
