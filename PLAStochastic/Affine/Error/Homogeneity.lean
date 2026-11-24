import PLAStochastic.Affine.Error.Pathwise
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Amplitude homogeneity and restriction of pathwise approximation errors

These are deterministic identities of the errors defined in `PLAStochastic/Affine/Error/Pathwise.lean`.
They do not assume Brownian scaling or a lifetime distribution identity.
-/

noncomputable section

namespace BrownianAffine

open scoped Pointwise

/-- Nonzero scalar multiplication preserves a real linear fitting subspace. -/
theorem smul_submodule_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) {c : ℝ} (hc : c ≠ 0) :
    c • (V : Set E) = (V : Set E) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact V.smul_mem c hv
  · intro hx
    refine ⟨c⁻¹ • x, V.smul_mem c⁻¹ hx, ?_⟩
    simp [smul_smul, hc]

@[simp] theorem bestError_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) : bestError V 0 = 0 :=
  Metric.infDist_zero_of_mem V.zero_mem

/-- Exact amplitude homogeneity, including zero and negative real amplitudes. -/
theorem bestError_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Submodule ℝ E) (c : ℝ) (f : E) :
    bestError V (c • f) = |c| * bestError V f := by
  by_cases hc : c = 0
  · simp [hc]
  · have h := infDist_smul₀ hc (V : Set E) f
    rw [smul_submodule_set V hc] at h
    simpa only [bestError, Real.norm_eq_abs] using h

theorem anchoredError_smul {T : ℝ} (f : Path T) (c : ℝ) :
    anchoredError (c • f) = |c| * anchoredError f :=
  bestError_smul (anchoredSubspace T) c f

theorem optimalError_smul {T : ℝ} (f : Path T) (c : ℝ) :
    optimalError (c • f) = |c| * optimalError f :=
  bestError_smul (affineSubspace T) c f

theorem anchoredError_smul_add_drift {T : ℝ} (f : Path T) (c a : ℝ) :
    anchoredError (c • f + a • timePath T) = |c| * anchoredError f := by
  rw [anchoredError_add_drift, anchoredError_smul]

theorem optimalError_smul_add_affine {T : ℝ} (f : Path T) (c a b : ℝ) :
    optimalError (c • f + (a • timePath T + b • (1 : Path T))) =
      |c| * optimalError f := by
  rw [optimalError_add_affine, optimalError_smul]

/-- Restrict a continuous path from [0,T] to the shorter interval [0,S]. -/
def restrictPath {S T : ℝ} (hST : S ≤ T) (f : Path T) : Path S :=
  f.comp ⟨Set.inclusion (Set.Icc_subset_Icc le_rfl hST),
    continuous_inclusion (Set.Icc_subset_Icc le_rfl hST)⟩

@[simp] theorem restrictPath_apply {S T : ℝ} (hST : S ≤ T) (f : Path T)
    (x : Set.Icc (0 : ℝ) S) :
    restrictPath hST f x = f ⟨x, x.property.1, x.property.2.trans hST⟩ := rfl

@[simp] theorem restrictPath_timePath {S T : ℝ} (hST : S ≤ T) :
    restrictPath hST (timePath T) = timePath S := by
  ext x
  rfl

@[simp] theorem restrictPath_one {S T : ℝ} (hST : S ≤ T) :
    restrictPath hST (1 : Path T) = (1 : Path S) := by
  ext x
  rfl

@[simp] theorem restrictPath_smul {S T : ℝ} (hST : S ≤ T) (c : ℝ) (f : Path T) :
    restrictPath hST (c • f) = c • restrictPath hST f := by
  ext x
  rfl

@[simp] theorem restrictPath_add {S T : ℝ} (hST : S ≤ T) (f g : Path T) :
    restrictPath hST (f + g) = restrictPath hST f + restrictPath hST g := by
  ext x
  rfl

/-- Restriction cannot increase uniform distance. -/
theorem restrictPath_dist_le {S T : ℝ} (hST : S ≤ T) (f g : Path T) :
    dist (restrictPath hST f) (restrictPath hST g) ≤ dist f g := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro x
  exact ContinuousMap.dist_apply_le_dist
    (f := f) (g := g) ⟨x, x.property.1, x.property.2.trans hST⟩

/-- Restriction of the interval cannot increase the best anchored approximation error. -/
theorem anchoredError_restrict_le {S T : ℝ} (hST : S ≤ T) (f : Path T) :
    anchoredError (restrictPath hST f) ≤ anchoredError f := by
  apply (Metric.le_infDist ⟨0, (anchoredSubspace T).zero_mem⟩).mpr
  intro g hg
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
  calc
    anchoredError (restrictPath hST f) ≤
        dist (restrictPath hST f) (a • timePath S) :=
      Metric.infDist_le_dist_of_mem
        (Submodule.mem_span_singleton.mpr ⟨a, rfl⟩)
    _ = dist (restrictPath hST f) (restrictPath hST (a • timePath T)) := by simp
    _ ≤ dist f (a • timePath T) := restrictPath_dist_le hST f _

/-- Restriction of the interval cannot increase the best unrestricted affine error. -/
theorem optimalError_restrict_le {S T : ℝ} (hST : S ≤ T) (f : Path T) :
    optimalError (restrictPath hST f) ≤ optimalError f := by
  apply (Metric.le_infDist ⟨0, (affineSubspace T).zero_mem⟩).mpr
  intro g hg
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hg
  calc
    optimalError (restrictPath hST f) ≤
        dist (restrictPath hST f) (a • timePath S + b • (1 : Path S)) :=
      Metric.infDist_le_dist_of_mem
        (Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩)
    _ = dist (restrictPath hST f)
        (restrictPath hST (a • timePath T + b • (1 : Path T))) := by simp
    _ ≤ dist f (a • timePath T + b • (1 : Path T)) := restrictPath_dist_le hST f _

end BrownianAffine
