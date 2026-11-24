import PLAStochastic.Affine.Error.Homogeneity

/-!
# The deterministic error processes in time

All paths in this module are continuous real functions. Reparametrization onto
a fixed unit interval gives a continuous error process; its agreement with the
original interval formulation is proved by transforming all fitting slopes.
-/

noncomputable section

namespace BrownianAffine

/-- Restriction of a global continuous path to the observation interval. -/
def intervalPath (f : C(ℝ, ℝ)) (T : ℝ) : Path T := f.restrict (Set.Icc 0 T)

/-- Reparametrize the observed path on the fixed unit interval. -/
def unitPath (f : C(ℝ, ℝ)) (T : ℝ) : Path 1 :=
  ⟨fun u => f (T * (u : ℝ)), f.continuous.comp (continuous_const.mul continuous_subtype_val)⟩

def anchoredTimeError (f : C(ℝ, ℝ)) (T : ℝ) : ℝ := anchoredError (unitPath f T)

def optimalTimeError (f : C(ℝ, ℝ)) (T : ℝ) : ℝ := optimalError (unitPath f T)

theorem continuous_unitPath (f : C(ℝ, ℝ)) : Continuous (unitPath f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × Set.Icc (0 : ℝ) 1 => f (p.1 * (p.2 : ℝ)))
  exact f.continuous.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))

theorem continuous_anchoredTimeError (f : C(ℝ, ℝ)) : Continuous (anchoredTimeError f) :=
  (continuous_anchoredError 1).comp (continuous_unitPath f)

theorem continuous_optimalTimeError (f : C(ℝ, ℝ)) : Continuous (optimalTimeError f) :=
  (continuous_optimalError 1).comp (continuous_unitPath f)

/-- The change of time coordinate from [0,1] to [0,T]. -/
def unitToInterval {T : ℝ} (hT : 0 < T) :
    C(Set.Icc (0 : ℝ) 1, Set.Icc (0 : ℝ) T) :=
  ⟨fun u => ⟨T * (u : ℝ), mul_nonneg hT.le u.property.1,
    by have := u.property.2; nlinarith⟩,
    (continuous_const.mul continuous_subtype_val).subtype_mk _⟩

theorem unitToInterval_surjective {T : ℝ} (hT : 0 < T) :
    Function.Surjective (unitToInterval hT) := by
  intro x
  refine ⟨⟨(x : ℝ) / T, div_nonneg x.property.1 hT.le,
    (div_le_one hT).mpr x.property.2⟩, ?_⟩
  apply Subtype.ext
  change T * ((x : ℝ) / T) = x
  field_simp

def pullbackInterval {T : ℝ} (hT : 0 < T) (g : Path T) : Path 1 :=
  g.comp (unitToInterval hT)

/-- Surjectivity of the time change preserves the uniform distance exactly. -/
theorem pullbackInterval_dist {T : ℝ} (hT : 0 < T) (f g : Path T) :
    dist (pullbackInterval hT f) (pullbackInterval hT g) = dist f g := by
  apply le_antisymm
  · apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro u
    exact ContinuousMap.dist_apply_le_dist (f := f) (g := g) (unitToInterval hT u)
  · apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro x
    obtain ⟨u, rfl⟩ := unitToInterval_surjective hT x
    exact ContinuousMap.dist_apply_le_dist
      (f := pullbackInterval hT f) (g := pullbackInterval hT g) u

@[simp] theorem pullbackInterval_intervalPath {T : ℝ} (hT : 0 < T) (f : C(ℝ, ℝ)) :
    pullbackInterval hT (intervalPath f T) = unitPath f T := by ext u; rfl

@[simp] theorem pullbackInterval_timePath {T : ℝ} (hT : 0 < T) :
    pullbackInterval hT (timePath T) = T • timePath 1 := by ext u; rfl

@[simp] theorem pullbackInterval_one {T : ℝ} (hT : 0 < T) :
    pullbackInterval hT (1 : Path T) = (1 : Path 1) := by ext u; rfl

@[simp] theorem pullbackInterval_smul {T : ℝ} (hT : 0 < T) (a : ℝ) (g : Path T) :
    pullbackInterval hT (a • g) = a • pullbackInterval hT g := by ext u; rfl

@[simp] theorem pullbackInterval_add {T : ℝ} (hT : 0 < T) (f g : Path T) :
    pullbackInterval hT (f + g) = pullbackInterval hT f + pullbackInterval hT g := by
  ext u
  rfl

theorem dist_unit_anchored_fit {T : ℝ} (hT : 0 < T) (f : C(ℝ, ℝ)) (a : ℝ) :
    dist (unitPath f T) (a • timePath 1) =
      dist (intervalPath f T) ((a / T) • timePath T) := by
  have h := pullbackInterval_dist hT (intervalPath f T) ((a / T) • timePath T)
  simpa only [pullbackInterval_intervalPath, pullbackInterval_smul,
    pullbackInterval_timePath, smul_smul, div_mul_cancel₀ _ hT.ne'] using h

theorem dist_unit_affine_fit {T : ℝ} (hT : 0 < T) (f : C(ℝ, ℝ)) (a b : ℝ) :
    dist (unitPath f T) (a • timePath 1 + b • (1 : Path 1)) =
      dist (intervalPath f T) ((a / T) • timePath T + b • (1 : Path T)) := by
  have h := pullbackInterval_dist hT (intervalPath f T)
    ((a / T) • timePath T + b • (1 : Path T))
  simpa only [pullbackInterval_intervalPath, pullbackInterval_add, pullbackInterval_smul,
    pullbackInterval_timePath, pullbackInterval_one, smul_smul,
    div_mul_cancel₀ _ hT.ne'] using h

/-- For positive T, unit-interval parametrization gives the original anchored error. -/
theorem anchoredTimeError_eq_interval_of_pos {T : ℝ} (hT : 0 < T) (f : C(ℝ, ℝ)) :
    anchoredTimeError f T = anchoredError (intervalPath f T) := by
  apply le_antisymm
  · apply (Metric.le_infDist ⟨0, (anchoredSubspace T).zero_mem⟩).mpr
    intro g hg
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
    have h := Metric.infDist_le_dist_of_mem (x := unitPath f T)
      (show (a * T) • timePath 1 ∈ anchoredSubspace 1 from
        Submodule.mem_span_singleton.mpr ⟨a * T, rfl⟩)
    rw [dist_unit_anchored_fit hT f (a * T)] at h
    simpa only [mul_div_cancel_right₀ _ hT.ne', anchoredTimeError, anchoredError,
      bestError] using h
  · apply (Metric.le_infDist ⟨0, (anchoredSubspace 1).zero_mem⟩).mpr
    intro g hg
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
    rw [dist_unit_anchored_fit hT f a]
    exact Metric.infDist_le_dist_of_mem (Submodule.mem_span_singleton.mpr ⟨a / T, rfl⟩)

/-- The same slope change preserves unrestricted affine fitting. -/
theorem optimalTimeError_eq_interval_of_pos {T : ℝ} (hT : 0 < T) (f : C(ℝ, ℝ)) :
    optimalTimeError f T = optimalError (intervalPath f T) := by
  apply le_antisymm
  · apply (Metric.le_infDist ⟨0, (affineSubspace T).zero_mem⟩).mpr
    intro g hg
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hg
    have h := Metric.infDist_le_dist_of_mem (x := unitPath f T)
      (show (a * T) • timePath 1 + b • (1 : Path 1) ∈ affineSubspace 1 from
        Submodule.mem_span_pair.mpr ⟨a * T, b, rfl⟩)
    rw [dist_unit_affine_fit hT f (a * T) b] at h
    simpa only [mul_div_cancel_right₀ _ hT.ne', optimalTimeError, optimalError,
      bestError] using h
  · apply (Metric.le_infDist ⟨0, (affineSubspace 1).zero_mem⟩).mpr
    intro g hg
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hg
    rw [dist_unit_affine_fit hT f a b]
    exact Metric.infDist_le_dist_of_mem (Submodule.mem_span_pair.mpr ⟨a / T, b, rfl⟩)

/-- A constant path's anchored error is its initial magnitude, even on the zero interval. -/
theorem anchoredError_const {T : ℝ} (hT : 0 ≤ T) (b : ℝ) :
    anchoredError (ContinuousMap.const (Set.Icc (0 : ℝ) T) b) = |b| := by
  apply le_antisymm
  · calc
      anchoredError (ContinuousMap.const (Set.Icc (0 : ℝ) T) b) ≤
          dist (ContinuousMap.const (Set.Icc (0 : ℝ) T) b) (0 : Path T) :=
        Metric.infDist_le_dist_of_mem (anchoredSubspace T).zero_mem
      _ ≤ |b| := (ContinuousMap.dist_le (abs_nonneg b)).mpr (by
        intro u
        simp)
  · apply (Metric.le_infDist ⟨0, (anchoredSubspace T).zero_mem⟩).mpr
    intro g hg
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hg
    have h := ContinuousMap.dist_apply_le_dist
      (f := ContinuousMap.const (Set.Icc (0 : ℝ) T) b) (g := a • timePath T)
      ⟨0, le_rfl, hT⟩
    simpa [timePath, Real.dist_eq] using h

/-- Unrestricted affine fitting represents every constant exactly. -/
theorem optimalError_const (T b : ℝ) :
    optimalError (ContinuousMap.const (Set.Icc (0 : ℝ) T) b) = 0 := by
  apply Metric.infDist_zero_of_mem
  apply Submodule.mem_span_pair.mpr
  refine ⟨0, b, ?_⟩
  ext u
  simp

@[simp] theorem unitPath_zero (f : C(ℝ, ℝ)) :
    unitPath f 0 = ContinuousMap.const (Set.Icc (0 : ℝ) 1) (f 0) := by
  ext u
  simp [unitPath]

@[simp] theorem intervalPath_zero (f : C(ℝ, ℝ)) :
    intervalPath f 0 = ContinuousMap.const (Set.Icc (0 : ℝ) 0) (f 0) := by
  ext u
  have hu : (u : ℝ) = 0 := le_antisymm u.property.2 u.property.1
  change f (u : ℝ) = f 0
  rw [hu]

theorem anchoredTimeError_zero (f : C(ℝ, ℝ)) : anchoredTimeError f 0 = |f 0| := by
  rw [anchoredTimeError, unitPath_zero, anchoredError_const zero_le_one]

theorem optimalTimeError_zero (f : C(ℝ, ℝ)) : optimalTimeError f 0 = 0 := by
  rw [optimalTimeError, unitPath_zero, optimalError_const]

theorem anchoredTimeError_zero_of_start_zero (f : C(ℝ, ℝ)) (hf : f 0 = 0) :
    anchoredTimeError f 0 = 0 := by rw [anchoredTimeError_zero, hf, abs_zero]

/-- Agreement with the paper's original interval error includes T = 0. -/
theorem anchoredTimeError_eq_interval {T : ℝ} (hT : 0 ≤ T) (f : C(ℝ, ℝ)) :
    anchoredTimeError f T = anchoredError (intervalPath f T) := by
  rcases eq_or_lt_of_le hT with heq | hpos
  · subst T
    rw [anchoredTimeError_zero, intervalPath_zero, anchoredError_const le_rfl]
  · exact anchoredTimeError_eq_interval_of_pos hpos f

theorem optimalTimeError_eq_interval {T : ℝ} (hT : 0 ≤ T) (f : C(ℝ, ℝ)) :
    optimalTimeError f T = optimalError (intervalPath f T) := by
  rcases eq_or_lt_of_le hT with heq | hpos
  · subst T
    rw [optimalTimeError_zero, intervalPath_zero, optimalError_const]
  · exact optimalTimeError_eq_interval_of_pos hpos f

theorem intervalPath_restrict {S T : ℝ} (hST : S ≤ T) (f : C(ℝ, ℝ)) :
    restrictPath hST (intervalPath f T) = intervalPath f S := by ext u; rfl

theorem anchoredTimeError_monotoneOn (f : C(ℝ, ℝ)) :
    MonotoneOn (anchoredTimeError f) (Set.Ici 0) := by
  intro S hS T hT hST
  rw [anchoredTimeError_eq_interval hS, anchoredTimeError_eq_interval hT,
    ← intervalPath_restrict hST f]
  exact anchoredError_restrict_le hST (intervalPath f T)

theorem optimalTimeError_monotoneOn (f : C(ℝ, ℝ)) :
    MonotoneOn (optimalTimeError f) (Set.Ici 0) := by
  intro S hS T hT hST
  rw [optimalTimeError_eq_interval hS, optimalTimeError_eq_interval hT,
    ← intervalPath_restrict hST f]
  exact optimalError_restrict_le hST (intervalPath f T)

theorem optimalTimeError_le_anchoredTimeError (f : C(ℝ, ℝ)) (T : ℝ) :
    optimalTimeError f T ≤ anchoredTimeError f T :=
  optimalError_le_anchoredError (unitPath f T)

/-- Deterministic dilation of the time parameter of a global path. -/
def dilatePath (f : C(ℝ, ℝ)) (c : ℝ) : C(ℝ, ℝ) :=
  f.comp ⟨fun u => c * u, continuous_const.mul continuous_id⟩

@[simp] theorem unitPath_dilate (f : C(ℝ, ℝ)) (c T : ℝ) :
    unitPath (dilatePath f c) T = unitPath f (c * T) := by
  ext u
  change f (c * (T * (u : ℝ))) = f ((c * T) * (u : ℝ))
  rw [mul_assoc]

theorem anchoredTimeError_dilate (f : C(ℝ, ℝ)) (c T : ℝ) :
    anchoredTimeError (dilatePath f c) T = anchoredTimeError f (c * T) := by
  simp only [anchoredTimeError, unitPath_dilate]

theorem optimalTimeError_dilate (f : C(ℝ, ℝ)) (c T : ℝ) :
    optimalTimeError (dilatePath f c) T = optimalTimeError f (c * T) := by
  simp only [optimalTimeError, unitPath_dilate]

@[simp] theorem unitPath_smul (f : C(ℝ, ℝ)) (a T : ℝ) :
    unitPath (a • f) T = a • unitPath f T := by ext u; rfl

@[simp] theorem unitPath_add (f g : C(ℝ, ℝ)) (T : ℝ) :
    unitPath (f + g) T = unitPath f T + unitPath g T := by ext u; rfl

theorem anchoredTimeError_smul (f : C(ℝ, ℝ)) (a T : ℝ) :
    anchoredTimeError (a • f) T = |a| * anchoredTimeError f T := by
  simp only [anchoredTimeError, unitPath_smul, anchoredError_smul]

theorem optimalTimeError_smul (f : C(ℝ, ℝ)) (a T : ℝ) :
    optimalTimeError (a • f) T = |a| * optimalTimeError f T := by
  simp only [optimalTimeError, unitPath_smul, optimalError_smul]

theorem anchoredTimeError_nonneg (f : C(ℝ, ℝ)) (T : ℝ) :
    0 ≤ anchoredTimeError f T := bestError_nonneg _ _

theorem optimalTimeError_nonneg (f : C(ℝ, ℝ)) (T : ℝ) :
    0 ≤ optimalTimeError f T := bestError_nonneg _ _

/-- A deterministic affine function on the global time domain. -/
def affinePath (a b : ℝ) : C(ℝ, ℝ) :=
  ⟨fun u => a * u + b, (continuous_const.mul continuous_id).add continuous_const⟩

@[simp] theorem unitPath_affinePath (a b T : ℝ) :
    unitPath (affinePath a b) T = (a * T) • timePath 1 + b • (1 : Path 1) := by
  ext u
  change a * (T * (u : ℝ)) + b = (a * T) * (u : ℝ) + b * 1
  ring

theorem anchoredTimeError_add_drift (f : C(ℝ, ℝ)) (a T : ℝ) :
    anchoredTimeError (f + affinePath a 0) T = anchoredTimeError f T := by
  simp only [anchoredTimeError, unitPath_add, unitPath_affinePath, zero_smul, add_zero,
    anchoredError_add_drift]

theorem optimalTimeError_add_affine (f : C(ℝ, ℝ)) (a b T : ℝ) :
    optimalTimeError (f + affinePath a b) T = optimalTimeError f T := by
  simp only [optimalTimeError, unitPath_add, unitPath_affinePath, optimalError_add_affine]

theorem anchoredTimeError_smul_add_drift (f : C(ℝ, ℝ)) (σ a T : ℝ) :
    anchoredTimeError (σ • f + affinePath a 0) T = |σ| * anchoredTimeError f T := by
  rw [anchoredTimeError_add_drift, anchoredTimeError_smul]

theorem optimalTimeError_smul_add_affine (f : C(ℝ, ℝ)) (σ a b T : ℝ) :
    optimalTimeError (σ • f + affinePath a b) T = |σ| * optimalTimeError f T := by
  rw [optimalTimeError_add_affine, optimalTimeError_smul]

end BrownianAffine
