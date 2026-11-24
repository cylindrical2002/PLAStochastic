import PLAStochastic.Affine.Lifetime.Pathwise
import PLAStochastic.Affine.Error.Attainment
import PLAStochastic.ForMathlib.Probability.FirstExceedance.OrderedApproximation
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Actual finite-mesh anchored errors

The observations are exactly 0, h, ..., floor(T / h) * h. Their finite
minimax error is a distance to the one-dimensional sampled fitting space.
The mesh limit below is proved from continuity of the path.
-/

noncomputable section
open Filter
open scoped Topology NNReal ENNReal

namespace BrownianAffine

abbrev MeshIndex (T h : ℝ) := Fin (⌊T / h⌋₊ + 1)

def meshTimes (T h : ℝ) (i : MeshIndex T h) : ℝ := (i : ℕ) * h

def meshValues (f : C(ℝ, ℝ)) (T h : ℝ) (i : MeshIndex T h) : ℝ :=
  f (meshTimes T h i)

def meshAnchoredSubspace (T h : ℝ) : Submodule ℝ (MeshIndex T h → ℝ) :=
  Submodule.span ℝ {meshTimes T h}

/-- The true finite-grid infimum over all real anchored slopes. -/
def finiteMeshAnchoredError (f : C(ℝ, ℝ)) (T h : ℝ) : ℝ :=
  bestError (meshAnchoredSubspace T h) (meshValues f T h)

theorem finiteMeshAnchoredError_nonneg (f : C(ℝ, ℝ)) (T h : ℝ) :
    0 ≤ finiteMeshAnchoredError f T h := bestError_nonneg _ _

/-- A finite-grid error bound is equivalent to one actual slope fitting every listed sample. -/
theorem finiteMeshAnchoredError_le_iff (f : C(ℝ, ℝ)) (T h ε : ℝ) :
    finiteMeshAnchoredError f T h ≤ ε ↔
      ∃ a : ℝ, ∀ i : MeshIndex T h, |f (meshTimes T h i) - a * meshTimes T h i| ≤ ε := by
  rw [finiteMeshAnchoredError, bestError_le_iff_exists_fit]
  constructor
  · rintro ⟨v, hv, hε⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨a, ?_⟩
    simpa only [dist_eq_norm, pi_norm_le_iff_of_nonempty, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, meshValues] using hε
  · rintro ⟨a, ha⟩
    refine ⟨a • meshTimes T h, Submodule.mem_span_singleton.mpr ⟨a, rfl⟩, ?_⟩
    simpa only [dist_eq_norm, pi_norm_le_iff_of_nonempty, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, meshValues] using ha

theorem meshFloor_mul_le {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) :
    (⌊T / h⌋₊ : ℝ) * h ≤ T :=
  (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hT hh.le))

theorem meshFloor_gap_lt {T h : ℝ} (hh : 0 < h) :
    T - (⌊T / h⌋₊ : ℝ) * h < h := by
  have h := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (T / h))
  nlinarith

theorem meshTimes_mem {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) (i : MeshIndex T h) :
    meshTimes T h i ∈ Set.Icc (0 : ℝ) T := by
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) hh.le
  · calc
      meshTimes T h i ≤ (⌊T / h⌋₊ : ℝ) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        exact_mod_cast Nat.le_of_lt_succ i.isLt
      _ ≤ T := meshFloor_mul_le hT hh

/-- Removing observations cannot increase the actual fitting error. -/
theorem finiteMeshAnchoredError_le_continuous (f : C(ℝ, ℝ))
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) :
    finiteMeshAnchoredError f T h ≤ anchoredTimeError f T := by
  rw [anchoredTimeError_eq_interval hT]
  obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit hT (intervalPath f T)).mp le_rfl
  apply (finiteMeshAnchoredError_le_iff _ _ _ _).mpr
  exact ⟨a, fun i => ha ⟨meshTimes T h i, meshTimes_mem hT hh i⟩⟩

theorem path_value_le_interval_norm (f : C(ℝ, ℝ)) {T t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) : |f t| ≤ ‖intervalPath f T‖ := by
  simpa [intervalPath] using
    (intervalPath f T).norm_coe_le_norm ⟨t, ht⟩

theorem finiteMeshAnchoredError_le_interval_norm (f : C(ℝ, ℝ))
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) :
    finiteMeshAnchoredError f T h ≤ ‖intervalPath f T‖ := by
  apply (finiteMeshAnchoredError_le_continuous f hT hh).trans
  rw [anchoredTimeError_eq_interval hT]
  exact bestError_le_norm _ _

/-- Grid minimizers have a slope bound independent of all sufficiently small meshes. -/
theorem finiteMeshAnchoredError_bounded_slope (f : C(ℝ, ℝ))
    {T h : ℝ} (hT : 0 < T) (hh : 0 < h) (hhT : h < T / 2) :
    ∃ a : ℝ, |a| ≤ 4 * ‖intervalPath f T‖ / T ∧
      ∀ i : MeshIndex T h,
        |f (meshTimes T h i) - a * meshTimes T h i| ≤ finiteMeshAnchoredError f T h := by
  obtain ⟨a, ha⟩ := (finiteMeshAnchoredError_le_iff f T h
    (finiteMeshAnchoredError f T h)).mp le_rfl
  refine ⟨a, ?_, ha⟩
  let i : MeshIndex T h := ⟨⌊T / h⌋₊, Nat.lt_succ_self _⟩
  have hi := meshTimes_mem hT.le hh i
  have hg : T / 2 < meshTimes T h i := by
    have := meshFloor_gap_lt (T := T) hh
    change T / 2 < (⌊T / h⌋₊ : ℝ) * h
    linarith
  have hres := (ha i).trans (finiteMeshAnchoredError_le_interval_norm f hT.le hh)
  have hval := path_value_le_interval_norm f hi
  have hbound := abs_sub (f (meshTimes T h i) - a * meshTimes T h i)
    (f (meshTimes T h i))
  rw [show (f (meshTimes T h i) - a * meshTimes T h i) -
    f (meshTimes T h i) = -(a * meshTimes T h i) by ring,
    abs_neg, abs_mul, abs_of_nonneg hi.1] at hbound
  apply (le_div_iff₀ hT).mpr
  have habs := abs_nonneg a
  nlinarith

/-- Every time in the interval has a grid observation less than one mesh width to its left. -/
theorem exists_meshTime_close {T h t : ℝ} (hh : 0 < h)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ i : MeshIndex T h, meshTimes T h i ≤ t ∧ |t - meshTimes T h i| < h := by
  have hindex : ⌊t / h⌋₊ ≤ ⌊T / h⌋₊ :=
    Nat.floor_mono ((div_le_div_iff_of_pos_right hh).mpr ht.2)
  let i : MeshIndex T h := ⟨⌊t / h⌋₊, Nat.lt_succ_of_le hindex⟩
  have hle : meshTimes T h i ≤ t := meshFloor_mul_le ht.1 hh
  refine ⟨i, hle, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  exact meshFloor_gap_lt hh

/-- A modulus-of-continuity estimate compares the actual optimized errors.
The modulus hypothesis concerns the given continuous path, not convergence of fitted errors. -/
theorem continuous_error_le_finiteMesh_add (f : C(ℝ, ℝ))
    {T h δ η : ℝ} (hT : 0 < T) (hh : 0 < h) (hhT : h < T / 2) (hhδ : h < δ)
    (hmod : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      |s - t| < δ → |f s - f t| < η) :
    anchoredTimeError f T ≤ finiteMeshAnchoredError f T h + η +
      (4 * ‖intervalPath f T‖ / T) * h := by
  obtain ⟨a, habound, ha⟩ := finiteMeshAnchoredError_bounded_slope f hT hh hhT
  rw [anchoredTimeError_eq_interval hT.le]
  apply (anchoredError_le_iff_exists_fit hT.le (intervalPath f T)).mpr
  refine ⟨a, fun t => ?_⟩
  obtain ⟨i, _, hclose⟩ := exists_meshTime_close hh t.property
  have hi := meshTimes_mem hT.le hh i
  have hm := hmod t t.property (meshTimes T h i) hi (hclose.trans hhδ)
  have hres := ha i
  have h₁ := abs_sub_le (f (t : ℝ)) (f (meshTimes T h i)) (a * (t : ℝ))
  have h₂ := abs_sub_le (f (meshTimes T h i)) (a * meshTimes T h i) (a * (t : ℝ))
  have hmul : |a * meshTimes T h i - a * (t : ℝ)| ≤
      (4 * ‖intervalPath f T‖ / T) * h := by
    rw [← mul_sub, abs_mul, abs_sub_comm]
    exact mul_le_mul habound hclose.le (abs_nonneg _) (by positivity)
  change |f (t : ℝ) - a * (t : ℝ)| ≤ _
  linarith

theorem finiteMeshAnchoredError_at_zero (f : C(ℝ, ℝ)) (h : ℝ) :
    finiteMeshAnchoredError f 0 h = |f 0| := by
  have htime (i : MeshIndex 0 h) : meshTimes 0 h i = 0 := by
    have hi : (i : ℕ) = 0 := by
      have := i.isLt
      simp only [zero_div, Nat.floor_zero] at this
      omega
    simp [meshTimes, hi]
  apply le_antisymm
  · apply (finiteMeshAnchoredError_le_iff _ _ _ _).mpr
    exact ⟨0, fun i => by simp [htime]⟩
  · obtain ⟨a, ha⟩ := (finiteMeshAnchoredError_le_iff f 0 h
      (finiteMeshAnchoredError f 0 h)).mp le_rfl
    simpa [htime] using ha ⟨0, by simp⟩

/-- For every fixed nonnegative horizon, the actual finite-grid minimax errors
converge to the continuous anchored error as the positive mesh tends to zero. -/
theorem tendsto_finiteMeshAnchoredError (f : C(ℝ, ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun h : ℝ => finiteMeshAnchoredError f T h) (𝓝[>] 0)
      (𝓝 (anchoredTimeError f T)) := by
  rcases eq_or_lt_of_le hT with rfl | hT
  · simpa only [finiteMeshAnchoredError_at_zero, anchoredTimeError_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => |f 0|) (𝓝[>] 0) (𝓝 |f 0|))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu : UniformContinuousOn f (Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 4) (by positivity)
  let M := 4 * ‖intervalPath f T‖ / T
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let r := min (T / 2) (min δ (ε / (4 * (M + 1))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhr
  have hhpos : 0 < h := hh
  have hhT : h < T / 2 := hhr.trans_le (min_le_left _ _)
  have hhδ : h < δ := hhr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhε : h < ε / (4 * (M + 1)) :=
    hhr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hMh : M * h < ε / 4 := by
    have := (lt_div_iff₀ (show 0 < 4 * (M + 1) by positivity)).mp hhε
    nlinarith
  have hlower := finiteMeshAnchoredError_le_continuous f hT.le hhpos
  have hupper := continuous_error_le_finiteMesh_add f hT hhpos hhT hhδ
    (by intro s hs t ht hst; exact hmod s hs t ht (by simpa [Real.dist_eq] using hst))
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlower)]
  dsimp [M] at hMh
  linarith

/-- Extending the observation horizon only adds actual grid constraints. -/
theorem finiteMeshAnchoredError_monotone_time (f : C(ℝ, ℝ)) {h : ℝ} (hh : 0 < h) :
    Monotone (fun T : ℝ => finiteMeshAnchoredError f T h) := by
  intro S T hST
  obtain ⟨a, ha⟩ := (finiteMeshAnchoredError_le_iff f T h
    (finiteMeshAnchoredError f T h)).mp le_rfl
  apply (finiteMeshAnchoredError_le_iff f S h _).mpr
  refine ⟨a, fun i => ?_⟩
  have hfloor : ⌊S / h⌋₊ ≤ ⌊T / h⌋₊ :=
    Nat.floor_mono ((div_le_div_iff_of_pos_right hh).mpr hST)
  have hi : (i : ℕ) < ⌊T / h⌋₊ + 1 := by omega
  exact ha ⟨i, hi⟩

/-- The actual error convergence also holds along any positive mesh family tending to zero. -/
theorem tendsto_finiteMeshAnchoredError_of_mesh (f : C(ℝ, ℝ)) {T : ℝ} (hT : 0 ≤ T)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0)) :
    Tendsto (fun i => finiteMeshAnchoredError f T (h i)) l (𝓝 (anchoredTimeError f T)) := by
  have hw : Tendsto h l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hconv, Eventually.of_forall hh⟩
  exact (tendsto_finiteMeshAnchoredError f hT).comp hw

/-- First strict infeasibility of the actual finite-grid fitting problems. -/
def finiteMeshAnchoredLifetime (f : C(ℝ, ℝ)) (h ε : ℝ) : ℝ≥0∞ :=
  firstExceedance (fun T : ℝ≥0 => finiteMeshAnchoredError f T h) ε

/-- The actual sampled lifetime converges, including infinite lifetimes.
Only continuity of the given path and convergence of the positive mesh are assumed. -/
theorem tendsto_finiteMeshAnchoredLifetime (f : C(ℝ, ℝ)) (ε : ℝ)
    {ι : Type*} {l : Filter ι} {h : ι → ℝ}
    (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0)) :
    Tendsto (fun i => finiteMeshAnchoredLifetime f (h i) ε) l (𝓝 (anchoredLifetime f ε)) :=
  tendsto_firstExceedance_of_ordered_approximation ε
    (fun i T => finiteMeshAnchoredError_le_continuous f T.coe_nonneg (hh i))
    (fun T => tendsto_finiteMeshAnchoredError_of_mesh f T.coe_nonneg hh hconv)

end BrownianAffine
