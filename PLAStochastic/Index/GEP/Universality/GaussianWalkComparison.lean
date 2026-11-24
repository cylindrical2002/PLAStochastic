import PLAStochastic.Index.GEP.Universality.StrongApproxInterface
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers
import PLAStochastic.Index.GEP.Universality.BrownianLifetimeLaw
import PLAStochastic.Brownian.PathLaw.MeshIncrements
import PLAStochastic.Affine.Process.DriftedSurvival.GridChernoff
import PLAStochastic.Affine.Lifetime.BrownianProcess

/-! # Gaussian affine fits and their continuous Brownian comparison -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set BrownianAffine
open scoped NNReal ENNReal

/-- Interpolation between two residuals adds at most twice the cell oscillation. -/
theorem affine_cell_error_le {f₀ f₁ f x a b h α e r : ℝ}
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hr : 0 ≤ r)
    (h₀ : |f₀ - a * x - b| ≤ e)
    (h₁ : |f₁ - a * (x + h) - b| ≤ e)
    (hf : |f - f₀| ≤ r) (hd : |f₁ - f₀| ≤ r) :
    |f - a * (x + α * h) - b| ≤ e + 2 * r := by
  have hc : |(1 - α) * (f₀ - a * x - b) + α * (f₁ - a * (x + h) - b)| ≤ e := by
    calc
      _ ≤ |(1 - α) * (f₀ - a * x - b)| + |α * (f₁ - a * (x + h) - b)| := abs_add_le _ _
      _ = (1 - α) * |f₀ - a * x - b| + α * |f₁ - a * (x + h) - b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hα₁), abs_of_nonneg hα₀]
      _ ≤ (1 - α) * e + α * e := add_le_add
        (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hα₁))
        (mul_le_mul_of_nonneg_left h₁ hα₀)
      _ = e := by ring
  calc
    _ = |(f - f₀) + ((1 - α) * (f₀ - a * x - b) + α * (f₁ - a * (x + h) - b)) -
        α * (f₁ - f₀)| := by congr 1; ring
    _ ≤ |f - f₀| + |(1 - α) * (f₀ - a * x - b) + α * (f₁ - a * (x + h) - b)| +
        |α * (f₁ - f₀)| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ r + e + r := by
      apply add_le_add (add_le_add hf hc)
      rw [abs_mul, abs_of_nonneg hα₀]
      exact (mul_le_mul_of_nonneg_left hd hα₀).trans (mul_le_of_le_one_left hr hα₁)
    _ = e + 2 * r := by ring

/-- An affine fit on a uniform mesh extends with twice the within-cell oscillation. -/
theorem affine_grid_extension (f : ℝ≥0 → ℝ) {h : ℝ≥0} (hh : 0 < h)
    (N : ℕ) {a b e r : ℝ} (hr : 0 ≤ r)
    (hgrid : ∀ j : ℕ, j ≤ N → |f (j * h) - a * ((j * h : ℝ≥0) : ℝ) - b| ≤ e)
    (hmod : ∀ j : ℕ, j < N → ∀ u : ℝ≥0, u ≤ h →
      |f (j * h + u) - f (j * h)| ≤ r) :
    ∀ t : ℝ≥0, t ≤ N * h → |f t - a * (t : ℝ) - b| ≤ e + 2 * r := by
  intro t ht
  rcases ht.lt_or_eq with hlt | heq
  · let j : ℕ := ⌊t / h⌋₊
    have hjh : (j : ℝ≥0) * h ≤ t := (le_div_iff₀ hh).mp (Nat.floor_le (by positivity))
    have hj : j < N := (Nat.floor_lt (show (0 : ℝ≥0) ≤ t / h from bot_le)).mpr
      ((div_lt_iff₀ hh).mpr hlt)
    let u : ℝ≥0 := t - j * h
    have hu : u ≤ h := by
      apply tsub_le_iff_right.mpr
      have hs := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (t / h))
      simpa only [add_mul, one_mul, add_comm] using hs.le
    have hut : (j : ℝ≥0) * h + u = t := add_tsub_cancel_of_le hjh
    have hhr : (0 : ℝ) < h := by exact_mod_cast hh
    have hα₀ : 0 ≤ (u : ℝ) / h := div_nonneg u.coe_nonneg h.coe_nonneg
    have hα₁ : (u : ℝ) / h ≤ 1 := (div_le_one hhr).mpr (by exact_mod_cast hu)
    have hc := affine_cell_error_le (x := ((j * h : ℝ≥0) : ℝ)) (h := (h : ℝ))
      (α := (u : ℝ) / h) hα₀ hα₁ hr (hgrid j hj.le)
      (by simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, NNReal.coe_add]
        using hgrid (j + 1) hj)
      (by simpa only [hut] using hmod j hj u hu)
      (by simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        using hmod j hj h le_rfl)
    simpa only [div_mul_cancel₀ _ hhr.ne', ← NNReal.coe_add, hut] using hc
  · rw [heq]
    exact (hgrid N le_rfl).trans (by linarith)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The continuous affine error is characterized by actual fits on the time interval. -/
theorem optimalProcessError_le_iff_fit_of_continuous {ω : Ω} (hc : Continuous (B · ω))
    (T : ℝ≥0) (e : ℝ) :
    optimalProcessError B T ω ≤ e ↔
      ∃ a b : ℝ, ∀ t : ℝ≥0, t ≤ T → |B t ω - a * (t : ℝ) - b| ≤ e := by
  unfold optimalProcessError
  rw [optimalTimeError_eq_interval T.coe_nonneg,
    optimalError_le_iff_exists_fit T.coe_nonneg]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, fun t ht => ?_⟩
    have h := hab ⟨t, t.coe_nonneg, ht⟩
    simpa only [intervalPath, ContinuousMap.restrict_apply,
      processPath_apply_of_continuous hc t] using! h
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, fun t => ?_⟩
    have h := hab ⟨t, t.property.1⟩ t.property.2
    simpa only [intervalPath, ContinuousMap.restrict_apply,
      ← processPath_apply_of_continuous hc ⟨t, t.property.1⟩] using! h

omit [MeasurableSpace Ω] in
theorem sqrt_mul_gapKeys_mesh (h : ℝ≥0) (hh : 0 < h) (j : ℕ) (ω : Ω) :
    Real.sqrt (h : ℝ) * gapKeys (fun i => normalizedMeshIncrement B h i ω) j =
      B (j * h) ω - B 0 ω := by
  rw [gapKeys, sum_normalizedMeshIncrement]
  exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr (by exact_mod_cast hh)).ne'

omit [MeasurableSpace Ω] in
/-- Restricting a continuous fit to the mesh cannot increase its optimal error. -/
theorem affErr_mesh_le_processError {ω : Ω} (hc : Continuous (B · ω))
    (h : ℝ≥0) (hh : 0 < h) (k : ℕ) :
    affErr (h : ℝ) k (fun i => normalizedMeshIncrement B h i ω) ≤
      optimalProcessError B (k * h) ω := by
  obtain ⟨a, b, hab⟩ := (optimalProcessError_le_iff_fit_of_continuous hc (k * h)
    (optimalProcessError B (k * h) ω)).mp le_rfl
  apply affErr_le_of_fit (lam := a * h) (c := b - B 0 ω)
  intro j hj
  rw [sqrt_mul_gapKeys_mesh h hh]
  have hjh : (j : ℝ≥0) * h ≤ k * h := mul_le_mul_of_nonneg_right
    (by exact_mod_cast hj) h.coe_nonneg
  have ht := hab (j * h) hjh
  convert ht using 1
  congr 1
  push_cast
  ring

omit [MeasurableSpace Ω] in
/-- The error of a continuous path is bounded by its mesh error and twice the oscillation. -/
theorem processError_le_affErr_mesh_add {ω : Ω} (hc : Continuous (B · ω))
    (h : ℝ≥0) (hh : 0 < h) (k : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hmod : ∀ j : ℕ, j < k → ∀ u : ℝ≥0, u ≤ h →
      |B (j * h + u) ω - B (j * h) ω| ≤ r) :
    optimalProcessError B (k * h) ω ≤
      affErr (h : ℝ) k (fun i => normalizedMeshIncrement B h i ω) + 2 * r := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  obtain ⟨a, b, hab⟩ := exists_fit_of_affErr_lt (lt_add_of_pos_right
    (affErr (h : ℝ) k (fun i => normalizedMeshIncrement B h i ω)) (half_pos hη))
  have he : optimalProcessError B (k * h) ω ≤
      affErr (h : ℝ) k (fun i => normalizedMeshIncrement B h i ω) + η / 2 + 2 * r := by
    apply (optimalProcessError_le_iff_fit_of_continuous hc _ _).mpr
    refine ⟨a / h, b + B 0 ω, affine_grid_extension (fun t => B t ω) hh k hr ?_ hmod⟩
    intro j hj
    have ht := (hab j hj).le
    rw [sqrt_mul_gapKeys_mesh h hh] at ht
    convert ht using 1
    congr 1
    push_cast
    field_simp [(show (h : ℝ) ≠ 0 by exact_mod_cast hh.ne')]
    ring
  linarith

/-- The Gaussian affine error has the law of the same mesh error of any Brownian motion. -/
theorem gaussian_affErr_measure_eq_mesh (hB : IsBrownianReal B μ)
    (h : ℝ≥0) (hh : 0 < h) (k : ℕ) (y : ℝ) :
    (iidLaw gaussPM).real {ζ | affErr (h : ℝ) k ζ ≤ y} =
      μ.real {ω | affErr (h : ℝ) k (fun i => normalizedMeshIncrement B h i ω) ≤ y} := by
  have hid := identDistrib_gaussian_mesh_sequence
    (fun i => (iidSeq_gapCoord gaussPM).measurable i |>.aemeasurable)
    (iidSeq_gapCoord gaussPM).indep
    (fun i => (show (iidLaw gaussPM).map (gapCoord i) = gaussianReal 0 1 from
      Measure.infinitePi_map_eval _ i)) hB.toIsPreBrownianReal h hh.ne'
  have he := (hid.comp (measurable_affErr (h : ℝ) k)).measure_mem_eq
    (s := Iic y) measurableSet_Iic
  exact congrArg ENNReal.toReal he

/-- Continuous Brownian fitting is a lower bound on Gaussian-walk fitting probability. -/
theorem brownian_error_prob_le_walk (hB : IsBrownianReal B μ)
    (h : ℝ≥0) (hh : 0 < h) (k : ℕ) (y : ℝ) :
    μ.real {ω | optimalProcessError B (k * h) ω ≤ y} ≤
      (iidLaw gaussPM).real {ζ | affErr (h : ℝ) k ζ ≤ y} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [gaussian_affErr_measure_eq_mesh hB h hh]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hB.cont] with ω hc
  intro hω
  exact (affErr_mesh_le_processError hc h hh k).trans hω

/-- The mesh-to-continuum comparison with an explicit within-cell failure probability. -/
theorem gaussian_walk_prob_le_brownian_error (hB : IsBrownianReal B μ)
    (h : ℝ≥0) (hh : 0 < h) (n k : ℕ) (hkn : k ≤ n) (y r : ℝ) (hr : 0 ≤ r) :
    (iidLaw gaussPM).real {ζ | affErr (h : ℝ) k ζ ≤ y} ≤
      μ.real {ω | optimalProcessError B (k * h) ω ≤ y + 2 * r} +
        n * (2 * Real.exp (-(r ^ 2 / (2 * (h : ℝ))))) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [gaussian_affErr_measure_eq_mesh hB h hh]
  have he : μ.real {ω | affErr (h : ℝ) k (fun i => normalizedMeshIncrement B h i ω) ≤ y} ≤
      μ.real ({ω | optimalProcessError B (k * h) ω ≤ y + 2 * r} ∪
        brownianGridOscillationEvent B h n r) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hB.cont] with ω hc
    intro hω
    by_cases hbad : ω ∈ brownianGridOscillationEvent B h n r
    · exact Or.inr hbad
    apply Or.inl
    have hmod : ∀ j : ℕ, j < k → ∀ u : ℝ≥0, u ≤ h →
        |B (j * h + u) ω - B (j * h) ω| ≤ r := by
      intro j hj u hu
      by_contra hn
      apply hbad
      simp only [brownianGridOscillationEvent, mem_iUnion, Finset.mem_range, mem_ofPred_eq]
      exact ⟨j, hj.trans_le hkn, u, hu, lt_of_not_ge hn⟩
    exact (processError_le_affErr_mesh_add hc h hh k hr hmod).trans
      (add_le_add hω le_rfl)
  exact he.trans ((measureReal_union_le _ _).trans (add_le_add le_rfl
    (measureReal_brownianGridOscillationEvent_le hB hh n hr)))

/-- The upper comparison required by `LifetimeSide`, for any Brownian realization. -/
theorem brownian_walk_le (hB : IsBrownianReal B μ)
    (v : ℝ) (hv : 0 < v) (n k : ℕ) (_hk : 1 ≤ k) (hkn : k ≤ n)
    (y ρ : ℝ) (hy : 0 < y) (hρ : 0 < ρ) :
    (iidLaw gaussPM).real {ζ | affErr v k ζ ≤ y} ≤
      (μ.map (optimalUnitLifetime B)).real (Ici (v * k / (y + 2 * Real.sqrt v * ρ) ^ 2)) +
        2 * n * Real.exp (-ρ ^ 2 / 2) := by
  let h : ℝ≥0 := ⟨v, hv.le⟩
  have hh : 0 < h := hv
  have hr : 0 ≤ Real.sqrt v * ρ := mul_nonneg (Real.sqrt_nonneg _) hρ.le
  have ha : 0 < y + 2 * (Real.sqrt v * ρ) := by positivity
  have hp := gaussian_walk_prob_le_brownian_error hB h hh n k hkn y (Real.sqrt v * ρ) hr
  rw [brownian_error_le_eq_lifetime_tail hB (k * h) ha] at hp
  have hex : (Real.sqrt v * ρ) ^ 2 / (2 * v) = ρ ^ 2 / 2 := by
    rw [mul_pow, Real.sq_sqrt hv.le]
    field_simp
  have hhval : (h : ℝ) = v := rfl
  simp only [NNReal.coe_mul, NNReal.coe_natCast, hhval, hex] at hp
  simpa only [mul_comm (k : ℝ) v, ← mul_assoc, mul_comm (n : ℝ) 2, neg_div] using hp

/-- The lower comparison required by `LifetimeSide`; restriction already gives the stronger bound. -/
theorem brownian_walk_ge (hB : IsBrownianReal B μ)
    (v : ℝ) (hv : 0 < v) (n k : ℕ) (_hk : 1 ≤ k) (_hkn : k ≤ n)
    (y ρ : ℝ) (hρ : 0 < ρ) (hy : 2 * Real.sqrt v * ρ < y) :
    (μ.map (optimalUnitLifetime B)).real (Ici (v * k / (y - 2 * Real.sqrt v * ρ) ^ 2)) -
        2 * n * Real.exp (-ρ ^ 2 / 2) ≤
      (iidLaw gaussPM).real {ζ | affErr v k ζ ≤ y} := by
  let h : ℝ≥0 := ⟨v, hv.le⟩
  have hh : 0 < h := hv
  have ha : 0 < y - 2 * Real.sqrt v * ρ := sub_pos.mpr hy
  have hp := brownian_error_prob_le_walk hB h hh k (y - 2 * Real.sqrt v * ρ)
  rw [brownian_error_le_eq_lifetime_tail hB (k * h) ha] at hp
  have htail : (μ.map (optimalUnitLifetime B)).real
      (Ici (v * k / (y - 2 * Real.sqrt v * ρ) ^ 2)) ≤
      (iidLaw gaussPM).real {ζ | affErr v k ζ ≤ y - 2 * Real.sqrt v * ρ} := by
    have hhval : (h : ℝ) = v := rfl
    simpa only [NNReal.coe_mul, NNReal.coe_natCast, hhval, mul_comm (k : ℝ) v]
      using hp
  have hm : (iidLaw gaussPM).real {ζ | affErr v k ζ ≤ y - 2 * Real.sqrt v * ρ} ≤
      (iidLaw gaussPM).real {ζ | affErr v k ζ ≤ y} := by
    refine measureReal_mono ?_
    intro ζ hζ
    change affErr v k ζ ≤ y - 2 * Real.sqrt v * ρ at hζ
    exact hζ.trans (sub_le_self y (show 0 ≤ 2 * Real.sqrt v * ρ by positivity))
  have he : 0 ≤ 2 * (n : ℝ) * Real.exp (-ρ ^ 2 / 2) := by positivity
  exact (sub_le_self _ he).trans (htail.trans hm)

end

end PGM
