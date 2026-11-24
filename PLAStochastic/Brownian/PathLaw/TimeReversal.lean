import PLAStochastic.Brownian.PathLaw.BridgeDecomposition

/-!
# Brownian reversal on a finite interval, extended to all nonnegative times

`B(max T t) - B(T-t)` reverses increments on `[0,T]` and then continues along
the original future increments. Truncated subtraction makes the extension
continuous. Joint Gaussianity, centering, and the actual covariance identify
the complete extended process as Brownian motion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def timeReversedProcess (B : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ω : Ω) : ℝ :=
  B (max T t) ω - B (T - t) ω

omit [MeasurableSpace Ω] in
theorem timeReversedProcess_of_le (B : ℝ≥0 → Ω → ℝ) {T t : ℝ≥0}
    (ht : t ≤ T) (ω : Ω) : timeReversedProcess B T t ω = B T ω - B (T - t) ω := by
  simp only [timeReversedProcess, max_eq_left ht]

theorem timeReversedProcess_isGaussianProcess (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    IsGaussianProcess (timeReversedProcess B T) μ := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro t
  refine ⟨{max T t, T - t},
    { toFun := fun x => x ⟨max T t, by simp⟩ - x ⟨T - t, by simp⟩
      map_add' := by intro x y; simp only [Pi.add_apply]; ring
      map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, ?_⟩
  intro ω
  rfl

theorem timeReversedProcess_integral (hB : IsPreBrownianReal B μ) (T t : ℝ≥0) :
    (∫ ω, timeReversedProcess B T t ω ∂μ) = 0 := by
  unfold timeReversedProcess
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
    hB.integral_eval, hB.integral_eval, sub_self]

theorem timeReversedProcess_covariance (hB : IsPreBrownianReal B μ)
    (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) :
    covariance (timeReversedProcess B T s) (timeReversedProcess B T t) μ = (s : ℝ) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have h₁ := (hB.isGaussianProcess.hasGaussianLaw_eval (max T s)).memLp_two
  have h₂ := (hB.isGaussianProcess.hasGaussianLaw_eval (T - s)).memLp_two
  have h₃ := (hB.isGaussianProcess.hasGaussianLaw_eval (max T t)).memLp_two
  have h₄ := (hB.isGaussianProcess.hasGaussianLaw_eval (T - t)).memLp_two
  have hmax : max T s ≤ max T t := max_le_max_left T hst
  have hcross₁ : T - t ≤ max T s := (tsub_le_self).trans (le_max_left _ _)
  have hcross₂ : T - s ≤ max T t := (tsub_le_self).trans (le_max_left _ _)
  have hsub : T - t ≤ T - s := tsub_le_tsub_left hst T
  have he : ((max T s : ℝ≥0) : ℝ) - ((T - s : ℝ≥0) : ℝ) = (s : ℝ) := by
    rcases le_total s T with hs | hs
    · rw [max_eq_left hs, NNReal.coe_sub hs]
      ring
    · rw [max_eq_right hs, tsub_eq_zero_of_le hs, NNReal.coe_zero, sub_zero]
  unfold timeReversedProcess
  rw [covariance_fun_sub_fun_sub h₁ h₂ h₃ h₄]
  simp only [hB.covariance_eval, min_eq_left hmax, min_eq_right hcross₁,
    min_eq_left hcross₂, min_eq_right hsub]
  linarith

theorem isPreBrownianReal_timeReversal (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    IsPreBrownianReal (timeReversedProcess B T) μ :=
  (timeReversedProcess_isGaussianProcess hB T).isPreBrownianReal_of_covariance
    (timeReversedProcess_integral hB T) (fun _ _ hst => timeReversedProcess_covariance hB T hst)

theorem isBrownianReal_timeReversal (hB : IsBrownianReal B μ) (T : ℝ≥0) :
    IsBrownianReal (timeReversedProcess B T) μ := by
  refine ⟨isPreBrownianReal_timeReversal hB.toIsPreBrownianReal T, ?_⟩
  filter_upwards [hB.cont] with ω hω
  unfold timeReversedProcess
  fun_prop

end BrownianAffine
