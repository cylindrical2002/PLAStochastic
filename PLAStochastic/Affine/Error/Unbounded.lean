import PLAStochastic.Affine.Lifetime.GaussianBlocks
import PLAStochastic.Affine.Error.BrownianScaling

/-!
# Brownian fitting errors are not essentially bounded

One Gaussian midpoint deviation suffices. This gives nondegeneracy without
requiring a separate Brownian small-ball theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem optimalTimeError_bounds_midpoint (f : C(ℝ, ℝ)) {r : ℝ}
    (h : optimalTimeError f 16 ≤ r) : |(f 8 - (f 0 + f 16) / 2) / 2| ≤ r := by
  have he : optimalTimeError f 16 = optimalError (intervalPath f 16) :=
    optimalTimeError_eq_interval (by norm_num) f
  rw [he] at h
  obtain ⟨a, b, hab⟩ := (optimalError_le_iff_exists_fit (by norm_num)
    (intervalPath f 16)).mp h
  have h₀ := hab ⟨0, by norm_num⟩
  have hₘ := hab ⟨8, by norm_num⟩
  have h₁ := hab ⟨16, by norm_num⟩
  change |f 0 - a * 0 - b| ≤ r at h₀
  change |f 8 - a * 8 - b| ≤ r at hₘ
  change |f 16 - a * 16 - b| ≤ r at h₁
  rw [abs_le] at h₀ hₘ h₁ ⊢
  constructor <;> linarith

theorem optimalProcessError_sixteen_not_bounded (hB : IsBrownianReal B μ) (r : ℝ) :
    ¬ ∀ᵐ ω ∂μ, optimalProcessError B 16 ω ≤ r := by
  intro hbound
  have hblock : ∀ᵐ ω ∂μ, gaussianBlock B 0 ω ≤ r := by
    filter_upwards [hbound, processPath_represents_brownian hB] with ω hω hp
    have hm := optimalTimeError_bounds_midpoint (processPath B ω) hω
    have h₀ := hp 0
    have hₘ := hp 8
    have h₁ := hp 16
    norm_num only [NNReal.coe_zero, NNReal.coe_ofNat] at h₀ hₘ h₁
    rw [h₀, hₘ, h₁] at hm
    simpa only [gaussianBlock, Nat.cast_zero, mul_zero, zero_add] using
      (le_abs_self _).trans hm
  have hz : μ {ω | r < gaussianBlock B 0 ω} = 0 := by
    simpa only [ae_iff, not_le] using hblock
  have hlaw := (gaussianBlock_hasLaw hB.toIsPreBrownianReal 0).measure_eq
    (p := fun x => r < x) measurableSet_Ioi
  rw [hz] at hlaw
  have hv := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)) hlaw.symm
  change volume (Ioi r) = 0 at hv
  rw [Real.volume_Ioi] at hv
  exact ENNReal.top_ne_zero hv

/-- At every positive duration, every finite error threshold can be exceeded
with positive probability. The assertion is expressed without an atomlessness hypothesis. -/
theorem optimalProcessError_not_bounded (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : T ≠ 0) (r : ℝ) :
    ¬ ∀ᵐ ω ∂μ, optimalProcessError B T ω ≤ r := by
  intro hbound
  let c : ℝ≥0 := T / 16
  have hc : c ≠ 0 := div_ne_zero hT (by norm_num)
  have hct : c * 16 = T := by simp [c]
  apply optimalProcessError_sixteen_not_bounded (isBrownianReal_normalized hB hc)
    ((Real.sqrt (c : ℝ))⁻¹ * r)
  filter_upwards [hbound, optimalProcessError_normalized_ae hB hc 16] with ω hω he
  rw [he, hct]
  exact mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem anchoredProcessError_not_bounded (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : T ≠ 0) (r : ℝ) :
    ¬ ∀ᵐ ω ∂μ, anchoredProcessError B T ω ≤ r := by
  intro hbound
  apply optimalProcessError_not_bounded hB hT r
  filter_upwards [hbound] with ω hω
  exact (optimalTimeError_le_anchoredTimeError (processPath B ω) T).trans hω

end BrownianAffine
