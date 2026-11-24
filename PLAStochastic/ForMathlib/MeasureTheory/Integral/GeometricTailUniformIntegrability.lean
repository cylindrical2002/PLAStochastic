import PLAStochastic.ForMathlib.MeasureTheory.Integral.GeometricTailIntegrability
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniform integrability from one common geometric tail

A common geometric ratio controls a whole family, rather than just making each
member separately integrable. The resulting Vitali theorem transfers almost
sure convergence of the original extended lifetimes to convergence of means.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem geometric_second_moment_sum_finite {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    (∑' n : ℕ, ENNReal.ofReal ((16 * ((n : ℝ) + 1)) ^ 2) *
      ENNReal.ofReal (q ^ n)) < ∞ := by
  have hqn : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq₀] using hq₁
  have h₂ := (summable_pow_mul_geometric_of_norm_lt_one 2 hqn).mul_left (256 : ℝ)
  have h₁ := (summable_pow_mul_geometric_of_norm_lt_one 1 hqn).mul_left (512 : ℝ)
  have h₀ := (summable_geometric_of_lt_one hq₀ hq₁).mul_left (256 : ℝ)
  have hs : Summable (fun n : ℕ => (16 * ((n : ℝ) + 1)) ^ 2 * q ^ n) := by
    have heq : (fun n : ℕ => (16 * ((n : ℝ) + 1)) ^ 2 * q ^ n) =
        (fun n : ℕ => 256 * ((n : ℝ) ^ 2 * q ^ n)) +
          (fun n : ℕ => 512 * ((n : ℝ) ^ 1 * q ^ n)) +
          (fun n : ℕ => 256 * q ^ n) := by
      ext n
      simp only [Pi.add_apply, pow_one]
      ring
    rw [heq]
    exact (h₂.add h₁).add h₀
  simpa only [← ENNReal.ofReal_mul (sq_nonneg _)] using hs.tsum_ofReal_lt_top

theorem uniformIntegrable_of_uniform_second_moment [IsFiniteMeasure μ]
    {f : ι → Ω → ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ i, (∫⁻ ω, ENNReal.ofReal ((f i ω) ^ 2) ∂μ) ≤ ENNReal.ofReal M) :
    UniformIntegrable f 1 μ := by
  apply uniformIntegrable_of le_rfl (by norm_num) hf
  intro ε hε
  let C : ℝ≥0 := ⟨(M + 1) / ε, by positivity⟩
  have hC : 0 < (C : ℝ) := div_pos (by linarith) hε
  refine ⟨C, fun i => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    (∫⁻ ω, ‖{ω | C ≤ ‖f i ω‖₊}.indicator (f i) ω‖ₑ ∂μ) ≤
        ∫⁻ ω, ENNReal.ofReal ((C : ℝ)⁻¹) * ENNReal.ofReal ((f i ω) ^ 2) ∂μ := by
      apply lintegral_mono
      intro ω
      change ‖(if C ≤ ‖f i ω‖₊ then f i ω else 0)‖ₑ ≤
        ENNReal.ofReal ((C : ℝ)⁻¹) * ENNReal.ofReal ((f i ω) ^ 2)
      split_ifs with hω
      · rw [Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hC.le)]
        apply ENNReal.ofReal_le_ofReal
        have hω' : (C : ℝ) ≤ |f i ω| := by exact_mod_cast hω
        have hsq : (C : ℝ) * |f i ω| ≤ (f i ω) ^ 2 := by
          nlinarith [sq_abs (f i ω), mul_le_mul_of_nonneg_right hω' (abs_nonneg (f i ω))]
        rw [← div_eq_inv_mul, le_div_iff₀ hC]
        nlinarith
      · rw [enorm_zero]
        exact zero_le
    _ = ENNReal.ofReal ((C : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal ((f i ω) ^ 2) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((C : ℝ)⁻¹) * ENNReal.ofReal M := mul_le_mul_right (hb i) _
    _ = ENNReal.ofReal ((C : ℝ)⁻¹ * M) := (ENNReal.ofReal_mul (inv_nonneg.mpr hC.le)).symm
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      rw [← div_eq_inv_mul, div_le_iff₀ hC]
      change M ≤ ε * ((M + 1) / ε)
      rw [mul_div_cancel₀ _ hε.ne']
      linarith

/-- A common tail estimate supplies a uniform second-moment bound, with no assumed moments. -/
theorem uniformIntegrable_toReal_of_geometricTail16 [IsFiniteMeasure μ]
    {X : ι → Ω → ℝ≥0∞} {q : ℝ} (hX : ∀ i, AEMeasurable (X i) μ)
    (ht : ∀ i, GeometricTail16 μ (X i) q) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    UniformIntegrable (fun i ω => (X i ω).toReal) 1 μ := by
  let S : ℝ≥0∞ := ∑' n : ℕ, ENNReal.ofReal ((16 * ((n : ℝ) + 1)) ^ 2) *
    ENNReal.ofReal (q ^ n)
  have hS : S ≠ ∞ := (geometric_second_moment_sum_finite hq₀ hq₁).ne
  apply uniformIntegrable_of_uniform_second_moment
    (fun i => (hX i).ennreal_toReal.aestronglyMeasurable) (M := S.toReal) ENNReal.toReal_nonneg
  intro i
  rw [ENNReal.ofReal_toReal hS]
  apply (ht i).lintegral_toReal_le (hX i) (fun y => ENNReal.ofReal (y ^ 2))
  intro a ha b _ hab
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ ha hab 2

/-- Vitali applied to extended nonnegative lifetimes; only finiteness of the limit is needed. -/
theorem tendsto_integral_toReal_of_geometricTail16 [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ≥0∞} {Y : Ω → ℝ≥0∞} {q : ℝ}
    (hX : ∀ n, AEMeasurable (X n) μ) (ht : ∀ n, GeometricTail16 μ (X n) q)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hY : ∀ᵐ ω ∂μ, Y ω ≠ ∞)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Integrable (fun ω => (Y ω).toReal) μ ∧
      Tendsto (fun n => ∫ ω, (X n ω).toReal ∂μ) atTop
        (𝓝 (∫ ω, (Y ω).toReal ∂μ)) := by
  have hu := uniformIntegrable_toReal_of_geometricTail16 hX ht hq₀ hq₁
  have hc : ∀ᵐ ω ∂μ, Tendsto (fun n => (X n ω).toReal) atTop (𝓝 (Y ω).toReal) := by
    filter_upwards [hY, hconv] with ω hω hcω
    exact (ENNReal.continuousAt_toReal hω).tendsto.comp hcω
  have hy := hu.integrable_of_ae_tendsto hc
  refine ⟨hy, tendsto_integral_of_L1' _ hy.aestronglyMeasurable
    (Eventually.of_forall fun n => (hu.memLp n).integrable le_rfl) ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by norm_num)
    (fun n => (hX n).ennreal_toReal.aestronglyMeasurable) (hu.memLp_of_ae_tendsto hc) hu.2.1 hc

end BrownianAffine
