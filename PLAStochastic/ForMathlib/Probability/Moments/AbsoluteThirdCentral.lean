import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# Absolute third central moments

This module formalizes the first identity in the main paper's appendix lemma
"Absolute third moment identities" for any real random variable in `L³` on a
probability space. Integrability of every term is derived from this hypothesis;
the asserted expectation identity is not an input assumption.

The first identity does not require the random variable to be nonnegative.
Brownian stopping-time distributions and their evaluated raw moments are not
identified by this generic theorem.
-/

open MeasureTheory
open scoped ENNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- A finite `Lⁿ` moment implies integrability of the signed natural power. -/
theorem integrable_pow_of_memLp {n : ℕ} (hn : n ≠ 0) (hX : MemLp X n μ) :
    Integrable (fun ω => X ω ^ n) μ := by
  apply (integrable_norm_iff (hX.aestronglyMeasurable.pow n)).mp
  simpa only [Pi.pow_apply, norm_pow] using hX.integrable_norm_pow hn

/-- The real identity underlying the absolute third moment decomposition. -/
theorem abs_cube_eq_cube_add_lower (x : ℝ) :
    |x| ^ 3 = x ^ 3 + 2 * max (-x) 0 ^ 3 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hx' : x ≤ 0 := le_of_lt (lt_of_not_ge hx)
    rw [abs_of_nonpos hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

section Probability

variable [IsProbabilityMeasure μ]

/-- Expanding the centered cube commutes with expectation because all required
raw powers, derived from `L³`, are integrable. -/
theorem integral_cube_sub (hX : MemLp X 3 μ) (a : ℝ) :
    (∫ ω, (X ω - a) ^ 3 ∂μ) =
      (∫ ω, X ω ^ 3 ∂μ) - 3 * a * (∫ ω, X ω ^ 2 ∂μ) +
        3 * a ^ 2 * (∫ ω, X ω ∂μ) - a ^ 3 := by
  have h₁ : Integrable X μ := hX.integrable (by norm_num)
  have h₂ : Integrable (fun ω => X ω ^ 2) μ :=
    integrable_pow_of_memLp (by decide) (hX.mono_exponent (by norm_num))
  have h₃ : Integrable (fun ω => X ω ^ 3) μ :=
    integrable_pow_of_memLp (by decide) hX
  have heq : (fun ω => (X ω - a) ^ 3) =
      (fun ω => X ω ^ 3 - (3 * a) * X ω ^ 2 + (3 * a ^ 2) * X ω - a ^ 3) := by
    funext ω
    ring
  have hsub : Integrable (fun ω => X ω ^ 3 - (3 * a) * X ω ^ 2) μ :=
    h₃.sub (h₂.const_mul (3 * a))
  have hsum : Integrable
      (fun ω => X ω ^ 3 - (3 * a) * X ω ^ 2 + (3 * a ^ 2) * X ω) μ :=
    hsub.add (h₁.const_mul (3 * a ^ 2))
  rw [heq, integral_sub hsum (integrable_const (a ^ 3)),
    integral_add hsub (h₁.const_mul (3 * a ^ 2)),
    integral_sub h₃ (h₂.const_mul (3 * a))]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]

/-- At the true mean, the signed third central moment has the paper's raw-moment
expansion. No separate raw-moment integrability assumptions are needed. -/
theorem integral_centered_cube (hX : MemLp X 3 μ) :
    (∫ ω, (X ω - ∫ z, X z ∂μ) ^ 3 ∂μ) =
      (∫ ω, X ω ^ 3 ∂μ) - 3 * (∫ ω, X ω ∂μ) * (∫ ω, X ω ^ 2 ∂μ) +
        2 * (∫ ω, X ω ∂μ) ^ 3 := by
  rw [integral_cube_sub hX]
  ring

/-- Both sides of the absolute-third-moment identity are ordinary finite
Bochner integrals, as follows from `L³` and stability under constants and max. -/
theorem integrable_third_central_terms (hX : MemLp X 3 μ) (a : ℝ) :
    Integrable (fun ω => |X ω - a| ^ 3) μ ∧
      Integrable (fun ω => (X ω - a) ^ 3) μ ∧
      Integrable (fun ω => max (a - X ω) 0 ^ 3) μ := by
  have hc : MemLp (fun ω => X ω - a) 3 μ := hX.sub (memLp_const a)
  have hl : MemLp (fun ω => max (a - X ω) 0) 3 μ :=
    ((memLp_const a).sub hX).sup (memLp_const 0)
  refine ⟨?_, integrable_pow_of_memLp (by decide) hc,
    integrable_pow_of_memLp (by decide) hl⟩
  simpa only [Real.norm_eq_abs] using hc.integrable_norm_pow (by decide : (3 : ℕ) ≠ 0)

/-- The unstandardized first identity of the paper's appendix lemma, including
the raw-moment expansion of the signed central moment. -/
theorem integral_absolute_third_central (hX : MemLp X 3 μ) :
    (∫ ω, |X ω - ∫ z, X z ∂μ| ^ 3 ∂μ) =
      (∫ ω, X ω ^ 3 ∂μ) - 3 * (∫ ω, X ω ∂μ) * (∫ ω, X ω ^ 2 ∂μ) +
        2 * (∫ ω, X ω ∂μ) ^ 3 +
          2 * (∫ ω, max ((∫ z, X z ∂μ) - X ω) 0 ^ 3 ∂μ) := by
  obtain ⟨_, hc, hl⟩ := integrable_third_central_terms hX (∫ z, X z ∂μ)
  have heq : (fun ω => |X ω - ∫ z, X z ∂μ| ^ 3) =
      (fun ω => (X ω - ∫ z, X z ∂μ) ^ 3 +
        2 * max ((∫ z, X z ∂μ) - X ω) 0 ^ 3) := by
    funext ω
    simpa only [neg_sub] using abs_cube_eq_cube_add_lower (X ω - ∫ z, X z ∂μ)
  rw [heq, integral_add hc (hl.const_mul 2), integral_const_mul,
    integral_centered_cube hX]

/-- Dividing by a positive variance scale gives the paper's standardized
identity. The caller identifies `V` with the model's positive variance. -/
theorem standardized_absolute_third_central (hX : MemLp X 3 μ) {V : ℝ} (hV : 0 < V) :
    (∫ ω, |X ω - ∫ z, X z ∂μ| ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) =
      ((∫ ω, X ω ^ 3 ∂μ) - 3 * (∫ ω, X ω ∂μ) * (∫ ω, X ω ^ 2 ∂μ) +
        2 * (∫ ω, X ω ∂μ) ^ 3) / V ^ (3 / 2 : ℝ) +
          2 * (∫ ω, max ((∫ z, X z ∂μ) - X ω) 0 ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) := by
  have hden : V ^ (3 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hV _)
  rw [← add_div]
  apply (div_eq_div_iff hden hden).2
  rw [integral_absolute_third_central hX]

end Probability

end BrownianAffine
