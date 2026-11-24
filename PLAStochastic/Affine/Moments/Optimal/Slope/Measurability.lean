import PLAStochastic.Affine.Moments.Optimal.Slope.Coarea
import PLAStochastic.Affine.Process.PathLaw.PathSpace
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Joint measurability and drift covariance of the slope integrand

The actual range is jointly Lipschitz in the uniform path topology and slope.
Its derivative is therefore jointly Borel measurable by the parameterized
derivative theorem. Drift translates the slope argument, giving the precise
zero-slope weight used in Gaussian endpoint integration.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace BrownianAffine

theorem slopeRange_le_add_path_dist (g h : Path 1) (a : ℝ) :
    slopeRange g a ≤ slopeRange h a + 2 * dist g h := by
  apply (slopeRange_le_iff g a _).mpr
  intro s t
  have hs : |g s - h s| ≤ dist g h := by
    simpa only [Real.dist_eq] using! ContinuousMap.dist_apply_le_dist (f := g) (g := h) s
  have ht : |g t - h t| ≤ dist g h := by
    simpa only [Real.dist_eq] using! ContinuousMap.dist_apply_le_dist (f := g) (g := h) t
  have hb := slopeResidual_sub_le_range h a s t
  have hs' := (abs_le.mp hs).2
  have ht' := (abs_le.mp ht).1
  unfold slopeResidual at *
  linarith

theorem slopeRange_le_add_joint_dist (g h : Path 1) (a b : ℝ) :
    slopeRange g a ≤ slopeRange h b + 2 * dist g h + |a - b| := by
  have h₁ := slopeRange_le_add_path_dist g h a
  have h₂ := slopeRange_le_add_abs h a b
  linarith

/-- The product uses the standard maximum metric; constant three is sufficient. -/
theorem slopeRange_joint_lipschitz :
    LipschitzWith 3 (fun p : Path 1 × ℝ => slopeRange p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hp : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have ha : |p.2 - q.2| ≤ dist p q := by
    rw [Prod.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have h₁ := slopeRange_le_add_joint_dist p.1 q.1 p.2 q.2
  have h₂ := slopeRange_le_add_joint_dist q.1 p.1 q.2 p.2
  rw [dist_comm q.1 p.1, abs_sub_comm q.2 p.2] at h₂
  simp only [Real.dist_eq, NNReal.coe_ofNat]
  rw [abs_le]
  constructor <;> linarith

theorem continuous_slopeRange_joint :
    Continuous (fun p : Path 1 × ℝ => slopeRange p.1 p.2) :=
  slopeRange_joint_lipschitz.continuous

theorem measurable_slopeRange_joint :
    Measurable (fun p : Path 1 × ℝ => slopeRange p.1 p.2) :=
  continuous_slopeRange_joint.measurable

theorem measurable_slopeRange_deriv_joint :
    Measurable (fun p : Path 1 × ℝ => deriv (slopeRange p.1) p.2) :=
  measurable_deriv_with_param continuous_slopeRange_joint

/-- The manuscript's nonnegative path functional evaluated at zero slope. -/
def slopeWeight (q : ℝ) (g : Path 1) : ℝ :=
  |deriv (slopeRange g) 0| / slopeRange g 0 ^ (2 * q + 1)

def slopeWeightENNReal (q : ℝ) (g : Path 1) : ℝ≥0∞ := ENNReal.ofReal (slopeWeight q g)

theorem slopeWeight_nonnegative (q : ℝ) (g : Path 1) : 0 ≤ slopeWeight q g :=
  div_nonneg (abs_nonneg _) (Real.rpow_nonneg (slopeRange_nonnegative g 0) _)

theorem measurable_slopeWeight (q : ℝ) : Measurable (slopeWeight q) := by
  have hd : Measurable (fun g : Path 1 => deriv (slopeRange g) 0) :=
    measurable_slopeRange_deriv_joint.comp (measurable_id.prodMk measurable_const)
  have hr : Measurable (fun g : Path 1 => slopeRange g 0) :=
    measurable_slopeRange_joint.comp (measurable_id.prodMk measurable_const)
  simpa only [slopeWeight, Real.norm_eq_abs, Pi.div_apply, Pi.pow_apply] using!
    hd.norm.div (hr.pow_const (2 * q + 1))

theorem measurable_slopeWeightENNReal (q : ℝ) : Measurable (slopeWeightENNReal q) :=
  (measurable_slopeWeight q).ennreal_ofReal

theorem slopeResidual_add_drift (g : Path 1) (y a : ℝ) (t : RangeTime) :
    slopeResidual (g + y • timePath 1) a t = slopeResidual g (a - y) t := by
  simp only [slopeResidual, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul, timePath, ContinuousMap.coe_mk]
  ring

theorem slopeUpper_add_drift (g : Path 1) (y a : ℝ) :
    slopeUpper (g + y • timePath 1) a = slopeUpper g (a - y) := by
  have hf := funext (slopeResidual_add_drift g y a)
  unfold slopeUpper
  rw [hf]

theorem slopeLower_add_drift (g : Path 1) (y a : ℝ) :
    slopeLower (g + y • timePath 1) a = slopeLower g (a - y) := by
  have hf := funext (slopeResidual_add_drift g y a)
  unfold slopeLower
  rw [hf]

theorem slopeRange_add_drift (g : Path 1) (y a : ℝ) :
    slopeRange (g + y • timePath 1) a = slopeRange g (a - y) := by
  unfold slopeRange
  rw [slopeUpper_add_drift g y a, slopeLower_add_drift g y a]

theorem slopeRange_deriv_add_drift (g : Path 1) (y a : ℝ) :
    deriv (slopeRange (g + y • timePath 1)) a = deriv (slopeRange g) (a - y) := by
  rw [funext (slopeRange_add_drift g y), deriv_comp_sub_const]

theorem slopeWeight_add_drift (q : ℝ) (g : Path 1) (y : ℝ) :
    slopeWeight q (g + y • timePath 1) =
      |deriv (slopeRange g) (-y)| / slopeRange g (-y) ^ (2 * q + 1) := by
  simp only [slopeWeight, slopeRange_deriv_add_drift, slopeRange_add_drift, zero_sub]

theorem integral_slopeWeight_add_drift (q : ℝ) (g : Path 1) :
    (∫ y : ℝ, slopeWeight q (g + y • timePath 1)) =
      ∫ a, |deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1) := by
  simp_rw [slopeWeight_add_drift]
  exact integral_neg_eq_self
    (fun a : ℝ => |deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1)) volume

theorem lintegral_slopeWeight_add_drift (q : ℝ) (g : Path 1) :
    (∫⁻ y : ℝ, slopeWeightENNReal q (g + y • timePath 1)) =
      ∫⁻ a, ENNReal.ofReal (|deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1)) := by
  simp only [slopeWeightENNReal, slopeWeight_add_drift]
  exact lintegral_neg_eq_self (μ := volume)
    (fun a : ℝ => ENNReal.ofReal (|deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1)))

/-- Coarea for the drifted zero-slope functional, including its integrability. -/
theorem slopeWeight_drift_coarea (g : Path 1) (hρ : 0 < slopeMinimum g)
    {q : ℝ} (hq : 0 < q) :
    Integrable (fun y : ℝ => slopeWeight q (g + y • timePath 1)) ∧
      optimalError g ^ (-2 * q) = (2 : ℝ) ^ (2 * q) * q *
        ∫ y : ℝ, slopeWeight q (g + y • timePath 1) := by
  have h := slopeRange_coarea_power_of_minimum_pos g hρ hq
  constructor
  · simpa only [slopeWeight_add_drift] using! h.1.comp_neg
  · rw [integral_slopeWeight_add_drift]
    exact h.2

/-- The extended nonnegative form can be used under a further expectation without
assuming any prior integrability of the random-path expression. -/
theorem slopeWeight_drift_lintegral (g : Path 1) (hρ : 0 < slopeMinimum g)
    {q : ℝ} (hq : 0 < q) :
    ENNReal.ofReal (optimalError g ^ (-2 * q)) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * q) * q) *
        ∫⁻ y : ℝ, slopeWeightENNReal q (g + y • timePath 1) := by
  have h := slopeWeight_drift_coarea g hρ hq
  rw [h.2, ENNReal.ofReal_mul (by positivity)]
  congr 1
  exact ofReal_integral_eq_lintegral_ofReal h.1
    (Eventually.of_forall fun y => slopeWeight_nonnegative q (g + y • timePath 1))

end BrownianAffine
