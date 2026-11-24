import PLAStochastic.Swing.Gaussian.Tail.ExcessMoments

/-! # Exact one-step quadratic drift for the actual Gaussian walk -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The strip potential used to bound the actual exit time. -/
def stripPotential (R u : ℝ) : ℝ := u*(R-u)

theorem stripPotential_increment (R u a z : ℝ) :
    stripPotential R (u+a+z) - stripPotential R u =
      a*(R-2*u)-a^2 + (R-2*u-2*a)*z-z^2 := by
  unfold stripPotential
  ring

theorem stripPotential_nonneg {R u : ℝ} (hu : u ∈ Icc 0 R) : 0 ≤ stripPotential R u :=
  mul_nonneg hu.1 (sub_nonneg.mpr hu.2)

/-- At either exit boundary the negative potential has exactly the overshoot form. -/
theorem stripPotential_lower_exit (R O : ℝ) : stripPotential R (-O) = -R*O-O^2 := by
  unfold stripPotential
  ring

theorem stripPotential_upper_exit (R O : ℝ) : stripPotential R (R+O) = -R*O-O^2 := by
  unfold stripPotential
  ring

/-- The original standard Gaussian has actual second moment one. -/
theorem integral_sq_standardGaussian : (∫ z : ℝ, z^2 ∂gaussianReal 0 1) = 1 := by
  have hv := variance_of_integral_eq_zero (X := (id : ℝ → ℝ))
    (μ := gaussianReal 0 1) measurable_id.aemeasurable (by simpa only [id_eq] using integral_id_gaussianReal (μ := 0) (v := 1))
  simpa only [variance_id_gaussianReal, NNReal.coe_one, id_eq] using hv.symm

/-- All terms in the one-step potential are truly integrable under the Gaussian increment. -/
theorem integrable_stripPotential_increment (R u a : ℝ) :
    Integrable (fun z => stripPotential R (u+a+z)-stripPotential R u) (gaussianReal 0 1) := by
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hz2 : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  simp_rw [stripPotential_increment]
  exact ((integrable_const _).add (hz.const_mul _)).sub hz2

/-- Exact conditional one-step mean for a fixed current position u. -/
theorem integral_stripPotential_increment (R u a : ℝ) :
    (∫ z, stripPotential R (u+a+z)-stripPotential R u ∂gaussianReal 0 1) =
      a*(R-2*u)-1-a^2 := by
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hz2 : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  simp_rw [stripPotential_increment]
  have hc : Integrable (fun z : ℝ => a*(R-2*u)-a^2+(R-2*u-2*a)*z) (gaussianReal 0 1) :=
    (integrable_const _).add (hz.const_mul _)
  rw [integral_sub hc hz2,
    integral_add (integrable_const _) (hz.const_mul _), integral_const_mul,
    show (∫ z : ℝ, z ∂gaussianReal 0 1) = 0 from integral_id_gaussianReal,
    integral_sq_standardGaussian]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul,
    mul_zero, add_zero]
  ring

/-- Negative drift at every position in the strip under the paper's aR≤1/2 constraint. -/
theorem integral_stripPotential_increment_le {R u a : ℝ} (hu : u ∈ Icc 0 R)
    (ha : 0 ≤ a) (haR : a*R ≤ 1/2) :
    (∫ z, stripPotential R (u+a+z)-stripPotential R u ∂gaussianReal 0 1) ≤ -(1/2 : ℝ) := by
  rw [integral_stripPotential_increment]
  nlinarith [mul_nonneg ha hu.1, sq_nonneg a]

end SwingRepair
