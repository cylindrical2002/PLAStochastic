import PLAStochastic.Index.GEP.Kernel.Leaves.ScalarAsOutputBoundary
import PLAStochastic.Index.GEP.Kernel.Output.Identification.UniformWindow
import PLAStochastic.Index.GEP.Kernel.Output.Identification.InterfaceTransfer

/-!
# The scalar kernel leaf follows from the output kernel leaf

The constant output test identifies the boundary density with the normalized
scalar influence. Derivative uniqueness transfers the quantitative estimates
from any output boundary supplied by `KernelPhi` to the concrete scalar
primitive, preserving the original exponent and quantifier order.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- Scaling the concrete scalar primitive retains its global integrability. -/
theorem kernel_IF_normalized_primitive {eps : ℝ} {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ≥0∞}
    (h : AEPrimitive (lawJC eps ν) (kernelIFInfluence ν f eps))
    (hi : Integrable (kernelIFInfluence ν f eps)) :
    AEPrimitive (fun x => lawJC eps ν x / lawC eps ν)
      (fun x => kernelIFInfluence ν f eps x / lawC eps ν) ∧
      Integrable (fun x => kernelIFInfluence ν f eps x / lawC eps ν) := by
  obtain ⟨hI, c, hc⟩ := h
  refine ⟨⟨fun R => (hI R).div_const _, c / lawC eps ν, ?_⟩, hi.div_const _⟩
  filter_upwards [hc] with x hx
  rw [hx, intervalIntegral.integral_div, add_div]

/-- Any original boundary kernel for the constant test agrees with the
normalized scalar density on the positive half-line. -/
theorem kernel_constant_boundary_eq_normalized_IF {D θ vlo vhi eps : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ≥0∞} (hC : 0 < lawC eps ν)
    (hconcrete : IsBdryKernel eps ν (fun _ => 1)
      (outputBoundaryKernel eps ν f (fun _ => 1)))
    {B : ℝ → ℝ} (hB : IsBdryKernel eps ν (fun _ => 1) B) :
    B =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => kernelIFInfluence ν f eps x / lawC eps ν) := by
  filter_upwards [kernel_bdryKernel_unique hB hconcrete,
    ae_restrict_mem measurableSet_Ioi] with x hx hxpos
  rw [hx, output_boundary_kernel_pos eps ν f (fun _ => 1) hxpos,
    output_IF_boundary_one hν hC]

/-- `KernelC` is not an independent remaining analytic leaf: the original
`KernelPhi` implies it by the admissible constant test. The polynomial tail
exponent is chosen before the input window and input exponential weight. -/
theorem kernelC_of_kernelPhi (hPhi : KernelPhi) : KernelC := by
  intro D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηB, hηB, hPhiClass⟩ := hPhi D θ vlo vhi hD hθ hvlo hv
  obtain ⟨η0, eOutput, hη0, heOutput, hWindow⟩ :=
    output_window_facts_regLaw D θ vlo vhi hD hθ hvlo hv
  obtain ⟨eScalar, hScalar⟩ := kernel_IF_influence_regLaw D θ vlo vhi hD hθ hvlo hv
  let η := min ηB η0
  have hη : 0 < η := lt_min hηB hη0
  have hηB' : η ≤ ηB := min_le_left _ _
  have hη0' : η ≤ η0 := min_le_right _ _
  have hOne : OutTest η 1 (fun _ => (1 : ℝ)) :=
    ⟨measurable_const, fun x hx => by
      rw [abs_one, one_mul]
      exact Real.one_le_exp (mul_nonneg hη.le hx)⟩
  obtain ⟨P₀, hPhiWeight⟩ := hPhiClass η hη hηB'
  refine ⟨P₀, fun b ζ hb hζ => ?_⟩
  obtain ⟨P, K, ePhi, hPhiBounds⟩ := hPhiWeight b ζ hb hζ
  refine ⟨P, K, max ePhi (max eOutput eScalar), fun eps heps ν hν => ?_⟩
  have hePhi : ePhi ≤ eps := (le_max_left _ _).trans heps
  have heOutput' : eOutput ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans heps)
  have heScalar : eScalar ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans heps)
  obtain ⟨f, hf, _, _, _, hνf⟩ := hν.density
  let fE : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  have hfE : Measurable fE := hf.ennreal_ofReal
  obtain ⟨hC, hηθ, hWin, hfin⟩ := hWindow eps heOutput' ν hν η hη hη0'
  have hconcrete := output_isBdryKernel_of_window hν hθ hfE hνf
    (heOutput.trans heOutput') hOne hη hC hηθ hWin hfin
  obtain ⟨B, hB, hAL, hTail⟩ := hPhiBounds eps hePhi ν hν 1 (fun _ => 1) hOne
  obtain ⟨hScalarPrimitive, hiScalar, _⟩ := hScalar eps heScalar ν hν fE hfE hνf
  have hNormalized := kernel_IF_normalized_primitive hScalarPrimitive hiScalar
  have he := kernel_constant_boundary_eq_normalized_IF hν hC hconcrete hB
  refine ⟨fun x => kernelIFInfluence ν fE eps x / lawC eps ν, hNormalized.1, ?_, ?_⟩
  · simpa only [one_mul] using hAL.congr_ae
      (ae_restrict_of_ae_restrict_of_subset (fun _ hx => hx.1) he.symm)
  · simpa only [one_mul] using hTail.congr_ae he.symm

end
end PGM
