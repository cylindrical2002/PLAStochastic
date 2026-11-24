import PLAStochastic.Index.GEP.Kernel.Output.Identification.InfinitePrimitive

/-!
# Identification of the actual infinite output boundary kernel

The boundary is the concrete weighted IF series on the positive half-line.
Outside that half-line it compensates the direct term, so the original
primitive definition does not impose conditions on negative test arguments.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_insKernel_div (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (F : (ℕ → ℝ) → ℝ) (C x : ℝ) :
    insKernel eps ν (fun g => F g/C) x = insKernel eps ν F x/C := by
  unfold insKernel
  have hi (i : ℕ) :
      (fun g => {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => F (Function.update g i x)/C) g) =
      (fun g => {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => F (Function.update g i x)) g/C) := by
    funext g
    by_cases hg : (i : ℕ∞) < gapSegLen eps g
    · rw [indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hg),
        indicator_of_mem (show g ∈ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hg)]
    · rw [indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hg),
        indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g} from hg), zero_div]
  simp_rw [hi, integral_div]
  exact tsum_div_const

theorem output_derivative_tsum_identified {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} (heps : 0 < eps) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C) (hηθ : η/C ≤ θ/4)
    (hWin : Summable (fluxWindowMoment eps ν (2*η/C)))
    (hfin : ∀ᵐ g ∂iidLaw ν, gapSegLen eps g ≠ ⊤) :
    (fun x => ∑' a : ℕ × ℕ, outputStepDerivative eps ν f ψ C a x)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
    (fun x => insKernel eps ν (fun g => ψ (stopSum eps g/C)) x/C +
      outputIFBoundary eps ν f ψ C x) := by
  have hM := hψ.nonneg
  have hκ : 2*η/C ≤ θ/2 := by linarith [show 2*η/C = 2*(η/C) by ring]
  have hFm : Measurable (fun s => ψ (s/C)/C) :=
    (hψ.1.comp (measurable_id.div_const C)).div_const C
  have hF (s : ℝ) (hs : 0 ≤ s) := output_direct_growth hψ hη.le hC hs
  filter_upwards [(output_IF_boundary_converges hν hθ hf hνf heps hψ hη.le hC hηθ hWin).2,
    ae_restrict_mem measurableSet_Ioi] with x hIF hx
  have hnorm := output_step_norm_summable hν hθ hFm (by positivity) hκ (by positivity)
    hF hWin hx.le
  have hd : Summable (fun a : ℕ × ℕ => ∫ g, outputStep eps (fun s => ψ (s/C)/C) a x g ∂iidLaw ν) :=
    hnorm.of_norm_bounded (fun _ => norm_integral_le_integral_norm _)
  have he (a : ℕ × ℕ) : outputStepDerivative eps ν f ψ C a x =
      (∫ g, outputStep eps (fun s => ψ (s/C)/C) a x g ∂iidLaw ν) +
      outputIFTerm eps ν f ψ C a x := by
    exact indicator_of_mem hx _
  simp_rw [he]
  rw [hd.tsum_add hIF.of_norm,
    output_steps_eq_insKernel hν hθ hFm (by positivity) hκ (by positivity) hF hWin hfin hx.le,
    output_insKernel_div]
  rfl

def outputBoundaryKernel (eps : ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x => directKernel eps ν ψ x +
    outputIFBoundary eps ν f ψ (lawC eps ν) x) x - directKernel eps ν ψ x

theorem output_boundary_kernel_pos (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (ψ : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    outputBoundaryKernel eps ν f ψ x = outputIFBoundary eps ν f ψ (lawC eps ν) x := by
  rw [outputBoundaryKernel, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
  ring

/-- The actual infinite facet series is an original output boundary kernel. -/
theorem output_isBdryKernel_of_window {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} (heps : 1 ≤ eps) {η M : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < lawC eps ν)
    (hηθ : η/lawC eps ν ≤ θ/4)
    (hWin : Summable (fluxWindowMoment eps ν (2*η/lawC eps ν)))
    (hfin : ∀ᵐ g ∂iidLaw ν, gapSegLen eps g ≠ ⊤) :
    IsBdryKernel eps ν ψ (outputBoundaryKernel eps ν f ψ) := by
  have hp := output_concrete_primitive_of_window hν hθ hf hνf heps hψ hη hC hηθ hWin hfin
  have he := output_derivative_tsum_identified hν hθ hf hνf (by linarith : 0 < eps)
    hψ hη hC hηθ hWin hfin
  have hp' := output_aePrimitive_congr_positive hp he
  change AEPrimitive (outIns eps ν ψ) (fun x => directKernel eps ν ψ x +
    outputBoundaryKernel eps ν f ψ x)
  have he' : (fun x => directKernel eps ν ψ x + outputBoundaryKernel eps ν f ψ x) =
      (Ioi (0 : ℝ)).indicator (fun x => directKernel eps ν ψ x +
        outputIFBoundary eps ν f ψ (lawC eps ν) x) := by
    funext x
    unfold outputBoundaryKernel
    ring
  rw [he']
  exact hp'

end
end PGM
