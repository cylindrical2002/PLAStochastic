import PLAStochastic.Index.GEP.Kernel.Output.Identification.StepPrimitive

/-!
# The infinite occupation primitive with its concrete facet derivative

Local absolute summation preserves the original test class and identifies the
derivative as the sum of the true direct terms and the true weighted facets.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_test_growth {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C) {s : ℝ} (hs : 0 ≤ s) :
    ‖testFn ψ (s/C)‖ ≤ (M/η) * Real.exp ((2*η/C)*s) := by
  simpa only [Real.norm_eq_abs, show 2*η*(s/C) = (2*η/C)*s by ring] using
    hψ.abs_testFn_le_exp hη (div_nonneg hs hC.le)

theorem output_direct_growth {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C) {s : ℝ} (hs : 0 ≤ s) :
    ‖ψ (s/C)/C‖ ≤ (M/C) * Real.exp ((2*η/C)*s) := by
  have hM := hψ.nonneg
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hC]
  calc
    _ ≤ (M*Real.exp (η*(s/C)))/C := div_le_div_of_nonneg_right
      (hψ.2 _ (div_nonneg hs hC.le)) hC.le
    _ ≤ (M*Real.exp ((2*η/C)*s))/C := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        have : 0 ≤ η*s/C := by positivity
        nlinarith [show η*(s/C) = η*s/C by ring,
          show (2*η/C)*s = 2*(η*s/C) by ring])) hM) hC.le
    _ = _ := by ring

theorem output_IF_term_nonpos (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (ψ : ℝ → ℝ) (C : ℝ) (a : ℕ × ℕ) {x : ℝ} (hx : x ≤ 0) :
    outputIFTerm eps ν f ψ C a x = 0 := by
  have hn : x ∉ Ioi (0 : ℝ) := not_lt.mpr hx
  simp only [outputIFTerm, kernelIFWeightedPrefixKernel, kernelIFSignedDensity,
    fluxPositiveDensity, indicator_of_notMem hn, sub_self, ite_self]

theorem output_step_derivative_eq (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (ψ : ℝ → ℝ) (C : ℝ) (a : ℕ × ℕ) :
    outputStepDerivative eps ν f ψ C a = fun x =>
      (Ioi (0 : ℝ)).indicator
        (fun x => ∫ g, outputStep eps (fun s => ψ (s/C)/C) a x g ∂iidLaw ν) x +
      outputIFTerm eps ν f ψ C a x := by
  funext x
  unfold outputStepDerivative
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx,
      output_IF_term_nonpos eps ν f ψ C a (le_of_not_gt hx), add_zero]

theorem output_step_derivative_local_summable {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} (heps : 0 < eps) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C) (hηθ : η/C ≤ θ/4)
    (hWin : Summable (fluxWindowMoment eps ν (2*η/C))) (R : ℝ) :
    (∀ a : ℕ × ℕ, IntervalIntegrable (outputStepDerivative eps ν f ψ C a) volume 0 R) ∧
      Summable (fun a : ℕ × ℕ => ∫ x in Ι (0 : ℝ) R, ‖outputStepDerivative eps ν f ψ C a x‖) := by
  have hM := hψ.nonneg
  have hκ : 2*η/C ≤ θ/2 := by linarith [show 2*η/C = 2*(η/C) by ring]
  have hd (a : ℕ × ℕ) := output_step_local_mass hν hθ (eps := eps)
    ((hψ.1.comp (measurable_id.div_const C)).div_const C)
    (by positivity : 0 ≤ 2*η/C) hκ (by positivity : 0 ≤ M/C)
    (fun s hs => output_direct_growth hψ hη.le hC hs) a R
  have hb := output_IF_local_summable hν hθ hf hνf heps hψ hη.le hC hηθ hWin R
  have hds : Summable (fun a : ℕ × ℕ => ∫ x in Ι (0 : ℝ) R,
      ‖(Ioi (0 : ℝ)).indicator
        (fun x => ∫ g, outputStep eps (fun s => ψ (s/C)/C) a x g ∂iidLaw ν) x‖) := by
    have hs : Summable (fun a : ℕ × ℕ => fluxWindowMoment eps ν (2*η/C) (a.1+1,a.2)) :=
      hWin.comp_injective (fun a b h => Prod.ext
        (by simpa using congrArg Prod.fst h) (by simpa using congrArg Prod.snd h))
    exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun a => (hd a).2) (hs.mul_left _)
  have hi (a : ℕ × ℕ) : IntervalIntegrable (outputStepDerivative eps ν f ψ C a) volume 0 R := by
    rw [output_step_derivative_eq]
    exact (hd a).1.add (hb.1 a)
  refine ⟨hi, Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) ?_
    (hds.add hb.2)⟩
  intro a
  rw [output_step_derivative_eq]
  calc
    _ ≤ ∫ x in Ι (0 : ℝ) R,
        ‖(Ioi (0 : ℝ)).indicator
          (fun x => ∫ g, outputStep eps (fun s => ψ (s/C)/C) a x g ∂iidLaw ν) x‖ +
        ‖outputIFTerm eps ν f ψ C a x‖ :=
      integral_mono ((hd a).1.def'.add (hb.1 a).def').norm
        ((hd a).1.def'.norm.add (hb.1 a).def'.norm) (fun _ => norm_add_le _ _)
    _ = _ := integral_add (hd a).1.def'.norm (hb.1 a).def'.norm

theorem output_aePrimitive_tsum_of_local_bound {ι : Type*} [Countable ι]
    {J j : ι → ℝ → ℝ} {B : ι → ℝ} (hp : ∀ i, AEPrimitive (J i) (j i))
    (hB : Summable B) (hb : ∀ i x, x ∈ Ioo (0 : ℝ) 1 → |J i x| ≤ B i)
    (hs : ∀ R : ℝ, Summable (fun i => ∫ x in Ι (0 : ℝ) R, ‖j i x‖)) :
    AEPrimitive (fun x => ∑' i, J i x) (fun x => ∑' i, j i x) := by
  have hc (i : ι) : ∃ c : ℝ,
      (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), J i x = c+∫ t in (0 : ℝ)..x, j i t) ∧
      |c| ≤ B i + ∫ x in Ι (0 : ℝ) 1, ‖j i x‖ := by
    obtain ⟨c,hc,hcb⟩ := kernel_aePrimitive_constant_bound_local (hp i)
      (by norm_num : (0 : ℝ) < 1) (hb i)
    refine ⟨c,hc,?_⟩
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Real.norm_eq_abs] using hcb
  choose c hc hcb using hc
  exact kernel_aePrimitive_tsum (fun i R => (hp i).1 R) hc
    ((hB.add (hs 1)).of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using hcb i)) hs

theorem output_concrete_primitive_of_window {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} (heps : 1 ≤ eps) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C) (hηθ : η/C ≤ θ/4)
    (hWin : Summable (fluxWindowMoment eps ν (2*η/C)))
    (hfin : ∀ᵐ g ∂iidLaw ν, gapSegLen eps g ≠ ⊤) :
    AEPrimitive (insKernel eps ν (fun g => testFn ψ (stopSum eps g/C)))
      (fun x => ∑' a : ℕ × ℕ, outputStepDerivative eps ν f ψ C a x) := by
  have hM := hψ.nonneg
  have hκ : 2*η/C ≤ θ/2 := by linarith [show 2*η/C = 2*(η/C) by ring]
  have hFm : Measurable (fun s => testFn ψ (s/C)) := hψ.measurable_testFn.comp (measurable_id.div_const C)
  have hF (s : ℝ) (hs : 0 ≤ s) := output_test_growth hψ hη hC hs
  have hS : Summable (fun a : ℕ × ℕ => fluxWindowMoment eps ν (2*η/C) (a.1+1,a.2)) :=
    hWin.comp_injective (fun a b h => Prod.ext
      (by simpa using congrArg Prod.fst h) (by simpa using congrArg Prod.snd h))
  have hp := output_aePrimitive_tsum_of_local_bound
    (output_step_concrete_primitive hν hθ hf hνf heps hψ hη hC hηθ)
    (hS.mul_left (2*(M/η)*Real.exp (2*η/C))) (fun a x hx => ?_)
    (fun R => (output_step_derivative_local_summable hν hθ hf hνf
      (by linarith) hψ hη hC hηθ hWin R).2)
  · apply output_aePrimitive_congr_fun hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (output_steps_eq_insKernel hν hθ hFm (by positivity) hκ (by positivity)
      hF hWin hfin hx.le).symm
  · rw [← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans
      ((output_step_integral_norm_le hν hθ hFm (by positivity) hκ (by positivity) hF hx.1.le a).2.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.2.le
              (show 0 ≤ 2*η/C by positivity))) (by positivity))
          (fluxWindowMoment_nonneg _ _ _ _)))

end
end PGM
