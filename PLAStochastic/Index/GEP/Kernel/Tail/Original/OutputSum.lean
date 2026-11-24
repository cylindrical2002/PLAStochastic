import PLAStochastic.Index.GEP.Kernel.Tail.Original.ScalarSum
import PLAStochastic.Index.GEP.Kernel.Tail.Original.OutputBlocksOn

/-! # Tonelli summation of physical output blocks on arbitrary slope sets -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1600000

def kernelWeightedBulkMass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s x y z : ℝ)
    (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ a, ∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s x y z a p) ∂μ

def kernelWeightedDiracMass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s x : ℝ) : ℝ≥0∞ :=
  ∑' m, ENNReal.ofReal (kernelWeightedDiracTailTerm ν f w s x m)

theorem measurable_kernelWeightedBulkTailTerm (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (w s x y z : ℝ) (p : ℕ × ℕ × ℕ) :
    Measurable (fun a => kernelWeightedBulkTailTerm ν f w s x y z a p) := by
  unfold kernelWeightedBulkTailTerm
  apply (measurable_kernelPhysicalOuterWeight ν w s).mul
  apply measurable_const.mul
  apply Measurable.mul
  · fun_prop
  exact (measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf measurable_const measurable_id
    measurable_const measurable_const measurable_const p.1 p.2.1).mul
      (measurable_krDens_param ν measurableSet_Icc hf measurable_const measurable_id
        measurable_const measurable_const (p.2.2 + 1))

theorem kernel_weighted_bulk_block_sum_measure (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) {w s : ℝ} (hw : 0 ≤ w) (x : ℝ)
    (houter : ∀ a, 0 < a → (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelPhysicalOuterPairAt ν w s a u v)) =
      ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a))
    (hmeasOuter : ∀ u v, Measurable (fun a => kernelPhysicalOuterPairAt ν w s a u v))
    (μ : Measure ℝ) (hμ : ∀ᵐ a ∂μ, 0 < a) :
    (∑' p : ℕ × ℕ × ℕ, ∑' u : ℕ, ∑' v : ℕ, ∫⁻ a, ENNReal.ofReal
      (kernelPhysicalOuterPairAt ν w s a u v * (((p.2.2 : ℝ)+1+w) *
        (Real.exp (s*((p.1 : ℝ)+p.2.1+p.2.2+2)/a) * kernelPairBoth ν f w a x p.1 p.2.1 p.2.2))) ∂μ) =
      kernelWeightedBulkMass ν f w s x 0 w μ + kernelWeightedBulkMass ν f w s x w 0 μ := by
  have hF (p : ℕ × ℕ × ℕ) (u v : ℕ) : Measurable (fun a => ENNReal.ofReal
      (kernelPhysicalOuterPairAt ν w s a u v * (((p.2.2 : ℝ)+1+w) *
        (Real.exp (s*((p.1 : ℝ)+p.2.1+p.2.2+2)/a) * kernelPairBoth ν f w a x p.1 p.2.1 p.2.2)))) := by
    apply Measurable.ennreal_ofReal
    apply (hmeasOuter u v).mul
    apply measurable_const.mul
    apply Measurable.mul
    · fun_prop
    exact measurable_kernelPairBoth ν hf w x _ _ _
  have ht := (lintegral_tsum (μ := μ)
    (fun p : (ℕ × ℕ × ℕ) × ℕ × ℕ => (hF p.1 p.2.1 p.2.2).aemeasurable)).symm
  simp only [ENNReal.tsum_prod'] at ht ⊢
  rw [ht]
  have he : (∫⁻ a, ∑' l : ℕ, ∑' h : ℕ, ∑' m : ℕ, ∑' u : ℕ, ∑' v : ℕ,
      ENNReal.ofReal (kernelPhysicalOuterPairAt ν w s a u v * (((m : ℝ)+1+w) *
        (Real.exp (s*((l : ℝ)+h+m+2)/a) * kernelPairBoth ν f w a x l h m))) ∂μ) =
      ∫⁻ a, ∑' p : ℕ × ℕ × ℕ,
        (ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s x 0 w a p) +
          ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s x w 0 a p)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hμ] with a ha
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro l
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro h
    apply tsum_congr
    intro m
    rw [kernel_outer_factor_sum (kernelPhysicalOuterPairAt_nonneg ν w s a)
      (kernelPhysicalOuterWeight_nonneg ν w s a) (houter a ha)]
    rw [← ENNReal.ofReal_add (kernelWeightedBulkTailTerm_nonneg ν hf0 hw s x 0 w a (l,h,m))
      (kernelWeightedBulkTailTerm_nonneg ν hf0 hw s x w 0 a (l,h,m))]
    congr 1
    unfold kernelWeightedBulkTailTerm kernelPairBoth
    dsimp only
    rw [show (l : ℝ)+h+((m : ℝ)+1)+1 = (l : ℝ)+h+m+2 by ring]
    ring
  rw [he]
  simp_rw [ENNReal.tsum_add]
  exact lintegral_add_left (Measurable.tsum fun p => (measurable_kernelWeightedBulkTailTerm ν hf w s x 0 w p).ennreal_ofReal) _

theorem kernel_weighted_dirac_block_sum (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) {w s x : ℝ}
    (hw : 0 ≤ w) (hx : 0 < x)
    (houter : ∀ a, 0 < a → (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelPhysicalOuterPairAt ν w s a u v)) =
      ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a)) :
    (∑' m : ℕ, ∑' u : ℕ, ∑' v : ℕ, kernelWeightedDiracBlock ν f w s x u m v) =
      kernelWeightedDiracMass ν f w s x := by
  apply tsum_congr
  intro m
  have hh := kernel_outer_factor_sum (P := ((m : ℝ)+1+w) *
    (Real.exp (s*((m : ℝ)+2)/((w+1)/x)) * kernelDiracPin ν f w (m+1) x))
    (kernelPhysicalOuterPairAt_nonneg ν w s ((w+1)/x))
    (kernelPhysicalOuterWeight_nonneg ν w s ((w+1)/x))
    (houter _ (div_pos (by linarith) hx))
  simpa only [kernelWeightedDiracBlock, kernelWeightedDiracMass, kernelWeightedDiracTailTerm,
    show ((m : ℝ)+1)+1 = (m : ℝ)+2 by ring] using hh

theorem kernel_weighted_majorant_on_sum (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) {w s x : ℝ} (hw : 0 ≤ w) (hx : 0 < x)
    (houter : ∀ a, 0 < a → (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelPhysicalOuterPairAt ν w s a u v)) =
      ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a))
    (hmeasOuter : ∀ u v, Measurable (fun a => kernelPhysicalOuterPairAt ν w s a u v))
    (S : Set ℝ) :
    (∑' p : KernelIFBlockIndex, kernelWeightedBlockMajorantOn ν f w s x S p) =
      2 * (kernelWeightedBulkMass ν f w s x 0 w ((volume.restrict (Ioi (0 : ℝ))).restrict S) +
        kernelWeightedBulkMass ν f w s x w 0 ((volume.restrict (Ioi (0 : ℝ))).restrict S) +
        kernelWeightedDiracMass ν f w s x) := by
  unfold kernelWeightedBlockMajorantOn
  rw [kernel_block_tsum_split]
  rw [kernel_weighted_dirac_block_sum ν f hw hx houter]
  unfold kernelWeightedBulkBlockOn
  have hμ : ∀ᵐ a ∂((volume.restrict (Ioi (0 : ℝ))).restrict S), 0 < a :=
    ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioi)
  rw [kernel_weighted_bulk_block_sum_measure ν hf hf0 hw x houter hmeasOuter
    ((volume.restrict (Ioi (0 : ℝ))).restrict S) hμ]

theorem kernel_weighted_majorant_sum (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) {w s x : ℝ} (hw : 0 ≤ w) (hx : 0 < x)
    (houter : ∀ a, 0 < a → (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelPhysicalOuterPairAt ν w s a u v)) =
      ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a))
    (hmeasOuter : ∀ u v, Measurable (fun a => kernelPhysicalOuterPairAt ν w s a u v)) :
    (∑' p : KernelIFBlockIndex, kernelWeightedBlockMajorant ν f w s x p) =
      2 * (kernelWeightedBulkMass ν f w s x 0 w (volume.restrict (Ioi (0 : ℝ))) +
        kernelWeightedBulkMass ν f w s x w 0 (volume.restrict (Ioi (0 : ℝ))) +
        kernelWeightedDiracMass ν f w s x) := by
  simpa only [kernelWeightedBlockMajorantOn, kernelWeightedBlockMajorant,
    kernelWeightedBulkBlockOn, kernelWeightedBulkBlock, Measure.restrict_univ] using
    kernel_weighted_majorant_on_sum ν hf hf0 hw hx houter hmeasOuter Set.univ

/-- The actual output mass on any slope set, including its genuine Dirac
part, is bounded after every exterior and interior length is summed. -/
theorem kernel_output_actual_block_mass_on_le {D θ vlo vhi η M C eps x : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (heps : 1 ≤ eps) (hx : 0 < x)
    (houter : ∀ a, 0 < a → (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelPhysicalOuterPairAt ν (2*eps) (η/C) a u v)) =
      ENNReal.ofReal (kernelPhysicalOuterWeight ν (2*eps) (η/C) a))
    (hmeasOuter : ∀ u v, Measurable (fun a => kernelPhysicalOuterPairAt ν (2*eps) (η/C) a u v))
    (S : Set ℝ) :
    kernelIFTotalPinBlockMassOn ν f eps S (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) (fun _ => True) x ≤
      (4 * ENNReal.ofReal (M*(8*D/θ^2)/C)) *
        (kernelWeightedBulkMass ν f (2*eps) (η/C) x 0 (2*eps) ((volume.restrict (Ioi (0 : ℝ))).restrict S) +
         kernelWeightedBulkMass ν f (2*eps) (η/C) x (2*eps) 0 ((volume.restrict (Ioi (0 : ℝ))).restrict S) +
         kernelWeightedDiracMass ν f (2*eps) (η/C) x) := by
  classical
  have hl := ENNReal.tsum_le_tsum (fun p => kernel_IF_left_output_block_on_le hν hθ hψ hη hC hscale hf0 heps hx S p)
  have hr := ENNReal.tsum_le_tsum (fun p => kernel_IF_right_output_block_on_le hν hθ hψ hη hC hscale hf0 heps hx S p)
  unfold kernelIFTotalPinBlockMassOn
  simp only [if_true]
  apply (add_le_add hl hr).trans_eq
  rw [ENNReal.tsum_mul_left, kernel_weighted_majorant_on_sum ν hf hf0 (by linarith) hx houter hmeasOuter S]
  ring

theorem kernel_output_actual_block_mass_le {D θ vlo vhi η M C eps x : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (heps : 1 ≤ eps) (hx : 0 < x)
    (houter : ∀ a, 0 < a → (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelPhysicalOuterPairAt ν (2*eps) (η/C) a u v)) =
      ENNReal.ofReal (kernelPhysicalOuterWeight ν (2*eps) (η/C) a))
    (hmeasOuter : ∀ u v, Measurable (fun a => kernelPhysicalOuterPairAt ν (2*eps) (η/C) a u v)) :
    kernelIFTotalPinBlockMass ν f eps (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) (fun _ => True) x ≤
      (4 * ENNReal.ofReal (M*(8*D/θ^2)/C)) *
        (kernelWeightedBulkMass ν f (2*eps) (η/C) x 0 (2*eps) (volume.restrict (Ioi (0 : ℝ))) +
         kernelWeightedBulkMass ν f (2*eps) (η/C) x (2*eps) 0 (volume.restrict (Ioi (0 : ℝ))) +
         kernelWeightedDiracMass ν f (2*eps) (η/C) x) := by
  classical
  have hl := ENNReal.tsum_le_tsum (fun p => kernel_IF_left_output_block_le hν hθ hψ hη hC hscale hf0 heps hx p)
  have hr := ENNReal.tsum_le_tsum (fun p => kernel_IF_right_output_block_le hν hθ hψ hη hC hscale hf0 heps hx p)
  unfold kernelIFTotalPinBlockMass
  simp only [if_true]
  apply (add_le_add hl hr).trans_eq
  rw [ENNReal.tsum_mul_left, kernel_weighted_majorant_sum ν hf hf0 (by linarith) hx houter hmeasOuter]
  ring

end
end PGM
