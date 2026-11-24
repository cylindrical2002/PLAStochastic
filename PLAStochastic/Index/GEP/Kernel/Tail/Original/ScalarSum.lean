import PLAStochastic.Index.GEP.Kernel.Tail.Original.ScalarBlocks
import PLAStochastic.Index.GEP.Kernel.Tail.Original.BlockSum

/-! # Summing all actual scalar exterior lengths before the tail estimate -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1400000

theorem measurable_kernelOuterPairAt (ν : ProbabilityMeasure ℝ) (w : ℝ) (u v : ℕ) :
    Measurable (fun a => kernelOuterPairAt ν w a u v) := by
  unfold kernelOuterPairAt
  apply Measurable.add <;> apply Measurable.mul <;>
    apply measurable_kernel_surv_param ν measurableSet_Icc <;> fun_prop

theorem measurable_kernelPairBoth (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (w x : ℝ) (l h m : ℕ) :
    Measurable (fun a => kernelPairBoth ν f w a x l h m) := by
  unfold kernelPairBoth
  apply Measurable.add <;> apply Measurable.mul
  all_goals first
    | apply measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf <;> fun_prop
    | apply measurable_krDens_param ν measurableSet_Icc hf <;> fun_prop

theorem measurable_kernelBulkTailTerm (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (w x y z : ℝ) (p : ℕ × ℕ × ℕ) :
    Measurable (fun a => kernelBulkTailTerm ν f w x y z a p) := by
  unfold kernelBulkTailTerm
  apply (measurable_kernelOuterWeight ν w).mul
  apply measurable_const.mul
  exact (measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf measurable_const measurable_id
    measurable_const measurable_const measurable_const p.1 p.2.1).mul
      (measurable_krDens_param ν measurableSet_Icc hf measurable_const measurable_id
        measurable_const measurable_const (p.2.2 + 1))

theorem kernelOuterPairAt_sum_regLaw (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν)
    {w a : ℝ} (hw : 1 ≤ w) (ha : 0 < a) :
    (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelOuterPairAt ν w a u v)) =
      ENNReal.ofReal (kernelOuterWeight ν w a) := by
  obtain ⟨K, hK, hgreen⟩ := kernel_regLaw_outer_green_large D θ vlo vhi a hD hθ hvlo hv ha
  have hp (y : ℝ) := (hgreen ν hν 0 w 1 a hw (by rw [abs_of_pos ha]) y).1
  have hm (y : ℝ) := (hgreen ν hν 0 w (-1) (-a) hw (by rw [abs_neg, abs_of_pos ha]) y).1
  simp only [zero_add] at hp hm
  exact kernel_real_outer_pair_sum _ _ _ _
    (fun n => krSurv_nonneg measurableSet_Icc ν _ _ n _) (fun n => krSurv_nonneg measurableSet_Icc ν _ _ n _)
    (fun n => krSurv_nonneg measurableSet_Icc ν _ _ n _) (fun n => krSurv_nonneg measurableSet_Icc ν _ _ n _)
    (hm 0) (hp 0) (hm w) (hp w)

def kernelBulkMass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w x y z : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in Ioi (0 : ℝ), ∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelBulkTailTerm ν f w x y z a p)

def kernelDiracMass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w x : ℝ) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal (kernelDiracTailTerm ν f w x m)

theorem kernel_scalar_bulk_block_sum (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) {w : ℝ} (hw : 1 ≤ w) (x : ℝ) :
    (∑' p : ℕ × ℕ × ℕ, ∑' u : ℕ, ∑' v : ℕ, kernelScalarBulkBlock ν f w x u p.1 p.2.1 p.2.2 v) =
      kernelBulkMass ν f w x 0 w + kernelBulkMass ν f w x w 0 := by
  have hw0 : 0 ≤ w := by linarith
  have hmeas (p : ℕ × ℕ × ℕ) (u v : ℕ) : Measurable (fun a => ENNReal.ofReal
      (kernelOuterPairAt ν w a u v * (((p.2.2 : ℝ)+1+w) * kernelPairBoth ν f w a x p.1 p.2.1 p.2.2))) :=
    ((measurable_kernelOuterPairAt ν w u v).mul (measurable_const.mul (measurable_kernelPairBoth ν hf w x _ _ _))).ennreal_ofReal
  unfold kernelScalarBulkBlock
  rw [kernel_block_sum_lintegral hmeas]
  have he : (∫⁻ a in Ioi (0 : ℝ), ∑' p : ℕ × ℕ × ℕ, ∑' u : ℕ, ∑' v : ℕ,
      ENNReal.ofReal (kernelOuterPairAt ν w a u v * (((p.2.2 : ℝ)+1+w) * kernelPairBoth ν f w a x p.1 p.2.1 p.2.2))) =
      ∫⁻ a in Ioi (0 : ℝ), ∑' p : ℕ × ℕ × ℕ,
        (ENNReal.ofReal (kernelBulkTailTerm ν f w x 0 w a p) + ENNReal.ofReal (kernelBulkTailTerm ν f w x w 0 a p)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    apply tsum_congr
    intro p
    rw [kernel_outer_factor_sum (kernelOuterPairAt_nonneg ν w a)
      (kernelOuterWeight_nonneg ν w a) (kernelOuterPairAt_sum_regLaw D θ vlo vhi hD hθ hvlo hv ν hν hw ha)]
    rw [← ENNReal.ofReal_add (kernelBulkTailTerm_nonneg ν hf0 hw0 x 0 w a p)
      (kernelBulkTailTerm_nonneg ν hf0 hw0 x w 0 a p)]
    congr 1
    unfold kernelBulkTailTerm kernelPairBoth
    ring
  rw [he]
  simp_rw [ENNReal.tsum_add]
  exact lintegral_add_left (Measurable.tsum fun p => (measurable_kernelBulkTailTerm ν hf w x 0 w p).ennreal_ofReal) _

theorem kernel_scalar_dirac_block_sum (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} {w x : ℝ} (hw : 1 ≤ w) (hx : 0 < x) :
    (∑' m : ℕ, ∑' u : ℕ, ∑' v : ℕ, kernelScalarDiracBlock ν f w x u m v) =
      kernelDiracMass ν f w x := by
  apply tsum_congr
  intro m
  apply kernel_outer_factor_sum (kernelOuterPairAt_nonneg ν w _)
    (kernelOuterWeight_nonneg ν w _)
  exact kernelOuterPairAt_sum_regLaw D θ vlo vhi hD hθ hvlo hv ν hν hw (div_pos (by linarith) hx)

/-- All five random lengths of the original source facets are now summed.
The remaining masses are exactly the completed bulk and Dirac tail series. -/
theorem kernel_scalar_actual_block_mass_le (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) {eps x : ℝ} (heps : 1 ≤ eps) (hx : 0 < x) :
    kernelIFPinBlockMass ν f eps (fun _ => True) x ≤
      4 * (kernelBulkMass ν f (2*eps) x 0 (2*eps) + kernelBulkMass ν f (2*eps) x (2*eps) 0 +
        kernelDiracMass ν f (2*eps) x) := by
  classical
  have hleft := ENNReal.tsum_le_tsum (fun p => kernel_IF_left_scalar_block_le ν hf0 heps hx p)
  have hright := ENNReal.tsum_le_tsum (fun p => kernel_IF_right_scalar_block_le ν hf0 heps hx p)
  have hsum : (∑' p : KernelIFBlockIndex, kernelScalarBlockMajorant ν f (2*eps) x p) =
      2 * (kernelBulkMass ν f (2*eps) x 0 (2*eps) + kernelBulkMass ν f (2*eps) x (2*eps) 0 +
        kernelDiracMass ν f (2*eps) x) := by
    rw [show (fun p => kernelScalarBlockMajorant ν f (2*eps) x p) =
      (fun p : KernelIFBlockIndex => kernelScalarBulkBlock ν f (2*eps) x p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 +
        if p.2.1=0 ∧ p.2.2.1=0 then kernelScalarDiracBlock ν f (2*eps) x p.1 p.2.2.2.1 p.2.2.2.2.1 else 0) from rfl]
    rw [kernel_block_tsum_split,
      kernel_scalar_bulk_block_sum D θ vlo vhi hD hθ hvlo hv ν hν hf hf0 (by linarith),
      kernel_scalar_dirac_block_sum D θ vlo vhi hD hθ hvlo hv ν hν (by linarith) hx]
  unfold kernelIFPinBlockMass
  simp only [if_true]
  apply (add_le_add hleft hright).trans_eq
  rw [hsum]
  ring

end
end PGM
