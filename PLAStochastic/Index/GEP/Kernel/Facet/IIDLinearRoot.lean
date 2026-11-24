import PLAStochastic.ForMathlib.MeasureTheory.Measure.Lebesgue.WeightedAffineDensity
import PLAStochastic.Index.GEP.Response.Score.ChangeOfMeasure

/-!
# Explicit weighted densities of actual iid linear roots

The selected coordinate is reinserted into the original iid path. The active
weight is evaluated on that same reinserted path, retaining all dependencies.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

/-- The full weight, including the one-coordinate density, after insertion. -/
def kernelIIDRootWeight (f : ℝ → ℝ≥0∞) (i : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞)
    (p : (ℕ → ℝ) × ℝ) : ℝ≥0∞ := f p.2 * W (Function.update p.1 i p.2)

theorem measurable_kernelIIDRootWeight {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (i : ℕ) {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelIIDRootWeight f i W) := by
  exact (hf.comp measurable_snd).mul
    (hW.comp ((measurable_update_pair i).comp measurable_swap))

/-- The affine formula is applied to the actual original iid law, not an
independently postulated law of the remaining coordinates. -/
theorem kernel_iid_affine_map_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (i : ℕ) {a : ℝ} (ha : a ≠ 0) {E b : (ℕ → ℝ) → ℝ}
    (hE : Measurable E) (hb : Measurable b)
    (hupdate : ∀ g x, E (Function.update g i x) = b g + a * x)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity W).map E =
      volume.withDensity (kernelLinearDensity (iidLaw ν) a b (kernelIIDRootWeight f i W)) := by
  rw [← kernel_weighted_affine_map_density (iidLaw ν) ha hb
    (measurable_kernelIIDRootWeight hf i hW)]
  have hU : Measurable (fun p : (ℕ → ℝ) × ℝ => Function.update p.1 i p.2) :=
    (measurable_update_pair i).comp measurable_swap
  have hA : Measurable (fun p : (ℕ → ℝ) × ℝ => b p.1 + a * p.2) := by fun_prop
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hφE : Measurable (fun g => φ (E g)) := hφ.comp hE
  have hφA : Measurable (fun p : (ℕ → ℝ) × ℝ => φ (b p.1 + a * p.2)) := by fun_prop
  rw [lintegral_map hφ hE, lintegral_withDensity_eq_lintegral_mul _ hW hφE,
    lintegral_map hφ hA, lintegral_withDensity_eq_lintegral_mul _
      (measurable_kernelIIDRootWeight hf i hW) hφA]
  simp only [Pi.mul_apply]
  rw [lintegral_update ν i (show Measurable (fun g => W g * φ (E g)) by fun_prop)]
  have hiJoint : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      W (Function.update p.2 i p.1) * φ (E (Function.update p.2 i p.1))) :=
    (hW.mul (hφ.comp hE)).comp (measurable_update_pair i)
  have hi : Measurable (fun y => ∫⁻ g, W (Function.update g i y) *
      φ (E (Function.update g i y)) ∂iidLaw ν) := by
    exact hiJoint.lintegral_prod_right'
  rw [hν, lintegral_withDensity_eq_lintegral_mul _ hf hi]
  simp only [Pi.mul_apply]
  have hm (y : ℝ) : Measurable (fun g => W (Function.update g i y) *
      φ (E (Function.update g i y))) := by fun_prop
  simp_rw [← lintegral_const_mul _ (hm _)]
  have hJoint : Measurable (fun p : ℝ × (ℕ → ℝ) => f p.1 *
      (W (Function.update p.2 i p.1) * φ (E (Function.update p.2 i p.1)))) :=
    (hf.comp measurable_fst).mul hiJoint
  have hTarget : Measurable (fun p : (ℕ → ℝ) × ℝ =>
      kernelIIDRootWeight f i W p * φ (b p.1 + a * p.2)) :=
    (measurable_kernelIIDRootWeight hf i hW).mul hφA
  rw [lintegral_lintegral_swap hJoint.aemeasurable, lintegral_prod _ hTarget.aemeasurable]
  apply lintegral_congr
  intro g
  apply lintegral_congr
  intro y
  dsimp only [kernelIIDRootWeight]
  rw [hupdate]
  exact (mul_assoc _ _ _).symm

/-- Every nondegenerate finite homogeneous linear root has this explicit
weighted density, for an arbitrary measurable active-facet weight. -/
theorem kernel_iid_linear_map_density (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (T : Finset ℕ) (c : ℕ → ℝ) {i : ℕ} (hi : i ∈ T) (hc : c i ≠ 0)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    ((iidLaw ν).withDensity W).map (fun g => ∑ l ∈ T, c l * g l) =
      volume.withDensity (kernelLinearDensity (iidLaw ν) (c i)
        (fun g => ∑ l ∈ T.erase i, c l * g l) (kernelIIDRootWeight f i W)) := by
  apply kernel_iid_affine_map_density ν hf hν i hc
    (Finset.measurable_sum _ fun l _ => measurable_const.mul (measurable_pi_apply l))
    (Finset.measurable_sum _ fun l _ => measurable_const.mul (measurable_pi_apply l)) ?_ hW
  intro g x
  simp only [Pi.mul_apply]
  rw [← Finset.sum_erase_add T (fun l => c l * Function.update g i x l) hi,
    Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

end
end PGM
