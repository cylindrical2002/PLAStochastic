import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.KilledBlocks

/-!
# Removing the physical positivity projection after reconstruction

The two smoothing densities vanish whenever a reconstructed random gap is
nonpositive. Otherwise the positive original iid gaps and the positive marked
gap make the whole reconstructed prefix positive. An arbitrary nonnegative
path reward is retained throughout.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

theorem kernel_IF_block_projection_update_three {f : ℝ → ℝ≥0∞}
    (hf0 : ∀ u, u ≤ 0 → f u = 0) {eps a x u v : ℝ} (hx : 0 < x)
    {k i j m : ℕ} (q : FluxFacetIndex k) (W : (ℕ → ℝ) → ℝ≥0∞)
    {g : ℕ → ℝ} (hg : ∀ l < k, 0 < g l) :
    let p := Function.update (Function.update (Function.update g j u) m v) i x
    f u * f v * kernelIFBlockWeight eps a q W p =
      f u * f v * (ENNReal.ofReal (kernelIFSurvival eps a q p) * W p) := by
  dsimp only
  by_cases hu : 0 < u
  · by_cases hv : 0 < v
    · have hp : ∀ l < k,
          0 < (Function.update (Function.update (Function.update g j u) m v) i x) l := by
        intro l hl
        by_cases hli : l = i
        · subst l
          simpa only [Function.update_self] using hx
        · rw [Function.update_of_ne hli]
          by_cases hlm : l = m
          · subst l
            simpa only [Function.update_self] using hv
          · rw [Function.update_of_ne hlm]
            by_cases hlj : l = j
            · subst l
              simpa only [Function.update_self] using hu
            · simpa only [Function.update_of_ne hlj] using hg l hl
      rw [kernelIFBlockWeight, indicator_of_mem (show
        Function.update (Function.update (Function.update g j u) m v) i x ∈
          {h : ℕ → ℝ | ∀ l < k, 0 < h l} from hp)]
    · simp only [hf0 v (le_of_not_gt hv), mul_zero, zero_mul]
  · simp only [hf0 u (le_of_not_gt hu), zero_mul]

theorem kernel_IF_left_projection_ae (ν : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u) {f : ℝ → ℝ≥0∞}
    (hf0 : ∀ u, u ≤ 0 → f u = 0) {eps a x : ℝ} (hx : 0 < x)
    {k : ℕ} (q : FluxFacetIndex k) (i j m : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞) :
    ∀ᵐ g ∂iidLaw ν,
      f (kernelFacetP eps q / a - x - kernelFacetRestA q i j g) *
        f (kernelFacetQ eps q / a - kernelFacetRestB q m g) *
          kernelIFBlockWeight eps a q W (kernelIFLeftPath eps x a q i j m g) =
      f (kernelFacetP eps q / a - x - kernelFacetRestA q i j g) *
        f (kernelFacetQ eps q / a - kernelFacetRestB q m g) *
          (ENNReal.ofReal (kernelIFSurvival eps a q (kernelIFLeftPath eps x a q i j m g)) *
            W (kernelIFLeftPath eps x a q i j m g)) := by
  have hall : ∀ᵐ g ∂iidLaw ν, ∀ l, 0 < g l := by
    rw [ae_all_iff]
    intro l
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) l).quasiMeasurePreserving
      |>.ae hpos
  filter_upwards [hall] with g hg
  exact kernel_IF_block_projection_update_three hf0 hx q W (fun l _ => hg l)

theorem kernel_IF_right_projection_ae (ν : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u) {f : ℝ → ℝ≥0∞}
    (hf0 : ∀ u, u ≤ 0 → f u = 0) {eps a x : ℝ} (hx : 0 < x)
    {k : ℕ} (q : FluxFacetIndex k) (i j m : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞) :
    ∀ᵐ g ∂iidLaw ν,
      f (kernelFacetQ eps q / a - x - kernelFacetRestRight q i j g) *
        f (kernelFacetP eps q / a - kernelFacetRestLeft q m g) *
          kernelIFBlockWeight eps a q W (kernelIFRightPath eps x a q i j m g) =
      f (kernelFacetQ eps q / a - x - kernelFacetRestRight q i j g) *
        f (kernelFacetP eps q / a - kernelFacetRestLeft q m g) *
          (ENNReal.ofReal (kernelIFSurvival eps a q (kernelIFRightPath eps x a q i j m g)) *
            W (kernelIFRightPath eps x a q i j m g)) := by
  have hall : ∀ᵐ g ∂iidLaw ν, ∀ l, 0 < g l := by
    rw [ae_all_iff]
    intro l
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) l).quasiMeasurePreserving
      |>.ae hpos
  filter_upwards [hall] with g hg
  exact kernel_IF_block_projection_update_three hf0 hx q W (fun l _ => hg l)

end
end PGM
