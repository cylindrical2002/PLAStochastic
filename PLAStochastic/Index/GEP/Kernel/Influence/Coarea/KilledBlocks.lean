import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.ActiveMeasure

/-!
# Four physical killed blocks in the actual coarea density

The outer reversed block and the three forward blocks use the reconstructed
path and its integration slope. The positivity projection remains explicit.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The four survival factors at the actual active contacts. -/
def kernelIFSurvival (eps a : ℝ) {k : ℕ} (q : FluxFacetIndex k) (g : ℕ → ℝ) : ℝ :=
  krAlive (Icc 0 (2*eps)) (-1) (-a) q.1 (eps - fluxFacetSign q * eps)
    (kernelReversePrefix g q.1) *
  (krAlive (Icc 0 (2*eps)) 1 a (q.2.1-q.1) (eps - fluxFacetSign q * eps)
    (fun l => g (l+q.1)) *
  (krAlive (Icc 0 (2*eps)) 1 a (q.2.2.1-q.2.1) (eps + fluxFacetSign q * eps)
    (fun l => g (l+q.2.1)) *
  krAlive (Icc 0 (2*eps)) 1 a (k-q.2.2.1) (eps - fluxFacetSign q * eps)
    (fun l => g (l+q.2.2.1))))

/-- The four-block reward includes the same physical positivity projection
as the original active-event weight. -/
def kernelIFBlockWeight (eps a : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (W : (ℕ → ℝ) → ℝ≥0∞) : (ℕ → ℝ) → ℝ≥0∞ :=
  {g : ℕ → ℝ | ∀ l < k, 0 < g l}.indicator
    (fun g => ENNReal.ofReal (kernelIFSurvival eps a q g) * W g)

/-- This identity is pathwise, including infeasible and nonpositive paths. -/
theorem kernel_IF_pathWeight_eq_blocks {eps a : ℝ} {k : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (W : (ℕ → ℝ) → ℝ≥0∞) (g : ℕ → ℝ)
    (hA : gapKeys g q.2.1 - gapKeys g q.1 = kernelFacetP eps q / a)
    (hB : gapKeys g q.2.2.1 - gapKeys g q.2.1 = kernelFacetQ eps q / a) :
    kernelIFPathWeight eps k W g = kernelIFBlockWeight eps a q W g := by
  classical
  by_cases hg : ∀ l < k, 0 < g l
  · have he := kernel_IF_indicator_of_sums hq ha g hg hA hB
    change _ = kernelIFSurvival eps a q g at he
    unfold kernelIFBlockWeight
    rw [indicator_of_mem (show g ∈ {h : ℕ → ℝ | ∀ l < k, 0 < h l} from hg), ← he]
    by_cases hp : prefixAffineFeasible eps (gapKeys g) (k + 1)
    · rw [indicator_of_mem (show g ∈ {h : ℕ → ℝ |
        prefixAffineFeasible eps (gapKeys h) (k + 1)} from hp), ENNReal.ofReal_one, one_mul]
      exact indicator_of_mem (show g ∈ kernelIFPathEvent eps k from ⟨hg, hp⟩) W
    · rw [indicator_of_notMem (show g ∉ {h : ℕ → ℝ |
        prefixAffineFeasible eps (gapKeys h) (k + 1)} from hp), ENNReal.ofReal_zero, zero_mul]
      exact indicator_of_notMem (show g ∉ kernelIFPathEvent eps k from fun h => hp h.2) W
  · unfold kernelIFBlockWeight
    rw [indicator_of_notMem (show g ∉ {h : ℕ → ℝ | ∀ l < k, 0 < h l} from hg)]
    exact indicator_of_notMem (show g ∉ kernelIFPathEvent eps k from fun h => hg h.1) W

theorem kernel_IF_left_weight_blocks {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1)
    (W : (ℕ → ℝ) → ℝ≥0∞) (g : ℕ → ℝ) :
    kernelIFPathWeight eps k W (kernelIFLeftPath eps x a q i j m g) =
      kernelIFBlockWeight eps a q W (kernelIFLeftPath eps x a q i j m g) := by
  have hs := kernel_IF_left_sums hq.1 hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂ (eps := eps) (x := x) (a := a) g
  exact kernel_IF_pathWeight_eq_blocks hq ha W _ hs.1 hs.2

theorem kernel_IF_right_weight_blocks {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (ha : 0 < a)
    (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1)
    (W : (ℕ → ℝ) → ℝ≥0∞) (g : ℕ → ℝ) :
    kernelIFPathWeight eps k W (kernelIFRightPath eps x a q i j m g) =
      kernelIFBlockWeight eps a q W (kernelIFRightPath eps x a q i j m g) := by
  have hs := kernel_IF_right_sums hq.1 hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂ (eps := eps) (x := x) (a := a) g
  exact kernel_IF_pathWeight_eq_blocks hq ha W _ hs.1 hs.2

/-- The explicit left coarea density factors along the four physical blocks. -/
theorem kernel_IF_left_density_blocks (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1)
    (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) :
    kernelIFLeftDensity ν f eps q i j m W x =
      ∫⁻ g, (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetQ eps q / a ^ 2) *
        (f (kernelFacetP eps q / a - x - kernelFacetRestA q i j g) *
          f (kernelFacetQ eps q / a - kernelFacetRestB q m g) *
            kernelIFBlockWeight eps a q W (kernelIFLeftPath eps x a q i j m g))) ∂iidLaw ν := by
  apply lintegral_congr
  intro g
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [kernel_IF_left_weight_blocks hq ha hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂]

/-- The right formula retains its own Jacobian and block lengths. -/
theorem kernel_IF_right_density_blocks (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    {eps : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : kernelFacetEffective eps q) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1)
    (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) :
    kernelIFRightDensity ν f eps q i j m W x =
      ∫⁻ g, (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetP eps q / a ^ 2) *
        (f (kernelFacetQ eps q / a - x - kernelFacetRestRight q i j g) *
          f (kernelFacetP eps q / a - kernelFacetRestLeft q m g) *
            kernelIFBlockWeight eps a q W (kernelIFRightPath eps x a q i j m g))) ∂iidLaw ν := by
  apply lintegral_congr
  intro g
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  rw [kernel_IF_right_weight_blocks hq ha hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂]

end
end PGM
