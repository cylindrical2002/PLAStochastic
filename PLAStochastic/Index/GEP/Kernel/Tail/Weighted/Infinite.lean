import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.SlopeIntegral
import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.Infinite

/-! # Absolute convergence of the actual full random-time scalar bulk -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 1400000

def kernelWeightedBulkTailTerm (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s t y z a : ℝ)
    (p : ℕ × ℕ × ℕ) : ℝ :=
  kernelPhysicalOuterWeight ν w s a * (((p.2.2 : ℝ) + 1 + w) *
    (Real.exp (s * ((p.1 : ℝ) + p.2.1 + ((p.2.2 : ℝ) + 1) + 1) / a) *
      (kernelMarkedFullDens (Icc 0 w) ν f 1 a t p.1 p.2.1 y z *
        krDens (Icc 0 w) ν f 1 a (p.2.2 + 1) z y)))

theorem kernelWeightedBulkTailTerm_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (s t y z a : ℝ) (p : ℕ × ℕ × ℕ) :
    0 ≤ kernelWeightedBulkTailTerm ν f w s t y z a p :=
  mul_nonneg (kernelPhysicalOuterWeight_nonneg ν w s a) (mul_nonneg (by positivity)
    (mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _) (krDens_nonneg ν hf0 _ _ _))))

theorem kernelWeightedBulkTailTerm_cube (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (s t y z a : ℝ) (N : ℕ) :
    (∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)),
      ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s t y z a p)) =
        ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a * kernelWeightedPairTailSum ν f w s a t y z N N N) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => kernelWeightedBulkTailTerm_nonneg ν hf0 hw s t y z a p)]
  congr 1
  simp only [Finset.sum_product, kernelWeightedBulkTailTerm, kernelWeightedPairTailSum, Finset.mul_sum]

/-- The full positive-slope integral of the actual nonnegative time series is
finite and has the fixed polynomial width power 16, for every input weight.
This is a genuine infinite sum, not just a bound uniform in finite cutoffs. -/
theorem kernel_regLaw_weighted_bulk_tail_infinite (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ : ℝ, 0 < ζ → ∃ σ K : ℝ, 0 < σ ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w s t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → s ≤ σ → 0 ≤ t → ∀ y z : ℝ,
          (∫⁻ a in Ioi (0 : ℝ), ∑' p : ℕ × ℕ × ℕ,
            ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s t y z a p)) ≤
              ENNReal.ofReal (K * w ^ 16 * Real.exp (ζ * t)) := by
  obtain ⟨ρ, hρ, hint⟩ := kernel_regLaw_weighted_bulk_tail_integral D θ vlo vhi hD hθ hvlo hv
  refine ⟨ρ, hρ, ?_⟩
  intro ζ hζ
  obtain ⟨σ, K, hσ, hK, hdata⟩ := hint ζ hζ
  refine ⟨σ, K, hσ, hK, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hb⟩ := hdata ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro w s t hw hs0 hs hsσ ht y z
  let F : ℕ → ℝ → ℝ≥0∞ := fun N a =>
    ∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)),
      ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s t y z a p)
  have hw0 : 0 ≤ w := by linarith
  have hFE (N : ℕ) (a : ℝ) : F N a =
      ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a * kernelWeightedPairTailSum ν f w s a t y z N N N) :=
    kernelWeightedBulkTailTerm_cube ν hf0 hw0 s t y z a N
  have hFm (N : ℕ) : Measurable (F N) := by
    have he : F N = fun a =>
        ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a * kernelWeightedPairTailSum ν f w s a t y z N N N) :=
      funext (hFE N)
    rw [he]
    exact ((measurable_kernelPhysicalOuterWeight ν w s).mul
      (measurable_kernelWeightedPairTailSum ν hf w s t y z N N N)).ennreal_ofReal
  have hFmono : Monotone F := by
    intro N M hNM a
    exact Finset.sum_le_sum_of_subset
      (Finset.product_subset_product (Finset.range_mono hNM)
        (Finset.product_subset_product (Finset.range_mono hNM) (Finset.range_mono hNM)))
  simp_rw [kernel_ennreal_triple_eq_iSup_cube]
  change (∫⁻ a in Ioi (0 : ℝ), ⨆ N : ℕ, F N a) ≤ _
  rw [lintegral_iSup hFm hFmono]
  apply iSup_le
  intro N
  obtain ⟨hI, hB⟩ := hb w s t hw hs0 hs hsσ ht y z N N N
  simp_rw [hFE]
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun a => mul_nonneg (kernelPhysicalOuterWeight_nonneg ν w s a)
      (kernelWeightedPairTailSum_nonneg ν hf0 (by linarith) s a t y z N N N))]
  exact ENNReal.ofReal_le_ofReal hB

end
end PGM
