import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.SlopeIntegral

/-! # Absolute convergence of the actual full random-time scalar bulk -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 1400000

/-- Rectangular cubes exhaust every triple of finite random lengths. -/
theorem kernel_ennreal_triple_eq_iSup_cube (F : ℕ × ℕ × ℕ → ℝ≥0∞) :
    (∑' p : ℕ × ℕ × ℕ, F p) =
      ⨆ N : ℕ, ∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)), F p := by
  apply ENNReal.tsum_eq_iSup_sum'
  intro s
  let N := s.sup (fun p : ℕ × ℕ × ℕ => p.1 + p.2.1 + p.2.2) + 1
  refine ⟨N, ?_⟩
  intro p hp
  have hh := Finset.le_sup (f := fun p : ℕ × ℕ × ℕ => p.1 + p.2.1 + p.2.2) hp
  simp only [Finset.mem_product, Finset.mem_range]
  dsimp [N]
  omega

def kernelBulkTailTerm (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w t y z a : ℝ)
    (p : ℕ × ℕ × ℕ) : ℝ :=
  kernelOuterWeight ν w a * (((p.2.2 : ℝ) + 1 + w) *
    (kernelMarkedFullDens (Icc 0 w) ν f 1 a t p.1 p.2.1 y z *
      krDens (Icc 0 w) ν f 1 a (p.2.2 + 1) z y))

theorem kernelBulkTailTerm_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (t y z a : ℝ) (p : ℕ × ℕ × ℕ) :
    0 ≤ kernelBulkTailTerm ν f w t y z a p :=
  mul_nonneg (kernelOuterWeight_nonneg ν w a) (mul_nonneg (by positivity)
    (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _) (krDens_nonneg ν hf0 _ _ _)))

theorem kernelBulkTailTerm_cube (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (t y z a : ℝ) (N : ℕ) :
    (∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)),
      ENNReal.ofReal (kernelBulkTailTerm ν f w t y z a p)) =
        ENNReal.ofReal (kernelOuterWeight ν w a * kernelPairTailSum ν f w a t y z N N N) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => kernelBulkTailTerm_nonneg ν hf0 hw t y z a p)]
  congr 1
  simp only [Finset.sum_product, kernelBulkTailTerm, kernelPairTailSum, Finset.mul_sum]

/-- The full positive-slope integral of the actual nonnegative time series is
finite and has the fixed polynomial width power 16, for every input weight.
This is a genuine infinite sum, not just a bound uniform in finite cutoffs. -/
theorem kernel_regLaw_bulk_tail_infinite (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∀ ζ : ℝ, 0 < ζ → ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w t : ℝ, 1 ≤ w → 0 ≤ t → ∀ y z : ℝ,
          (∫⁻ a in Ioi (0 : ℝ), ∑' p : ℕ × ℕ × ℕ,
            ENNReal.ofReal (kernelBulkTailTerm ν f w t y z a p)) ≤
              ENNReal.ofReal (K * w ^ 16 * Real.exp (ζ * t)) := by
  intro ζ hζ
  obtain ⟨K, hK, hdata⟩ := kernel_regLaw_bulk_tail_integral D θ vlo vhi hD hθ hvlo hv ζ hζ
  refine ⟨K, hK, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hb⟩ := hdata ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro w t hw ht y z
  let F : ℕ → ℝ → ℝ≥0∞ := fun N a =>
    ∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)),
      ENNReal.ofReal (kernelBulkTailTerm ν f w t y z a p)
  have hw0 : 0 ≤ w := by linarith
  have hFE (N : ℕ) (a : ℝ) : F N a =
      ENNReal.ofReal (kernelOuterWeight ν w a * kernelPairTailSum ν f w a t y z N N N) :=
    kernelBulkTailTerm_cube ν hf0 hw0 t y z a N
  have hFm (N : ℕ) : Measurable (F N) := by
    have he : F N = fun a =>
        ENNReal.ofReal (kernelOuterWeight ν w a * kernelPairTailSum ν f w a t y z N N N) :=
      funext (hFE N)
    rw [he]
    exact ((measurable_kernelOuterWeight ν w).mul
      (measurable_kernelPairTailSum ν hf w t y z N N N)).ennreal_ofReal
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
  obtain ⟨hI, hB⟩ := hb w t hw ht y z N N N
  simp_rw [hFE]
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun a => mul_nonneg (kernelOuterWeight_nonneg ν w a)
      (kernelPairTailSum_nonneg ν hf0 (by linarith) a t y z N N N))]
  exact ENNReal.ofReal_le_ofReal hB

end
end PGM
