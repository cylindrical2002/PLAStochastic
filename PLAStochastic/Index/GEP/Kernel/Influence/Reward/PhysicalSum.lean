import PLAStochastic.Index.GEP.Kernel.Output.Finite.FacetDensity

/-!
# The output reward in the actual coarea coordinates

The total physical sum on either reconstructed facet path depends only on the
two outer blocks and the slope. In particular it is independent of the marked
gap and of all internal random gaps. This is the cancellation needed to use the
same insertion regularity estimates for the original measurable output tests.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

def kernelIFPhysicalSum (a : ℝ) {k : ℕ} (q : FluxFacetIndex k) (g : ℕ → ℝ) : ℝ :=
  gapKeys g q.1 + ((q.2.2.1 : ℕ) - (q.1 : ℝ)) / a +
    (gapKeys g k - gapKeys g q.2.2.1)

theorem kernel_IF_left_total_sum {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (_hq : fluxFacetValid q) (_hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (_hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) :
    gapKeys (kernelIFLeftPath eps x a q i j m g) k = kernelIFPhysicalSum a q g := by
  have htk : (q.2.2.1 : ℕ) ≤ k := by have := q.2.2.1.isLt; omega
  have hik : i < k := by omega
  have hjk : j < k := by omega
  have hmk : m < k := by omega
  have hmi : i ≠ m := by omega
  have hmj : m ≠ j := by omega
  simp only [kernelIFLeftPath, kernel_gapKeys_update_affine, hik, hjk, hmk, if_true,
    Function.update_of_ne hmi, Function.update_of_ne hji.symm, Function.update_of_ne hmj]
  unfold kernelFacetRestA kernelFacetRestB kernelIFPhysicalSum kernelFacetP kernelFacetQ
  ring

theorem kernel_IF_right_total_sum {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (_hq : fluxFacetValid q) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (_hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) :
    gapKeys (kernelIFRightPath eps x a q i j m g) k = kernelIFPhysicalSum a q g := by
  have htk : (q.2.2.1 : ℕ) ≤ k := by have := q.2.2.1.isLt; omega
  have hik : i < k := by omega
  have hjk : j < k := by omega
  have hmk : m < k := by omega
  have hmi : i ≠ m := by omega
  have hmj : m ≠ j := by omega
  simp only [kernelIFRightPath, kernel_gapKeys_update_affine, hik, hjk, hmk, if_true,
    Function.update_of_ne hmi, Function.update_of_ne hji.symm, Function.update_of_ne hmj]
  unfold kernelFacetRestRight kernelFacetRestLeft kernelIFPhysicalSum kernelFacetP kernelFacetQ
  ring

theorem kernel_IF_left_reward (ν : ProbabilityMeasure ℝ) (C : ℝ) (ψ : ℝ → ℝ)
    {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) (hi₁ : (q.1 : ℕ) ≤ i) (hi₂ : i < q.2.1)
    (hj₁ : (q.1 : ℕ) ≤ j) (hj₂ : j < q.2.1) (hji : j ≠ i)
    (hm₁ : (q.2.1 : ℕ) ≤ m) (hm₂ : m < q.2.2.1) (g : ℕ → ℝ) :
    kernelBoundaryReward ν C ψ (gapKeys (kernelIFLeftPath eps x a q i j m g) k) =
      kernelBoundaryReward ν C ψ (kernelIFPhysicalSum a q g) := by
  rw [kernel_IF_left_total_sum hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂]

theorem kernel_IF_right_reward (ν : ProbabilityMeasure ℝ) (C : ℝ) (ψ : ℝ → ℝ)
    {eps x a : ℝ} {k i j m : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) (hi₁ : (q.2.1 : ℕ) ≤ i) (hi₂ : i < q.2.2.1)
    (hj₁ : (q.2.1 : ℕ) ≤ j) (hj₂ : j < q.2.2.1) (hji : j ≠ i)
    (hm₁ : (q.1 : ℕ) ≤ m) (hm₂ : m < q.2.1) (g : ℕ → ℝ) :
    kernelBoundaryReward ν C ψ (gapKeys (kernelIFRightPath eps x a q i j m g) k) =
      kernelBoundaryReward ν C ψ (kernelIFPhysicalSum a q g) := by
  rw [kernel_IF_right_total_sum hq hi₁ hi₂ hj₁ hj₂ hji hm₁ hm₂]

theorem kernel_IF_physical_sum_outer (a : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (g : ℕ → ℝ) :
    kernelIFPhysicalSum a q g = gapKeys g q.1 +
      ((q.2.2.1 : ℕ) - (q.1 : ℝ)) / a +
        gapKeys (fun j => g (j + q.2.2.1)) (k - q.2.2.1) := by
  have htk : (q.2.2.1 : ℕ) ≤ k := by have := q.2.2.1.isLt; omega
  simp only [Nat.add_comm _ (q.2.2.1 : ℕ), gapKeys_shift, Nat.add_sub_of_le htk,
    kernelIFPhysicalSum]

/-- The reward can be retained as one coupled outer-block weight; it is not
assumed to factor into two independent endpoint tests. -/
theorem kernel_IF_physical_sum_coord_measurable (a : ℝ) {k : ℕ}
    (q : FluxFacetIndex k) :
    Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))]
      (kernelIFPhysicalSum a q) := by
  let _ : MeasurableSpace (ℕ → ℝ) := kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))
  rw [show kernelIFPhysicalSum a q = fun g => gapKeys g q.1 +
    ((q.2.2.1 : ℕ) - (q.1 : ℝ)) / a +
      gapKeys (fun j => g (j + q.2.2.1)) (k - q.2.2.1) from
        funext (kernel_IF_physical_sum_outer a q)]
  unfold gapKeys
  have hpre : Measurable (fun g : ℕ → ℝ => ∑ j ∈ Finset.range (q.1 : ℕ), g j) := by
    exact Finset.measurable_sum _ fun j hj => kill_measurable_coord
      (Or.inl (Finset.mem_range.mp hj))
  have htail : Measurable (fun g : ℕ → ℝ =>
      ∑ j ∈ Finset.range (k - q.2.2.1), g (j + q.2.2.1)) := by
    exact Finset.measurable_sum _ fun j _ => kill_measurable_coord
      (Or.inr (show (q.2.2.1 : ℕ) ≤ j + q.2.2.1 by omega))
  exact (hpre.add measurable_const).add htail

theorem kernel_IF_reward_coord_measurable {η M : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (ν : ProbabilityMeasure ℝ) (C a : ℝ) {k : ℕ}
    (q : FluxFacetIndex k) :
    Measurable[kCoordSigma (Iio (q.1 : ℕ) ∪ Ici (q.2.2.1 : ℕ))]
      (fun g => kernelBoundaryReward ν C ψ (kernelIFPhysicalSum a q g)) :=
  (measurable_kernelBoundaryReward hψ ν C).comp (kernel_IF_physical_sum_coord_measurable a q)

theorem kernel_IF_physical_sum_nonneg {a : ℝ} (ha : 0 < a) {k : ℕ}
    {q : FluxFacetIndex k} (hq : fluxFacetValid q) {g : ℕ → ℝ}
    (hg : ∀ j < k, 0 ≤ g j) : 0 ≤ kernelIFPhysicalSum a q g := by
  have htk : (q.2.2.1 : ℕ) ≤ k := by have := q.2.2.1.isLt; omega
  rw [kernel_IF_physical_sum_outer]
  apply add_nonneg
  · apply add_nonneg
    · exact Finset.sum_nonneg fun j hj => hg j (by
        have := Finset.mem_range.mp hj; have := hq.1; have := hq.2; omega)
    · apply div_nonneg _ ha.le
      exact sub_nonneg.mpr (by exact_mod_cast (lt_trans hq.1 hq.2).le)
  · exact Finset.sum_nonneg fun j hj => hg (j + q.2.2.1) (by
      have := Finset.mem_range.mp hj; omega)

/-- The physical sum has the exact outer-residual representation, including
zero-length outer blocks. -/
theorem kernel_IF_physical_sum_residual {a : ℝ} (ha : a ≠ 0) (b : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (g : ℕ → ℝ) :
    a * kernelIFPhysicalSum a q g = (k : ℝ) +
      kWalk b (-1) (-a) (kernelReversePrefix g q.1) q.1 -
      kWalk b 1 a (fun j => g (j + q.2.2.1)) (k - q.2.2.1) := by
  have htk : (q.2.2.1 : ℕ) ≤ k := by have := q.2.2.1.isLt; omega
  have hrev : gapKeys (kernelReversePrefix g q.1) q.1 = gapKeys g q.1 :=
    Finset.sum_range_reflect g q.1
  rw [kernel_IF_physical_sum_outer]
  unfold kWalk
  rw [hrev, Nat.cast_sub htk]
  field_simp
  ring

/-- The actual coupled reward is controlled by the same exponential time
weight on every surviving pair of outer rows. -/
theorem kernel_IF_reward_le_time {D θ vlo vhi η M C a b w : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η / C ≤ θ / 4) (ha : 0 < a) {k : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) {g : ℕ → ℝ} (hg : ∀ j < k, 0 ≤ g j)
    (hleft : krAlive (Icc 0 w) (-1) (-a) q.1 b (kernelReversePrefix g q.1) = 1)
    (hright : krAlive (Icc 0 w) 1 a (k - q.2.2.1) b
      (fun j => g (j + q.2.2.1)) = 1) :
    |kernelBoundaryReward ν C ψ (kernelIFPhysicalSum a q g)| ≤
      M * (8 * D / θ ^ 2) / C * Real.exp (η * ((k : ℝ) + w) / (a * C)) := by
  have hleft' := (kernel_krAlive_eq_one_iff _ _ _ _ _ _).mp hleft _ le_rfl
  have hright' := (kernel_krAlive_eq_one_iff _ _ _ _ _ _).mp hright _ le_rfl
  exact kernelBoundaryReward_le_of_residual hν hθ hψ hη hC hscale
    (kernel_IF_physical_sum_nonneg ha hq hg) ha hleft'.2 hright'.1
    (kernel_IF_physical_sum_residual ha.ne' b q g)

end
end PGM
