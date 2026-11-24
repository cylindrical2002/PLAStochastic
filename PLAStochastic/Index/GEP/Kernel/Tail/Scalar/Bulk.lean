import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.Summation

/-! # Genuine outer weights and finite marked-pair tail sums -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1200000

/-- The exact two-endpoint exterior Green weight in the scalar IF formula. -/
def kernelOuterWeight (ν : ProbabilityMeasure ℝ) (w a : ℝ) : ℝ :=
  (∑' n : ℕ, krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) n 0) *
    (∑' n : ℕ, krSurv (Icc 0 w) (ν : Measure ℝ) 1 a n 0) +
  (∑' n : ℕ, krSurv (Icc 0 w) (ν : Measure ℝ) (-1) (-a) n w) *
    (∑' n : ℕ, krSurv (Icc 0 w) (ν : Measure ℝ) 1 a n w)

theorem kernelOuterWeight_nonneg (ν : ProbabilityMeasure ℝ) (w a : ℝ) :
    0 ≤ kernelOuterWeight ν w a := by
  apply add_nonneg <;> apply mul_nonneg <;> exact tsum_nonneg (fun n => krSurv_nonneg measurableSet_Icc ν _ _ n _)

theorem measurable_kernel_surv_param {X : Type*} [MeasurableSpace X]
    (ν : ProbabilityMeasure ℝ) {J : Set ℝ} (hJ : MeasurableSet J)
    {β a y : X → ℝ} (hβ : Measurable β) (ha : Measurable a) (hy : Measurable y) (n : ℕ) :
    Measurable (fun p => krSurv J (ν : Measure ℝ) (β p) (a p) n (y p)) := by
  simp_rw [krSurv_eq_integral hJ ν]
  exact (measurable_krAlive_param hJ (hβ.comp measurable_fst) (ha.comp measurable_fst)
    (hy.comp measurable_fst) measurable_snd n).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_kernelOuterWeight (ν : ProbabilityMeasure ℝ) (w : ℝ) :
    Measurable (kernelOuterWeight ν w) := by
  unfold kernelOuterWeight
  apply Measurable.add <;> apply Measurable.mul <;> apply Measurable.tsum <;>
    intro n <;> apply measurable_kernel_surv_param ν measurableSet_Icc <;> fun_prop

/-- Both actual exterior directions have summable Green series, and their
product has fixed width powers at both ends of the slope range. -/
theorem kernel_regLaw_outer_weight_bound (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ Ks Kl : ℝ, 0 < Ks ∧ 0 < Kl ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w a : ℝ, 1 ≤ w → 0 < a →
        kernelOuterWeight ν w a ≤ if a ≤ 1 / 2 then Ks * w ^ 2 else Kl * w ^ 6 := by
  obtain ⟨Ks, hKs, hsmall⟩ := kernel_regLaw_outer_green_small D θ vlo vhi hθ hvlo hv
  obtain ⟨Kl, hKl, hlarge⟩ := kernel_regLaw_outer_green_large D θ vlo vhi (1 / 2)
    hD hθ hvlo hv (by norm_num)
  refine ⟨2 * Ks ^ 2, 2 * Kl ^ 2, by positivity, by positivity, ?_⟩
  intro ν hν w a hw ha
  by_cases halo : a ≤ 1 / 2
  · rw [if_pos halo]
    have hp (y : ℝ) := (hsmall ν hν 0 w a hw ha halo 1 a (Or.inl ⟨rfl, rfl⟩) y).2
    have hm (y : ℝ) := (hsmall ν hν 0 w a hw ha halo (-1) (-a) (Or.inr ⟨rfl, rfl⟩) y).2
    simp only [zero_add] at hp hm
    have hprod (y : ℝ) := mul_le_mul (hm y) (hp y)
      (tsum_nonneg fun n => krSurv_nonneg (J := Icc 0 w) measurableSet_Icc ν 1 a n y)
      (show 0 ≤ Ks * w by positivity)
    have hh := add_le_add (hprod 0) (hprod w)
    exact hh.trans_eq (by ring)
  · rw [if_neg halo]
    have hp (y : ℝ) := (hlarge ν hν 0 w 1 a hw (by rw [abs_of_pos ha]; linarith) y).2
    have hm (y : ℝ) := (hlarge ν hν 0 w (-1) (-a) hw (by rw [abs_neg, abs_of_pos ha]; linarith) y).2
    simp only [zero_add] at hp hm
    have hprod (y : ℝ) := mul_le_mul (hm y) (hp y)
      (tsum_nonneg fun n => krSurv_nonneg (J := Icc 0 w) measurableSet_Icc ν 1 a n y)
      (show 0 ≤ Kl * w ^ 3 by positivity)
    have hh := add_le_add (hprod 0) (hprod w)
    exact hh.trans_eq (by ring)

/-- Finite absolute IF budget for one orientation. The other pin's reward is
the majorant `M+w` for either exact linear facet coefficient. -/
def kernelPairTailSum (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w a t y z : ℝ)
    (L R M : ℕ) : ℝ :=
  ∑ l ∈ Finset.range L, ∑ r ∈ Finset.range R, ∑ m ∈ Finset.range M,
    (((m : ℝ) + 1 + w) *
      (kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z *
        krDens (Icc 0 w) ν f 1 a (m + 1) z y))

theorem kernelPairTailSum_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (a t y z : ℝ) (L R M : ℕ) :
    0 ≤ kernelPairTailSum ν f w a t y z L R M := by
  apply Finset.sum_nonneg
  intro l hl
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (by positivity) (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _)
    (krDens_nonneg ν hf0 _ _ _))

theorem measurable_kernelPairTailSum (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (w t y z : ℝ) (L R M : ℕ) :
    Measurable (fun a => kernelPairTailSum ν f w a t y z L R M) := by
  apply Finset.measurable_sum
  intro l hl
  apply Finset.measurable_sum
  intro r hr
  apply Finset.measurable_sum
  intro m hm
  exact measurable_const.mul
    ((measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf measurable_const measurable_id
      measurable_const measurable_const measurable_const l r).mul
      (measurable_krDens_param ν measurableSet_Icc hf measurable_const measurable_id
        measurable_const measurable_const (m + 1)))

/-- A full marked-pair exponential bound immediately controls its genuine
three-index finite absolute IF budget. -/
theorem kernelPairTailSum_le_of_exp (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    {w a t y z u C : ℝ} (hw : 0 ≤ w) (hu : 0 < u) (hC : 0 ≤ C)
    (hb : ∀ l r m : ℕ, kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z *
      krDens (Icc 0 w) ν f 1 a (m + 1) z y ≤
        C * Real.exp (-u * ((l : ℝ) + r + (m + 1)))) (L R M : ℕ) :
    kernelPairTailSum ν f w a t y z L R M ≤ C * ((2 + w) * (1 + 1 / u) ^ 4) := by
  have hh : kernelPairTailSum ν f w a t y z L R M ≤ C *
      (∑ l ∈ Finset.range L, ∑ r ∈ Finset.range R, ∑ m ∈ Finset.range M,
        (((m : ℝ) + 1 + w) * Real.exp (-u * ((l : ℝ) + r + (m + 1))))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro m hm
    have hm' := mul_le_mul_of_nonneg_left (hb l r m) (show 0 ≤ (m : ℝ) + 1 + w by positivity)
    exact hm'.trans_eq (by ring)
  exact hh.trans (mul_le_mul_of_nonneg_left (kernel_triple_exp_sum_le hu hw L R M) hC)

end
end PGM
