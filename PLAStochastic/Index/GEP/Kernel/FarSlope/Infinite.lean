import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.Infinite
import PLAStochastic.Index.GEP.Kernel.FarSlope.FixedUniform

/-! # Infinite actual scalar IF outside a fixed saddle neighborhood -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 1400000

/-- An integrable constant at the lower slope end and the actual inverse
square at the upper end give a uniform complete slope budget. -/
theorem kernel_slope_integral_of_two_bounds {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ a, 0 ≤ F a) {Cs Cl : ℝ} (_hCs : 0 ≤ Cs) (_hCl : 0 ≤ Cl)
    (hsmall : ∀ a ∈ Ioc (0 : ℝ) (1 / 2), F a ≤ Cs)
    (hlarge : ∀ a ∈ Ioi (1 / 2 : ℝ), F a ≤ Cl * a⁻¹ ^ 2) :
    IntegrableOn F (Ioi (0 : ℝ)) ∧
      (∫ a in Ioi (0 : ℝ), F a) ≤ Cs / 2 + 2 * Cl := by
  have hIs : IntegrableOn F (Ioc (0 : ℝ) (1 / 2)) := by
    refine (integrableOn_const (s := Ioc (0 : ℝ) (1 / 2)) (C := Cs) (by simp)).mono'
      hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF a)] using hsmall a ha
  have hIl : IntegrableOn F (Ioi (1 / 2 : ℝ)) := by
    refine (kernel_integrable_inverse_square_half.const_mul Cl).mono' hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF a)] using hlarge a ha
  have hsplit : Ioc (0 : ℝ) (1 / 2) ∪ Ioi (1 / 2) = Ioi 0 := by
    ext a
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨h, _⟩ | h) <;> linarith
    · intro ha
      by_cases hh : a ≤ 1 / 2
      · exact Or.inl ⟨ha, hh⟩
      · exact Or.inr (not_le.mp hh)
  have hdis : Disjoint (Ioc (0 : ℝ) (1 / 2)) (Ioi (1 / 2)) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact (not_lt.mpr ha.2) hb
  have hIf : IntegrableOn F (Ioi (0 : ℝ)) := by rw [← hsplit]; exact hIs.union hIl
  refine ⟨hIf, ?_⟩
  rw [← hsplit, setIntegral_union hdis measurableSet_Ioi hIs hIl]
  have hsi : (∫ a in Ioc (0 : ℝ) (1 / 2), F a) ≤ Cs / 2 := by
    have hh := integral_mono_ae hIs (integrableOn_const (C := Cs) (by simp))
      (show ∀ᵐ a ∂volume.restrict (Ioc (0 : ℝ) (1 / 2)), F a ≤ Cs by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
        exact hsmall a ha)
    apply hh.trans_eq
    simp only [integral_const, smul_eq_mul]
    norm_num
    ring
  have hli : (∫ a in Ioi (1 / 2 : ℝ), F a) ≤ 2 * Cl := by
    have hh := integral_mono_ae hIl (kernel_integrable_inverse_square_half.const_mul Cl)
      (show ∀ᵐ a ∂volume.restrict (Ioi (1 / 2 : ℝ)), F a ≤ Cl * a⁻¹ ^ 2 by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact hlarge a ha)
    apply hh.trans_eq
    rw [integral_const_mul, kernel_integral_inverse_square_half]
    ring
  linarith

def kernelFarPairTailSum (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (δ w a t y z : ℝ)
    (L R M : ℕ) : ℝ :=
  if δ ≤ |a - 1| then kernelPairTailSum ν f w a t y z L R M else 0

theorem kernelFarPairTailSum_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (δ a t y z : ℝ) (L R M : ℕ) :
    0 ≤ kernelFarPairTailSum ν f δ w a t y z L R M := by
  unfold kernelFarPairTailSum
  split_ifs
  · exact kernelPairTailSum_nonneg ν hf0 hw a t y z L R M
  · rfl

theorem measurable_kernelFarPairTailSum (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (δ w t y z : ℝ) (L R M : ℕ) :
    Measurable (fun a => kernelFarPairTailSum ν f δ w a t y z L R M) :=
  Measurable.ite (measurableSet_le measurable_const ((measurable_id.sub measurable_const).abs))
    (measurable_kernelPairTailSum ν hf w t y z L R M) measurable_const

/-- Every finite actual random-length rectangle, with both exterior Green
products, is exponentially small outside the fixed saddle neighborhood. -/
theorem kernel_regLaw_far_bulk_budget (D θ vlo vhi δ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ lam c K : ℝ, 0 < lam ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w t : ℝ, 1 ≤ w → 0 ≤ t →
      ∀ y z : ℝ, ((y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) →
      ∀ L R M : ℕ, ∀ a : ℝ, 0 < a →
        kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z L R M ≤
          (if a ≤ 1 / 2 then K else K * a⁻¹ ^ 2) * w ^ 16 * Real.exp (lam * t - c * w) := by
  obtain ⟨lam, c, B, hlam, hc, hB, hpair⟩ :=
    kernel_regLaw_full_pair_far_width D θ vlo vhi δ hD hθ hvlo hv hδ hδhi
  obtain ⟨Os, Ol, hOs, hOl, houter⟩ := kernel_regLaw_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  let K := (Os + Ol) * B * (3 * (1 + 1 / c) ^ 4)
  have hK : 0 < K := by positivity
  refine ⟨lam, c, K, hlam, hc, hK, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w t hw ht y z hyz L R M a ha
  have hw0 : 0 ≤ w := by linarith
  unfold kernelFarPairTailSum
  by_cases haway : δ ≤ |a - 1|
  · rw [if_pos haway]
    have hp (l r m : ℕ) : kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z *
        krDens (Icc 0 w) ν f 1 a (m + 1) z y ≤
        ((if a ≤ 1 / 2 then B else B * a⁻¹ ^ 2) * Real.exp (lam * t - c * w)) *
          Real.exp (-c * ((l : ℝ) + r + (m + 1))) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hpair ν hν f hf hf0 hfD hfz hfe hνf w a t hw ha haway ht y z hyz l r (m + 1) (by omega)
    have hcoef : 0 ≤ (if a ≤ 1 / 2 then B else B * a⁻¹ ^ 2) * Real.exp (lam * t - c * w) := by
      split_ifs <;> positivity
    have hh := kernelPairTailSum_le_of_exp ν f hw0 hc hcoef hp L R M
    have ht' : (2 + w) * (1 + 1 / c) ^ 4 ≤ 3 * (1 + 1 / c) ^ 4 * w := by
      have hh := mul_le_mul_of_nonneg_right (show 2 + w ≤ 3 * w by linarith) (show 0 ≤ (1 + 1 / c) ^ 4 by positivity)
      exact hh.trans_eq (by ring)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left ht' hcoef)
    have ho := houter ν hν w a hw ha
    by_cases halo : a ≤ 1 / 2
    · rw [if_pos halo] at ho hh' ⊢
      have hh'' := mul_le_mul ho hh' (kernelPairTailSum_nonneg ν hf0 hw0 a t y z L R M) (by positivity)
      have hw16 : w ^ 3 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
      have hlast : Os * B * (3 * (1 + 1 / c) ^ 4) * w ^ 3 * Real.exp (lam * t - c * w) ≤
          K * w ^ 16 * Real.exp (lam * t - c * w) := by
        dsimp [K]
        gcongr
        linarith
      apply hh''.trans
      convert hlast using 1 <;> first | rfl | ring
    · rw [if_neg halo] at ho hh' ⊢
      have hh'' := mul_le_mul ho hh' (kernelPairTailSum_nonneg ν hf0 hw0 a t y z L R M) (by positivity)
      have hw16 : w ^ 7 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
      have hlast : (Ol * B * (3 * (1 + 1 / c) ^ 4)) * a⁻¹ ^ 2 * w ^ 7 * Real.exp (lam * t - c * w) ≤
          (K * a⁻¹ ^ 2) * w ^ 16 * Real.exp (lam * t - c * w) := by
        dsimp [K]
        gcongr
        linarith
      apply hh''.trans
      convert hlast using 1 <;> first | rfl | ring
  · rw [if_neg haway, mul_zero]
    split_ifs <;> positivity

/-- Complete positive-slope integration preserves the far width exponential. -/
theorem kernel_regLaw_far_bulk_integral (D θ vlo vhi δ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ lam c K : ℝ, 0 < lam ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w t : ℝ, 1 ≤ w → 0 ≤ t →
      ∀ y z : ℝ, ((y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) →
      ∀ L R M : ℕ,
        IntegrableOn (fun a => kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z L R M) (Ioi 0) ∧
        (∫ a in Ioi (0 : ℝ), kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z L R M) ≤
          K * w ^ 16 * Real.exp (lam * t - c * w) := by
  obtain ⟨lam, c, K, hlam, hc, hK, hb⟩ := kernel_regLaw_far_bulk_budget D θ vlo vhi δ hD hθ hvlo hv hδ hδhi
  refine ⟨lam, c, 5 * K / 2, hlam, hc, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w t hw ht y z hyz L R M
  have hF (a : ℝ) : 0 ≤ kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z L R M :=
    mul_nonneg (kernelOuterWeight_nonneg ν w a) (kernelFarPairTailSum_nonneg ν hf0 (by linarith) δ a t y z L R M)
  have hFm := (measurable_kernelOuterWeight ν w).mul (measurable_kernelFarPairTailSum ν hf δ w t y z L R M)
  let C := K * w ^ 16 * Real.exp (lam * t - c * w)
  have hC : 0 ≤ C := by positivity
  have hsmall (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) (1 / 2)) :
      kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z L R M ≤ C := by
    simpa only [if_pos ha.2] using hb ν hν f hf hf0 hfD hfz hfe hνf w t hw ht y z hyz L R M a ha.1
  have hlarge (a : ℝ) (ha : a ∈ Ioi (1 / 2 : ℝ)) :
      kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z L R M ≤ C * a⁻¹ ^ 2 := by
    have ha' : (1 / 2 : ℝ) < a := ha
    have hh := hb ν hν f hf hf0 hfD hfz hfe hνf w t hw ht y z hyz L R M a (by linarith)
    rw [if_neg (not_le.mpr ha')] at hh
    exact hh.trans_eq (by dsimp [C]; ring)
  obtain ⟨hi, hh⟩ := kernel_slope_integral_of_two_bounds hFm hF hC hC hsmall hlarge
  exact ⟨hi, hh.trans_eq (by dsimp [C]; ring)⟩

def kernelFarBulkTailTerm (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (δ w t y z a : ℝ)
    (p : ℕ × ℕ × ℕ) : ℝ :=
  if δ ≤ |a - 1| then kernelBulkTailTerm ν f w t y z a p else 0

theorem kernelFarBulkTailTerm_cube (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (δ t y z a : ℝ) (N : ℕ) :
    (∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)),
      ENNReal.ofReal (kernelFarBulkTailTerm ν f δ w t y z a p)) =
        ENNReal.ofReal (kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z N N N) := by
  by_cases ha : δ ≤ |a - 1|
  · simpa only [kernelFarBulkTailTerm, kernelFarPairTailSum, if_pos ha] using kernelBulkTailTerm_cube ν hf0 hw t y z a N
  · simp [kernelFarBulkTailTerm, kernelFarPairTailSum, ha]

/-- The actual infinite marked-pair IF at every slope outside a fixed saddle
neighborhood. This includes both extreme slope ends and has a uniform width
exponential before choosing any logarithmic input window. -/
theorem kernel_regLaw_far_bulk_infinite (D θ vlo vhi δ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ lam c K : ℝ, 0 < lam ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w t : ℝ, 1 ≤ w → 0 ≤ t →
      ∀ y z : ℝ, ((y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) →
        (∫⁻ a in Ioi (0 : ℝ), ∑' p : ℕ × ℕ × ℕ,
          ENNReal.ofReal (kernelFarBulkTailTerm ν f δ w t y z a p)) ≤
            ENNReal.ofReal (K * w ^ 16 * Real.exp (lam * t - c * w)) := by
  obtain ⟨lam, c, K, hlam, hc, hK, hb⟩ := kernel_regLaw_far_bulk_integral D θ vlo vhi δ hD hθ hvlo hv hδ hδhi
  refine ⟨lam, c, K, hlam, hc, hK, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w t hw ht y z hyz
  let F : ℕ → ℝ → ℝ≥0∞ := fun N a =>
    ∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)),
      ENNReal.ofReal (kernelFarBulkTailTerm ν f δ w t y z a p)
  have hw0 : 0 ≤ w := by linarith
  have hFE (N : ℕ) (a : ℝ) : F N a = ENNReal.ofReal
      (kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z N N N) :=
    kernelFarBulkTailTerm_cube ν hf0 hw0 δ t y z a N
  have hFm (N : ℕ) : Measurable (F N) := by
    have he : F N = fun a => ENNReal.ofReal
        (kernelOuterWeight ν w a * kernelFarPairTailSum ν f δ w a t y z N N N) := funext (hFE N)
    rw [he]
    exact ((measurable_kernelOuterWeight ν w).mul (measurable_kernelFarPairTailSum ν hf δ w t y z N N N)).ennreal_ofReal
  have hFmono : Monotone F := by
    intro N M hNM a
    exact Finset.sum_le_sum_of_subset (Finset.product_subset_product (Finset.range_mono hNM)
      (Finset.product_subset_product (Finset.range_mono hNM) (Finset.range_mono hNM)))
  simp_rw [kernel_ennreal_triple_eq_iSup_cube]
  change (∫⁻ a in Ioi (0 : ℝ), ⨆ N : ℕ, F N a) ≤ _
  rw [lintegral_iSup hFm hFmono]
  apply iSup_le
  intro N
  obtain ⟨hI, hB⟩ := hb ν hν f hf hf0 hfD hfz hfe hνf w t hw ht y z hyz N N N
  simp_rw [hFE]
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun a => mul_nonneg (kernelOuterWeight_nonneg ν w a)
      (kernelFarPairTailSum_nonneg ν hf0 hw0 δ a t y z N N N))]
  exact ENNReal.ofReal_le_ofReal hB

end
end PGM
