import PLAStochastic.Index.CEPS.Tails.LocalCertificate

/-!
# Actual occupation localized in certificate drift

For a measurable drift domain `E ⊆ (-1,∞)`, the integral of the actual pair is
exactly the marked occupation of those surviving prefixes whose unique
minimal-slope certificate has drift in `E`. The identity uses the actual pair,
not an abstract comparison kernel.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset

/-- The surviving prefix has a certificate whose drift is in `E`. -/
def cepsDriftEvent (eps : ℝ) (E : Set ℝ) (g : ℕ → ℝ) (k : ℕ) : Prop :=
  ∃ ij ∈ certPairs eps k, certOK eps (gapKeys g) k ij.1 ij.2 ∧
    cepsCertDrift eps (gapKeys g) ij.1 ij.2 ∈ E

/-- The marked occupation term with a specified certificate-drift domain. -/
def cepsDriftOccupationTerm (ν : ProbabilityMeasure ℝ) (eps : ℝ) (E : Set ℝ) (t : ℂ) (k : ℕ) : ℂ :=
  ∫ g, {g | cepsDriftEvent eps E g k}.indicator
    (fun g => Complex.exp (-t * gapKeys g k)) g ∂(iidLaw ν)

theorem measurableSet_cepsDriftEvent (eps : ℝ) {E : Set ℝ} (hE : MeasurableSet E) (k : ℕ) :
    MeasurableSet {g | cepsDriftEvent eps E g k} := by
  have heq : {g | cepsDriftEvent eps E g k} = ⋃ ij ∈ certPairs eps k,
      {g : ℕ → ℝ | certOK eps (gapKeys g) k ij.1 ij.2} ∩
        (fun g => cepsCertDrift eps (gapKeys g) ij.1 ij.2) ⁻¹' E := by
    ext g
    simp only [cepsDriftEvent, mem_ofPred_eq, mem_iUnion, mem_inter_iff, Set.mem_preimage]
    aesop
  rw [heq]
  exact Finset.measurableSet_biUnion _ fun ij _ =>
    (measurableSet_certOK eps k ij.1 ij.2).inter
      (hE.preimage (measurable_cepsCertDrift eps ij.1 ij.2))

/-- The localized integral of a layer equals the corresponding certificate sum. -/
theorem CepsGapDensity.integral_cepsLayerSum_drift_eq_sum {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) {eps : ℝ} (heps : 0 < eps)
    {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Ioi (-1 : ℝ)) {t : ℂ} (ht : 0 ≤ t.re)
    (k : ℕ) :
    ∫ μ in E, cepsLayerSum ν f eps t k μ =
      ∑ ij ∈ certPairs eps k, ∫ g,
        {g' : ℕ → ℝ | certOK eps (gapKeys g') k ij.1 ij.2}.indicator (fun _ => (1 : ℂ)) g *
          Complex.exp (-t * gapKeys g k) *
          E.indicator (fun _ => (1 : ℂ)) (cepsCertDrift eps (gapKeys g) ij.1 ij.2) ∂(iidLaw ν) := by
  have hinter : Ioi (-1 : ℝ) ∩ E = E := inter_eq_right.mpr hsub
  unfold cepsLayerSum
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    (hf.integrableOn_cepsTripleTerm heps ht i (j - i) (k - j)).mono_set hsub]
  simp_rw [integral_finsetSum _ fun i _ =>
    (hf.integrableOn_cepsTripleTerm heps ht i _ _).mono_set hsub]
  set P : ℕ × ℕ → Prop := fun ij => ij.1 < ij.2 ∧ 2 * eps < (ij.2 : ℝ) - ij.1
  have hcp : certPairs eps k = (Finset.range (k + 1) ×ˢ Finset.range (k + 1)).filter P := rfl
  rw [hcp, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : j + 1 ≤ k + 1)) ?_]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
    have hcast : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by rw [Nat.cast_sub hij]
    by_cases hL : 2 * eps < ((j - i : ℕ) : ℝ)
    · have hP : P (i, j) := by
        refine ⟨?_, by rw [← hcast]; exact hL⟩
        by_contra h
        have : j - i = 0 := by omega
        rw [this] at hL
        simp at hL
        linarith
      rw [if_pos hP, ← hinter, ← hf.integral_cert_drift_set heps hL ht hE]
      have e1 : i + (j - i) + (k - j) = k := by omega
      have e2 : i + (j - i) = j := by omega
      rw [e1, e2, hinter]
    · have hP : ¬ P (i, j) := fun h => hL (by rw [hcast]; exact h.2)
      rw [if_neg hP]
      exact setIntegral_eq_zero_of_forall_eq_zero fun μ hμ =>
        hf.cepsTripleTerm_eq_zero t (not_lt.mp hL) (hsub hμ)
  · intro i _ hi
    have hji : j < i := by have := Finset.mem_range.not.mp hi; omega
    rw [if_neg fun h => by have := h.1; omega]

/-- Almost-sure certificate uniqueness localizes the indicator decomposition. -/
theorem CepsGapDensity.cepsDriftEvent_indicator_ae {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) (eps : ℝ) (E : Set ℝ) (k : ℕ)
    (F : (ℕ → ℝ) → ℂ) :
    ∀ᵐ g ∂(iidLaw ν), {g | cepsDriftEvent eps E g k}.indicator F g =
      ∑ ij ∈ certPairs eps k,
        {g' : ℕ → ℝ | certOK eps (gapKeys g') k ij.1 ij.2}.indicator (fun _ => (1 : ℂ)) g *
          F g * E.indicator (fun _ => (1 : ℂ)) (cepsCertDrift eps (gapKeys g) ij.1 ij.2) := by
  have huniq := cert_ae_certOK_unique hf.absolutelyContinuous hf.absolutelyContinuous
    hf.measure_Iic_zero hf.measure_Iic_zero ∅ eps k
  simp only [wordLaw_self] at huniq
  filter_upwards [huniq] with g hu
  by_cases h : cepsDriftEvent eps E g k
  · obtain ⟨ij, hij, hc, hd⟩ := h
    rw [indicator_of_mem (show g ∈ {g | cepsDriftEvent eps E g k} from ⟨ij, hij, hc, hd⟩),
      Finset.sum_eq_single_of_mem ij hij]
    · rw [indicator_of_mem hc, indicator_of_mem hd, one_mul, mul_one]
    · intro ij' hij' hne
      rw [indicator_of_notMem (show ¬ certOK eps (gapKeys g) k ij'.1 ij'.2 from
        fun hc' => hne (hu ij' hij' ij hij hc' hc)), zero_mul, zero_mul]
  · rw [indicator_of_notMem (show g ∉ {g | cepsDriftEvent eps E g k} from h)]
    symm
    refine Finset.sum_eq_zero fun ij hij => ?_
    by_cases hc : certOK eps (gapKeys g) k ij.1 ij.2
    · have hd : cepsCertDrift eps (gapKeys g) ij.1 ij.2 ∉ E :=
        fun hd => h ⟨ij, hij, hc, hd⟩
      rw [indicator_of_notMem hd, mul_zero]
    · rw [indicator_of_notMem hc, zero_mul, zero_mul]

/-- Every localized actual layer is a marked actual-prefix event. -/
theorem CepsGapDensity.integral_cepsLayerSum_drift {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) {eps : ℝ} (heps : 0 < eps)
    {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Ioi (-1 : ℝ)) {t : ℂ} (ht : 0 ≤ t.re)
    (k : ℕ) : ∫ μ in E, cepsLayerSum ν f eps t k μ = cepsDriftOccupationTerm ν eps E t k := by
  have hexp : Integrable (fun g : ℕ → ℝ => Complex.exp (-t * gapKeys g k)) (iidLaw ν) :=
    (integrable_const (1 : ℝ)).mono' (measurable_cexp_gapKeys t k).aestronglyMeasurable
      (hf.ae_gapKeys_nonneg.mono fun g hg => norm_cexp_neg_mul_le_one ht (hg k))
  rw [hf.integral_cepsLayerSum_drift_eq_sum heps hE hsub ht k]
  unfold cepsDriftOccupationTerm
  rw [integral_congr_ae (hf.cepsDriftEvent_indicator_ae eps E k _), integral_finsetSum]
  intro ij _
  have hset := (measurableSet_certOK eps k ij.1 ij.2).inter
    (hE.preimage (measurable_cepsCertDrift eps ij.1 ij.2))
  refine (hexp.indicator hset).congr (Eventually.of_forall fun g => ?_)
  by_cases hc : certOK eps (gapKeys g) k ij.1 ij.2 <;>
    by_cases hd : cepsCertDrift eps (gapKeys g) ij.1 ij.2 ∈ E <;> simp [hc, hd]

/-- The actual pair integral is the localized marked occupation series. -/
theorem CepsGapDensity.hasSum_cepsDriftOccupation {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) {eps : ℝ} (heps : 0 < eps)
    (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν))
    {E : Set ℝ} (hE : MeasurableSet E) (hsub : E ⊆ Ioi (-1 : ℝ)) {t : ℂ} (ht : 0 ≤ t.re) :
    HasSum (cepsDriftOccupationTerm ν eps E t) (∫ μ in E, cepsActualPair ν f eps t μ) := by
  have hsum := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict E) (F := fun k => cepsLayerSum ν f eps t k)
    (f := cepsActualPair ν f eps t) (fun k => cepsLayerReal ν f eps k)
    (fun k => ((hf.integrableOn_cepsLayerSum heps ht k).mono_set hsub).aestronglyMeasurable)
    (fun k => by
      filter_upwards [ae_restrict_mem hE] with μ hμ
      exact hf.norm_cepsLayerSum_le heps ht k (hsub hμ))
    (by
      filter_upwards [ae_restrict_mem hE] with μ hμ
      exact (hf.cepsActualPair_zero_eq heps (hsub hμ)).1)
    (by
      refine ((hf.integrableOn_norm_cepsActualPair_zero heps hfin hT).mono_set hsub).congr_fun
        (fun μ hμ => ?_) hE
      dsimp only
      rw [hf.norm_cepsActualPair_zero_eq heps μ, indicator_of_mem (hsub hμ)])
    (by
      filter_upwards [ae_restrict_mem hE] with μ hμ
      exact hf.hasSum_cepsLayerSum ht (hsub hμ))
  simpa only [hf.integral_cepsLayerSum_drift heps hE hsub ht] using hsum

end

end PGM
