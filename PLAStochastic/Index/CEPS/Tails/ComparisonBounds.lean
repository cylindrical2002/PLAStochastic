import PLAStochastic.Index.CEPS.Tails.DriftOccupation
import PLAStochastic.Index.CEPS.Tails.DrawupTail

/-!
# Marked occupation comparisons on actual paths

This module links localized actual-pair integrals to the path comparisons and
Cramér bounds. Marks have norm at most one for every `Re t ≥ 0`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset WienerHopf

/-- Marked occupation of the actual positive outer event, including short prefixes. -/
def cepsPositiveOccupationTerm (ν : ProbabilityMeasure ℝ) (eps δ : ℝ) (t : ℂ) (k : ℕ) : ℂ :=
  ∫ g, {g | cepsPositiveOuter eps δ g k}.indicator
    (fun g => Complex.exp (-t * gapKeys g k)) g ∂(iidLaw ν)

/-- `E[e^{-tS_k}; τ_l > k]` for the actual drift-`δ` drawup. -/
def cepsDrawupOccupationTerm (ν : ProbabilityMeasure ℝ) (δ l : ℝ) (t : ℂ) (k : ℕ) : ℂ :=
  ∫ g, {g | cepsDrawupOK (1 + δ) 1 l g k}.indicator
    (fun g => Complex.exp (-t * gapKeys g k)) g ∂(iidLaw ν)

/-- The actual marked drawup occupation, including time zero. -/
def cepsDrawupOccupation (ν : ProbabilityMeasure ℝ) (δ l : ℝ) (t : ℂ) : ℂ :=
  ∑' k, cepsDrawupOccupationTerm ν δ l t k

/-- Positive certificate drift is exactly the lower-slope cutoff used in S-7(a). -/
theorem cepsCertDrift_ge_iff {eps δ : ℝ} (hδ : 0 < 1 + δ) {g : ℕ → ℝ}
    (hg : ∀ n, 0 < g n) {k i j : ℕ} (hij : (i, j) ∈ certPairs eps k) :
    δ ≤ cepsCertDrift eps (gapKeys g) i j ↔ certSlope eps (gapKeys g) i j ≤ 1 / (1 + δ) := by
  obtain ⟨hij, hj, hL⟩ := mem_certPairs.mp hij
  have hden : 0 < (j : ℝ) - i - 2 * eps := by linarith
  have hsum : 0 < gapKeys g j - gapKeys g i :=
    sub_pos.mpr (cert_gapKeys_lt (fun n _ => hg n) i j hij hj)
  rw [cepsCertDrift, le_sub_iff_add_le, le_div_iff₀ hden, certSlope,
    div_le_div_iff₀ hsum hδ]
  ring_nf

/-- Negative certificate drift is exactly the upper-slope cutoff used in S-7(b). -/
theorem cepsCertDrift_lt_neg_iff {eps δ : ℝ} (hδ : δ < 1) {g : ℕ → ℝ}
    (hg : ∀ n, 0 < g n) {k i j : ℕ} (hij : (i, j) ∈ certPairs eps k) :
    cepsCertDrift eps (gapKeys g) i j < -δ ↔ 1 / (1 - δ) < certSlope eps (gapKeys g) i j := by
  obtain ⟨hij, hj, hL⟩ := mem_certPairs.mp hij
  have hden : 0 < (j : ℝ) - i - 2 * eps := by linarith
  have hsum : 0 < gapKeys g j - gapKeys g i :=
    sub_pos.mpr (cert_gapKeys_lt (fun n _ => hg n) i j hij hj)
  rw [cepsCertDrift, sub_lt_iff_lt_add, div_lt_iff₀ hden, certSlope,
    div_lt_div_iff₀ (by linarith : 0 < 1 - δ) hsum]
  ring_nf

/-- Certificate drifts belong to the actual drift domain. -/
theorem cepsCertDrift_gt_neg_one {eps : ℝ} {g : ℕ → ℝ} (hg : ∀ n, 0 < g n)
    {k i j : ℕ} (hij : (i, j) ∈ certPairs eps k) : -1 < cepsCertDrift eps (gapKeys g) i j := by
  obtain ⟨hij, hj, hL⟩ := mem_certPairs.mp hij
  have hpos : 0 < (gapKeys g j - gapKeys g i) / ((j : ℝ) - i - 2 * eps) :=
    div_pos (sub_pos.mpr (cert_gapKeys_lt (fun n _ => hg n) i j hij hj)) (by linarith)
  unfold cepsCertDrift
  linarith

theorem measurableSet_cepsPositiveOuter (eps δ : ℝ) (k : ℕ) :
    MeasurableSet {g | cepsPositiveOuter eps δ g k} := by
  by_cases hk : (k : ℝ) ≤ 2 * eps
  · have h : {g | cepsPositiveOuter eps δ g k} = univ := by ext g; simp [cepsPositiveOuter, hk]
    rw [h]
    exact MeasurableSet.univ
  · have h : {g | cepsPositiveOuter eps δ g k} = ⋃ ij ∈ certPairs eps k,
        {g : ℕ → ℝ | certOK eps (gapKeys g) k ij.1 ij.2} ∩
          {g | certSlope eps (gapKeys g) ij.1 ij.2 ≤ 1 / (1 + δ)} := by
      ext g
      simp only [cepsPositiveOuter, hk, false_or, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      aesop
    rw [h]
    exact Finset.measurableSet_biUnion _ fun ij _ =>
      (measurableSet_certOK eps k ij.1 ij.2).inter (measurableSet_le
        (measurable_const.div ((rawAsm_measurable_gapKeys ij.2).sub
          (rawAsm_measurable_gapKeys ij.1))) measurable_const)

/-- Reverse crossings are the complement of reflected drawup survival. -/
theorem measurableSet_cepsReverseCross (eps δ : ℝ) (k : ℕ) :
    MeasurableSet {g | cepsReverseCross eps δ g k} := by
  have heq : {g | cepsReverseCross eps δ g k} =
      {g | cepsDrawupOK (-(1 + δ)) (-1) (2 * eps * (1 + δ)) g k}ᶜ := by
    ext g
    simp only [mem_ofPred_eq, mem_compl_iff, cepsReverseCross, cepsDrawupOK]
    push Not
    have he : ∀ n, kWalk 0 (-(1 + δ)) (-1) g n = -kWalk 0 (1 + δ) 1 g n := by
      intro n
      unfold kWalk
      ring
    simp_rw [he]
    constructor
    · rintro ⟨i, hi, j, hj, hij, hlt⟩
      exact ⟨i, j, hij, hj, by linarith⟩
    · rintro ⟨i, j, hij, hj, hlt⟩
      exact ⟨i, by omega, j, hj, hij, by linarith⟩
  rw [heq]
  exact (measurableSet_cepsDrawupOK _ _ _ k).compl

theorem CepsGapDensity.integrable_marked_event {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D : ℝ} (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) :
    Integrable (A.indicator (fun g => Complex.exp (-t * gapKeys g k))) (iidLaw ν) := by
  refine ((integrable_const (1 : ℝ)).mono'
    (measurable_cexp_gapKeys t k).aestronglyMeasurable
    (hf.ae_gapKeys_nonneg.mono fun g hg => norm_cexp_neg_mul_le_one ht (hg k))).indicator hA

/-- The localized negative occupation has the required crossing probability bound. -/
theorem CepsGapDensity.norm_negativeOccupation_le {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D eps δ : ℝ} (hf : CepsGapDensity ν f D) (hδ : δ < 1) {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) :
    ‖cepsDriftOccupationTerm ν eps (Ioo (-1) (-δ)) t k‖ ≤
      (iidLaw ν).real {g | ¬ cepsDrawupOK (1 - δ) 1 (2 * eps * (1 - δ)) g k} := by
  unfold cepsDriftOccupationTerm
  refine (norm_integral_le_of_norm_le ((integrable_const (1 : ℝ)).indicator
    (measurableSet_cepsDrawupOK (1 - δ) 1 (2 * eps * (1 - δ)) k).compl) ?_).trans (le_of_eq ?_)
  · filter_upwards [hf.ae_iidLaw_pos] with g hg
    by_cases h : cepsDriftEvent eps (Ioo (-1) (-δ)) g k
    · obtain ⟨ij, hij, hc, hd⟩ := h
      have hn := not_cepsDrawupOK_of_negativeOuter hδ hg
        (show cepsNegativeOuter eps δ g k from
          ⟨ij, hij, hc, (cepsCertDrift_lt_neg_iff hδ hg hij).mp hd.2⟩)
      rw [indicator_of_mem (show g ∈ {g | cepsDriftEvent eps (Ioo (-1) (-δ)) g k}
        from ⟨ij, hij, hc, hd⟩), indicator_of_mem (show g ∈ {g | cepsDrawupOK (1 - δ) 1 (2 * eps * (1 - δ)) g k}ᶜ from hn)]
      exact norm_cexp_neg_mul_le_one ht (gapKeys_nonneg (fun n => (hg n).le) k)
    · rw [indicator_of_notMem (show g ∉ {g | cepsDriftEvent eps (Ioo (-1) (-δ)) g k} from h), norm_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
  · rw [integral_indicator (measurableSet_cepsDrawupOK (1 - δ) 1 (2 * eps * (1 - δ)) k).compl,
      setIntegral_const, smul_eq_mul, mul_one]
    rfl

/-- The positive outer occupation differs from drawup only on a reverse crossing. -/
theorem CepsGapDensity.norm_positiveOccupation_sub_drawup_le {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D eps δ : ℝ} (hf : CepsGapDensity ν f D) (hδ : 0 < 1 + δ)
    {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) :
    ‖cepsPositiveOccupationTerm ν eps δ t k -
      cepsDrawupOccupationTerm ν δ (2 * eps * (1 + δ)) t k‖ ≤
      (iidLaw ν).real {g | cepsReverseCross eps δ g k} := by
  unfold cepsPositiveOccupationTerm cepsDrawupOccupationTerm
  rw [← integral_sub (hf.integrable_marked_event ht k (measurableSet_cepsPositiveOuter eps δ k))
    (hf.integrable_marked_event ht k (measurableSet_cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) k))]
  refine (norm_integral_le_of_norm_le ((integrable_const (1 : ℝ)).indicator
    (measurableSet_cepsReverseCross eps δ k)) ?_).trans (le_of_eq ?_)
  · filter_upwards [hf.ae_iidLaw_pos] with g hg
    by_cases hp : cepsPositiveOuter eps δ g k
    · have hd := cepsDrawupOK_of_positiveOuter hδ hg hp
      rw [indicator_of_mem (show g ∈ {g | cepsPositiveOuter eps δ g k} from hp), indicator_of_mem (show g ∈ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd), sub_self, norm_zero]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
    · by_cases hd : cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k
      · have hr := cepsReverseCross_of_drawup_not_positive hδ hg hd hp
        rw [indicator_of_notMem (show g ∉ {g | cepsPositiveOuter eps δ g k} from hp), indicator_of_mem (show g ∈ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd), indicator_of_mem (show g ∈ {g | cepsReverseCross eps δ g k} from hr), zero_sub, norm_neg]
        exact norm_cexp_neg_mul_le_one ht (gapKeys_nonneg (fun n => (hg n).le) k)
      · rw [indicator_of_notMem (show g ∉ {g | cepsPositiveOuter eps δ g k} from hp), indicator_of_notMem (show g ∉ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd), sub_self, norm_zero]
        exact indicator_nonneg (fun _ _ => zero_le_one) _
  · rw [integral_indicator (measurableSet_cepsReverseCross eps δ k), setIntegral_const,
      smul_eq_mul, mul_one]

/-- At late times the positive comparison error is bounded by drawup survival itself. -/
theorem CepsGapDensity.norm_positiveOccupation_sub_drawup_le_survival {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D eps δ : ℝ} (hf : CepsGapDensity ν f D) (hδ : 0 < 1 + δ)
    {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) :
    ‖cepsPositiveOccupationTerm ν eps δ t k -
      cepsDrawupOccupationTerm ν δ (2 * eps * (1 + δ)) t k‖ ≤
      (iidLaw ν).real {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} := by
  unfold cepsPositiveOccupationTerm cepsDrawupOccupationTerm
  rw [← integral_sub (hf.integrable_marked_event ht k (measurableSet_cepsPositiveOuter eps δ k))
    (hf.integrable_marked_event ht k (measurableSet_cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) k))]
  refine (norm_integral_le_of_norm_le ((integrable_const (1 : ℝ)).indicator
    (measurableSet_cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) k)) ?_).trans (le_of_eq ?_)
  · filter_upwards [hf.ae_iidLaw_pos] with g hg
    by_cases hp : cepsPositiveOuter eps δ g k
    · have hd := cepsDrawupOK_of_positiveOuter hδ hg hp
      rw [indicator_of_mem (show g ∈ {g | cepsPositiveOuter eps δ g k} from hp), indicator_of_mem (show g ∈ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd), sub_self, norm_zero, indicator_of_mem (show g ∈ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd)]
      exact zero_le_one
    · by_cases hd : cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k
      · rw [indicator_of_notMem (show g ∉ {g | cepsPositiveOuter eps δ g k} from hp), indicator_of_mem (show g ∈ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd), zero_sub, norm_neg, indicator_of_mem (show g ∈ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd)]
        exact norm_cexp_neg_mul_le_one ht (gapKeys_nonneg (fun n => (hg n).le) k)
      · rw [indicator_of_notMem (show g ∉ {g | cepsPositiveOuter eps δ g k} from hp), indicator_of_notMem (show g ∉ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd), sub_self, norm_zero, indicator_of_notMem (show g ∉ {g | cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) g k} from hd)]
  · rw [integral_indicator (measurableSet_cepsDrawupOK (1 + δ) 1 (2 * eps * (1 + δ)) k), setIntegral_const,
      smul_eq_mul, mul_one]

end

end PGM
