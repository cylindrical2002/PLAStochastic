import PLAStochastic.Index.CEPS.Tails.ComparisonBounds
import PLAStochastic.Index.CEPS.Actual.Main

/-!
# Occupation-series identities for the outer drift domains

The positive actual-pair integral includes the deterministic short prefix.
The drawup occupation is absolutely convergent, and both series use the actual
key mark `exp(-t S_k)` for the whole half-plane `Re t ≥ 0`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter WienerHopf

/-- Every certificate has length exceeding the deterministic short prefix. -/
theorem not_cepsDriftEvent_of_short {eps : ℝ} {g : ℕ → ℝ} {E : Set ℝ} {k : ℕ}
    (hk : (k : ℝ) ≤ 2 * eps) : ¬ cepsDriftEvent eps E g k := by
  rintro ⟨⟨i, j⟩, hij, -, -⟩
  obtain ⟨-, hj, hL⟩ := mem_certPairs.mp hij
  have hj' : (j : ℝ) ≤ k := by exact_mod_cast hj
  linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]

/-- One positive occupation term is the short-prefix term plus the localized actual layer. -/
theorem CepsGapDensity.cepsPositiveOccupationTerm_eq {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D eps δ : ℝ} (hf : CepsGapDensity ν f D) (heps : 0 < eps)
    (hδ : 0 < 1 + δ) {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) :
    cepsPositiveOccupationTerm ν eps δ t k =
      (if k ≤ ⌊2 * eps⌋₊ then cepsLaplace ν t ^ k else 0) +
        cepsDriftOccupationTerm ν eps (Ici δ) t k := by
  by_cases hk : k ≤ ⌊2 * eps⌋₊
  · have hk' : (k : ℝ) ≤ 2 * eps := cast_le_two_mul_of_le_floor heps.le le_rfl hk
    have hp : {g | cepsPositiveOuter eps δ g k} = univ := by
      ext g
      simp [cepsPositiveOuter, hk']
    have hz : cepsDriftOccupationTerm ν eps (Ici δ) t k = 0 := by
      unfold cepsDriftOccupationTerm
      have he : {g | cepsDriftEvent eps (Ici δ) g k} = ∅ := by
        ext g
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact not_cepsDriftEvent_of_short hk'
      rw [he]
      simp
    rw [if_pos hk, hz, add_zero, cepsPositiveOccupationTerm, hp, indicator_univ]
    exact integral_cexp_partialSum (hf.integrable_cexp ht) k
  · have hk' : ¬ (k : ℝ) ≤ 2 * eps := by
      intro h
      exact hk (Nat.le_floor h)
    rw [if_neg hk, zero_add]
    unfold cepsPositiveOccupationTerm cepsDriftOccupationTerm
    refine integral_congr_ae ?_
    filter_upwards [hf.ae_iidLaw_pos] with g hg
    have he : cepsPositiveOuter eps δ g k ↔ cepsDriftEvent eps (Ici δ) g k := by
      simp only [cepsPositiveOuter, hk', false_or, cepsDriftEvent, mem_Ici]
      constructor
      · rintro ⟨ij, hij, hc, hs⟩
        exact ⟨ij, hij, hc, (cepsCertDrift_ge_iff hδ hg hij).mpr hs⟩
      · rintro ⟨ij, hij, hc, hs⟩
        exact ⟨ij, hij, hc, (cepsCertDrift_ge_iff hδ hg hij).mp hs⟩
    by_cases h : cepsPositiveOuter eps δ g k
    · rw [indicator_of_mem (show g ∈ {g | cepsPositiveOuter eps δ g k} from h),
        indicator_of_mem (show g ∈ {g | cepsDriftEvent eps (Ici δ) g k} from he.mp h)]
    · rw [indicator_of_notMem (show g ∉ {g | cepsPositiveOuter eps δ g k} from h),
        indicator_of_notMem (show g ∉ {g | cepsDriftEvent eps (Ici δ) g k} from fun h' => h (he.mpr h'))]

/-- Positive outer occupation is exactly the short prefix plus the actual positive pair integral. -/
theorem CepsGapDensity.hasSum_cepsPositiveOccupation {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D eps δ : ℝ} (hf : CepsGapDensity ν f D) (heps : 0 < eps)
    (hδ : 0 < 1 + δ) (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤)
    (hT : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ)) (iidLaw ν))
    {t : ℂ} (ht : 0 ≤ t.re) :
    HasSum (cepsPositiveOccupationTerm ν eps δ t)
      ((∑ k ∈ Finset.range (⌊2 * eps⌋₊ + 1), cepsLaplace ν t ^ k) +
        ∫ μ in Ici δ, cepsActualPair ν f eps t μ) := by
  have hsub : Ici δ ⊆ Ioi (-1 : ℝ) := fun μ hμ => by
    simp only [mem_Ici, mem_Ioi] at hμ ⊢
    linarith
  have hs := hf.hasSum_cepsDriftOccupation heps hfin hT measurableSet_Ici hsub ht
  have hfinite : Summable (fun k : ℕ => if k ≤ ⌊2 * eps⌋₊ then cepsLaplace ν t ^ k else 0) :=
    summable_of_ne_finset_zero (s := Finset.range (⌊2 * eps⌋₊ + 1)) fun k hk =>
      if_neg (fun h => hk (Finset.mem_range.mpr (by omega)))
  have hfsum : ∑' k : ℕ, (if k ≤ ⌊2 * eps⌋₊ then cepsLaplace ν t ^ k else 0) =
      ∑ k ∈ Finset.range (⌊2 * eps⌋₊ + 1), cepsLaplace ν t ^ k := by
    rw [tsum_eq_sum (s := Finset.range (⌊2 * eps⌋₊ + 1)) fun k hk =>
      if_neg (fun h => hk (Finset.mem_range.mpr (by omega)))]
    exact Finset.sum_congr rfl fun k hk => if_pos (by have := Finset.mem_range.mp hk; omega)
  rw [← hfsum]
  convert hfinite.hasSum.add hs using 1
  ext k
  exact hf.cepsPositiveOccupationTerm_eq heps hδ ht k

/-- An event mark is dominated by the probability of that event. -/
theorem CepsGapDensity.norm_marked_event_le {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D : ℝ} (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) :
    ‖∫ g, A.indicator (fun g => Complex.exp (-t * gapKeys g k)) g ∂(iidLaw ν)‖ ≤
      (iidLaw ν).real A := by
  refine (norm_integral_le_of_norm_le ((integrable_const (1 : ℝ)).indicator hA) ?_).trans
    (le_of_eq ?_)
  · filter_upwards [hf.ae_gapKeys_nonneg] with g hg
    by_cases h : g ∈ A
    · rw [indicator_of_mem h, indicator_of_mem h]
      exact norm_cexp_neg_mul_le_one ht (hg k)
    · rw [indicator_of_notMem h, indicator_of_notMem h, norm_zero]
  · rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]

/-- Drawup occupation terms are bounded by drawup survival probabilities. -/
theorem CepsGapDensity.norm_cepsDrawupOccupationTerm_le {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D δ l : ℝ} (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) :
    ‖cepsDrawupOccupationTerm ν δ l t k‖ ≤
      (iidLaw ν).real {g | cepsDrawupOK (1 + δ) 1 l g k} :=
  hf.norm_marked_event_le ht k (measurableSet_cepsDrawupOK _ _ _ k)

/-- The actual marked drawup occupation converges absolutely over the whole right half-plane. -/
theorem summable_norm_cepsDrawupOccupation_of_regLaw {ν : ProbabilityMeasure ℝ}
    {D θ vlo vhi δ l : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D)
    (hvlo : 0 < vlo) (hδ : 0 < δ) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {t : ℂ} (ht : 0 ≤ t.re) : Summable (fun k => ‖cepsDrawupOccupationTerm ν δ l t k‖) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 * l / δ)
  have hN' : 2 * l ≤ δ * N / 2 := by
    have hh := (div_le_iff₀ hδ).mp hN
    nlinarith
  have htail := (summable_cepsDrawupOK_tail_of_regLaw hν hθ hD hvlo hδ N hN').1
  have htailSame : Summable (fun k => (iidLaw ν).real
      {g | cepsDrawupOK (1 + δ) 1 l g (k + N)}) := by
    simpa only [Nat.add_comm] using htail
  have htail' : Summable (fun k => ‖cepsDrawupOccupationTerm ν δ l t (k + N)‖) :=
    htailSame.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => hf.norm_cepsDrawupOccupationTerm_le ht (k + N))
  exact (summable_nat_add_iff N).mp htail'

end

end PGM
