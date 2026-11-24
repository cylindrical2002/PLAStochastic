import PLAStochastic.Index.GEP.SurvivalBound.Certificate.Geometry
import PLAStochastic.Index.GEP.RawDisc.Defs

/-!
# WP4 `SurvivalBound`: null ties and the certificate decomposition of the survival indicator

Source: `research/2026-09-28-gep-closure/analytic-response.md` §2 (the maximizing pair of AR (4) is
a.s. unique; AR (5)); task P1, target 3 of `research/2026-09-30-lean-gep-direct-term/task-cert.md`.

* **Null hyperplanes** (`cert_infinitePi_linear_null`, `cert_wordLaw_linear_null`): under a
  product law whose coordinate `m` is absolutely continuous, the level set
  `{g | ∑_{l ∈ T} c_l g_l = d}` of a linear form with `c_m ≠ 0` is null.  The coordinate `c_m g_m`
  is independent of the rest `Y = ∑_{l ≠ m} c_l g_l` (`iIndepFun_infinitePi`), so the level set
  has measure `∫ μ_m {x | c_m x = d - y} d(law Y)(y) = 0`, a Lebesgue-null point for each `y`.
* **Ties are linear forms** (`cert_tie_sub_eq_sum`, coefficients `certTieCoef`): for admissible
  pairs `(i, j) ≠ (i', j')` the tie difference
  `(j - i - 2ε)(p_{j'} - p_{i'}) - (j' - i' - 2ε)(p_j - p_i)` is `∑_{l < k} c_l g_l` with a nonzero
  coefficient on the symmetric difference of `[i, j)` and `[i', j')`
  (`cert_exists_tieCoef_ne_zero`), hence a.s. nonzero under `wordLaw ν σ S` (`cert_ae_noTie`).
* **Decomposition of the survival indicator** (`cert_indicator_ae_eq_sum`): if `ν, σ` are
  absolutely continuous and supported on `(0, ∞)` (so that the gaps are a.s. positive,
  `cert_ae_pos_wordLaw`), then for `2ε < k`, `wordLaw ν σ S`-a.e.
  `1{k < T} F = ∑_{(i,j) ∈ certPairs eps k} 1{certOK eps (gapKeys g) k i j} F`
  (`cert_indicator_one_ae_eq_sum` for `F = 1`); at most one term is nonzero, since a.s. at most
  one admissible pair is a certificate (`cert_ae_certOK_unique`); integrated form
  `cert_integral_indicator_eq_sum`.
* The certificate events are measurable (`measurableSet_certOK`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset

/-! ## Null level sets of linear forms under product laws -/

/-- **A linear level set is null** under a product of probability laws whose coordinate `m` is
absolutely continuous, when the form has a nonzero coefficient at `m`. -/
theorem cert_infinitePi_linear_null {μ : ℕ → Measure ℝ} [∀ l, IsProbabilityMeasure (μ l)]
    {T : Finset ℕ} {c : ℕ → ℝ} {m : ℕ} (hm : m ∈ T) (hcm : c m ≠ 0) (hac : μ m ≪ volume)
    (d : ℝ) :
    Measure.infinitePi μ {g : ℕ → ℝ | ∑ l ∈ T, c l * g l = d} = 0 := by
  have hind : iIndepFun (fun l (g : ℕ → ℝ) => c l * g l) (Measure.infinitePi μ) :=
    (iIndepFun_infinitePi (P := μ) (X := fun _ x => x) fun _ => measurable_id).comp
      (fun l x => c l * x) fun l => measurable_const.mul measurable_id
  have hmeas : ∀ l, Measurable fun g : ℕ → ℝ => c l * g l :=
    fun l => measurable_const.mul (measurable_pi_apply l)
  have hsum := hind.indepFun_finsetSum_of_notMem hmeas (Finset.notMem_erase m T)
  have hYfun : (∑ l ∈ T.erase m, fun g : ℕ → ℝ => c l * g l) =
      fun g => ∑ l ∈ T.erase m, c l * g l := by
    funext g
    exact Finset.sum_apply g _ _
  rw [hYfun] at hsum
  have hY : Measurable fun g : ℕ → ℝ => ∑ l ∈ T.erase m, c l * g l :=
    Finset.measurable_sum _ fun l _ => hmeas l
  have hV := hmeas m
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hV.aemeasurable).1 hsum
  have hq : MeasurableSet {q : ℝ × ℝ | q.1 + q.2 = d} :=
    measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const
  have hset : {g : ℕ → ℝ | ∑ l ∈ T, c l * g l = d} =
      (fun g : ℕ → ℝ => (∑ l ∈ T.erase m, c l * g l, c m * g m)) ⁻¹'
        {q : ℝ × ℝ | q.1 + q.2 = d} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← Finset.sum_erase_add T _ hm]
  rw [hset, ← Measure.map_apply (hY.prodMk hV) hq, hmap, Measure.prod_apply hq]
  have hzero : ∀ y : ℝ, ((Measure.infinitePi μ).map fun g : ℕ → ℝ => c m * g m)
      (Prod.mk y ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = d}) = 0 := by
    intro y
    rw [Measure.map_apply hV (measurable_prodMk_left hq)]
    have e : (fun g : ℕ → ℝ => c m * g m) ⁻¹' (Prod.mk y ⁻¹' {q : ℝ × ℝ | q.1 + q.2 = d}) =
        (fun g : ℕ → ℝ => g m) ⁻¹' {(d - y) / c m} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      rw [eq_div_iff hcm]
      constructor <;> intro h <;> linarith [mul_comm (g m) (c m)]
    rw [e, ← Measure.map_apply (measurable_pi_apply m) (measurableSet_singleton _),
      Measure.infinitePi_map_eval]
    exact hac (Real.volume_singleton)
  simp only [hzero, lintegral_zero]

/-- **Null hyperplanes under a word law.**  If `ν` and `σ` are absolutely continuous, every level
set of a linear form of finitely many coordinates with some nonzero coefficient is
`wordLaw ν σ S`-null. -/
theorem cert_wordLaw_linear_null {ν σ : ProbabilityMeasure ℝ} (hν : (ν : Measure ℝ) ≪ volume)
    (hσ : (σ : Measure ℝ) ≪ volume) (S : Finset ℕ) {T : Finset ℕ} {c : ℕ → ℝ} {m : ℕ}
    (hm : m ∈ T) (hcm : c m ≠ 0) (d : ℝ) :
    wordLaw ν σ S {g : ℕ → ℝ | ∑ l ∈ T, c l * g l = d} = 0 := by
  unfold wordLaw
  refine cert_infinitePi_linear_null hm hcm ?_ d
  by_cases h : m ∈ S
  · simpa only [h, if_true] using hσ
  · simpa only [h, if_false] using hν

/-- Under a word law with coordinate laws supported on `(0, ∞)` all gaps are a.s. positive. -/
theorem cert_ae_pos_wordLaw {ν σ : ProbabilityMeasure ℝ} (hν : (ν : Measure ℝ) (Set.Iic 0) = 0)
    (hσ : (σ : Measure ℝ) (Set.Iic 0) = 0) (S : Finset ℕ) :
    ∀ᵐ g ∂(wordLaw ν σ S), ∀ l, 0 < g l := by
  rw [ae_all_iff]
  intro l
  have hl : (((if l ∈ S then σ else ν : ProbabilityMeasure ℝ)) : Measure ℝ) (Set.Iic 0) = 0 := by
    by_cases h : l ∈ S
    · simpa only [h, if_true] using hσ
    · simpa only [h, if_false] using hν
  have hm := (measurePreserving_eval_infinitePi (fun i : ℕ =>
    (((if i ∈ S then σ else ν : ProbabilityMeasure ℝ)) : Measure ℝ)) l).measure_preimage
      (s := Set.Iic 0) measurableSet_Iic.nullMeasurableSet
  rw [hl] at hm
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hm] with g hg
  simpa using hg

/-! ## Ties as linear forms of the gaps -/

/-- The coefficient of the gap `g l` in the tie difference of the pairs `(i, j)` and `(i', j')`:
`(j - i - 2ε) 1{l ∈ [i', j')} - (j' - i' - 2ε) 1{l ∈ [i, j)}`. -/
def certTieCoef (eps : ℝ) (i j i' j' l : ℕ) : ℝ :=
  ((j : ℝ) - i - 2 * eps) * (if i' ≤ l ∧ l < j' then 1 else 0) -
    ((j' : ℝ) - i' - 2 * eps) * (if i ≤ l ∧ l < j then 1 else 0)

/-- A key difference as a linear form of the first `k` gaps. -/
theorem cert_gapKeys_sub_eq_sum (g : ℕ → ℝ) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    gapKeys g j - gapKeys g i = ∑ l ∈ range k, (if i ≤ l ∧ l < j then 1 else 0) * g l := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have e : (range k).filter (fun l => i ≤ l ∧ l < j) = Ico i j := by
    ext l
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [e, Finset.sum_Ico_eq_sub _ hij]
  rfl

/-- The tie difference of two pairs of `[0, k]` is the linear form `∑_{l < k} certTieCoef · g l`. -/
theorem cert_tie_sub_eq_sum (eps : ℝ) (g : ℕ → ℝ) {i j i' j' k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hij' : i' ≤ j') (hj'k : j' ≤ k) :
    ((j : ℝ) - i - 2 * eps) * (gapKeys g j' - gapKeys g i') -
        ((j' : ℝ) - i' - 2 * eps) * (gapKeys g j - gapKeys g i) =
      ∑ l ∈ range k, certTieCoef eps i j i' j' l * g l := by
  rw [cert_gapKeys_sub_eq_sum g hij hjk, cert_gapKeys_sub_eq_sum g hij' hj'k, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold certTieCoef
  ring

/-- Two distinct admissible pairs have a gap of `[0, k)` with nonzero tie coefficient (a point of
the symmetric difference of `[i, j)` and `[i', j')`). -/
theorem cert_exists_tieCoef_ne_zero {eps : ℝ} {k i j i' j' : ℕ} (hij : i < j) (hjk : j ≤ k)
    (hL : 2 * eps < (j : ℝ) - i) (hij' : i' < j') (hj'k : j' ≤ k)
    (hL' : 2 * eps < (j' : ℝ) - i') (hne : (i, j) ≠ (i', j')) :
    ∃ m ∈ range k, certTieCoef eps i j i' j' m ≠ 0 := by
  have hN : ((j : ℝ) - i - 2 * eps) ≠ 0 := by
    intro h
    linarith
  have hN' : ((j' : ℝ) - i' - 2 * eps) ≠ 0 := by
    intro h
    linarith
  rcases lt_trichotomy i i' with h | rfl | h
  · refine ⟨i, mem_range.2 (by omega), ?_⟩
    rw [certTieCoef, if_neg (by omega), if_pos ⟨le_rfl, hij⟩]
    intro h0
    apply hN'
    linarith
  · rcases lt_trichotomy j j' with h' | rfl | h'
    · refine ⟨j, mem_range.2 (by omega), ?_⟩
      rw [certTieCoef, if_pos ⟨hij.le, h'⟩, if_neg (by omega)]
      intro h0
      apply hN
      linarith
    · exact absurd rfl hne
    · refine ⟨j', mem_range.2 (by omega), ?_⟩
      rw [certTieCoef, if_neg (by omega), if_pos ⟨hij'.le, h'⟩]
      intro h0
      apply hN'
      linarith
  · refine ⟨i', mem_range.2 (by omega), ?_⟩
    rw [certTieCoef, if_pos ⟨le_rfl, hij'⟩, if_neg (by omega)]
    intro h0
    apply hN
    linarith

/-- **Null ties.**  If `ν` and `σ` are absolutely continuous then, `wordLaw ν σ S`-a.s., no two
distinct admissible pairs of `[0, k]` tie. -/
theorem cert_ae_noTie {ν σ : ProbabilityMeasure ℝ} (hν : (ν : Measure ℝ) ≪ volume)
    (hσ : (σ : Measure ℝ) ≪ volume) (S : Finset ℕ) (eps : ℝ) (k : ℕ) :
    ∀ᵐ g ∂(wordLaw ν σ S), ∀ ij ∈ certPairs eps k, ∀ ij' ∈ certPairs eps k, ij ≠ ij' →
      ((ij.2 : ℝ) - ij.1 - 2 * eps) * (gapKeys g ij'.2 - gapKeys g ij'.1) ≠
        ((ij'.2 : ℝ) - ij'.1 - 2 * eps) * (gapKeys g ij.2 - gapKeys g ij.1) := by
  rw [eventually_all_finset]
  rintro ⟨i, j⟩ hij
  rw [eventually_all_finset]
  rintro ⟨i', j'⟩ hij'
  obtain ⟨h1, h2, h3⟩ := mem_certPairs.1 hij
  obtain ⟨h1', h2', h3'⟩ := mem_certPairs.1 hij'
  by_cases hne : (i, j) = (i', j')
  · exact Eventually.of_forall fun _ h => absurd hne h
  obtain ⟨m, hm, hcm⟩ := cert_exists_tieCoef_ne_zero h1 h2 h3 h1' h2' h3' hne
  have hnull := cert_wordLaw_linear_null hν hσ S hm hcm 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with g hg _ heq
  apply hg
  show ∑ l ∈ range k, certTieCoef eps i j i' j' l * g l = 0
  rw [← cert_tie_sub_eq_sum eps g h1.le h2 h1'.le h2']
  exact sub_eq_zero.2 heq

/-! ## Measurability of the certificate events -/

/-- The certificate events `{g | certOK eps (gapKeys g) k i j}` are measurable. -/
theorem measurableSet_certOK (eps : ℝ) (k i j : ℕ) :
    MeasurableSet {g : ℕ → ℝ | certOK eps (gapKeys g) k i j} := by
  have hK : ∀ t, Measurable fun g : ℕ → ℝ => gapKeys g t :=
    fun t => (measurable_pi_apply t).comp measurable_gapKeys
  have ha : Measurable fun g : ℕ → ℝ => certSlope eps (gapKeys g) i j :=
    measurable_const.div ((hK j).sub (hK i))
  have hD : ∀ t, Measurable fun g : ℕ → ℝ =>
      certResid (certSlope eps (gapKeys g) i j) (gapKeys g) t -
        certResid (certSlope eps (gapKeys g) i j) (gapKeys g) i := fun t => by
    unfold certResid
    exact (measurable_const.sub (ha.mul (hK t))).sub (measurable_const.sub (ha.mul (hK i)))
  have e : {g : ℕ → ℝ | certOK eps (gapKeys g) k i j} =
      ⋂ t ∈ range (k + 1),
        ({g : ℕ → ℝ | 0 ≤ certResid (certSlope eps (gapKeys g) i j) (gapKeys g) t -
            certResid (certSlope eps (gapKeys g) i j) (gapKeys g) i} ∩
          {g : ℕ → ℝ | certResid (certSlope eps (gapKeys g) i j) (gapKeys g) t -
            certResid (certSlope eps (gapKeys g) i j) (gapKeys g) i ≤ 2 * eps}) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff, mem_range, certOK,
      certBand]
    exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩
  rw [e]
  exact Finset.measurableSet_biInter _ fun t _ =>
    (measurableSet_le measurable_const (hD t)).inter (measurableSet_le (hD t) measurable_const)

/-! ## The certificate decomposition of the survival indicator -/

/-- **A.s. uniqueness of the certificate.**  If `ν, σ` are absolutely continuous and supported on
`(0, ∞)`, then `wordLaw ν σ S`-a.s. at most one admissible pair of `[0, k]` is a certificate. -/
theorem cert_ae_certOK_unique {ν σ : ProbabilityMeasure ℝ} (hνac : (ν : Measure ℝ) ≪ volume)
    (hσac : (σ : Measure ℝ) ≪ volume) (hνpos : (ν : Measure ℝ) (Set.Iic 0) = 0)
    (hσpos : (σ : Measure ℝ) (Set.Iic 0) = 0) (S : Finset ℕ) (eps : ℝ) (k : ℕ) :
    ∀ᵐ g ∂(wordLaw ν σ S), ∀ ij ∈ certPairs eps k, ∀ ij' ∈ certPairs eps k,
      certOK eps (gapKeys g) k ij.1 ij.2 → certOK eps (gapKeys g) k ij'.1 ij'.2 → ij = ij' := by
  filter_upwards [cert_ae_pos_wordLaw hνpos hσpos S, cert_ae_noTie hνac hσac S eps k]
    with g hpos htie
  have hp := cert_gapKeys_lt (k := k) fun l _ => hpos l
  rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' hok hok'
  by_contra hne
  obtain ⟨h1, h2, -⟩ := mem_certPairs.1 hij
  obtain ⟨h1', h2', -⟩ := mem_certPairs.1 hij'
  exact htie (i, j) hij (i', j') hij' hne (cert_tie hp h1 h2 h1' h2' hok hok')

/-- **Certificate decomposition of the survival indicator** (AR (5)).  If `ν, σ` are absolutely
continuous and supported on `(0, ∞)` and `2ε < k`, then `wordLaw ν σ S`-a.e.
`1{k < T} F = ∑_{(i,j) ∈ certPairs eps k} 1{certOK eps (gapKeys g) k i j} F`: on the survival event
exactly one admissible pair is a certificate, off it none is. -/
theorem cert_indicator_ae_eq_sum {ν σ : ProbabilityMeasure ℝ} (hνac : (ν : Measure ℝ) ≪ volume)
    (hσac : (σ : Measure ℝ) ≪ volume) (hνpos : (ν : Measure ℝ) (Set.Iic 0) = 0)
    (hσpos : (σ : Measure ℝ) (Set.Iic 0) = 0) (S : Finset ℕ) {eps : ℝ} {k : ℕ}
    (hk : 2 * eps < k) {M : Type*} [AddCommMonoid M] (F : (ℕ → ℝ) → M) :
    ∀ᵐ g ∂(wordLaw ν σ S), {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator F g =
      ∑ ij ∈ certPairs eps k, {g : ℕ → ℝ | certOK eps (gapKeys g) k ij.1 ij.2}.indicator F g := by
  filter_upwards [cert_ae_pos_wordLaw hνpos hσpos S,
    cert_ae_certOK_unique hνac hσac hνpos hσpos S eps k] with g hpos huniq
  by_cases hT : (k : ℕ∞) < gapSegLen eps g
  · rw [Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from hT)]
    obtain ⟨i, j, hij, hjk, hL, hok⟩ := (cert_lt_gapSegLen_iff hk fun l _ => hpos l).1 hT
    have hmem : (i, j) ∈ certPairs eps k := mem_certPairs.2 ⟨hij, hjk, hL⟩
    rw [Finset.sum_eq_single_of_mem (i, j) hmem]
    · exact (Set.indicator_of_mem
        (show g ∈ {g : ℕ → ℝ | certOK eps (gapKeys g) k (i, j).1 (i, j).2} from hok) F).symm
    · intro ij' hmem' hne
      exact Set.indicator_of_notMem (fun hok' => hne (huniq ij' hmem' (i, j) hmem hok' hok)) F
  · rw [Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from hT)]
    symm
    exact Finset.sum_eq_zero fun ij _ =>
      Set.indicator_of_notMem (fun hok => hT (cert_lt_gapSegLen_of_certOK hok)) F

/-- The decomposition for the plain survival indicator:
`1{k < T} = ∑_{(i,j)} 1{certOK eps (gapKeys g) k i j}` a.e. -/
theorem cert_indicator_one_ae_eq_sum {ν σ : ProbabilityMeasure ℝ}
    (hνac : (ν : Measure ℝ) ≪ volume) (hσac : (σ : Measure ℝ) ≪ volume)
    (hνpos : (ν : Measure ℝ) (Set.Iic 0) = 0) (hσpos : (σ : Measure ℝ) (Set.Iic 0) = 0)
    (S : Finset ℕ) {eps : ℝ} {k : ℕ} (hk : 2 * eps < k) :
    ∀ᵐ g ∂(wordLaw ν σ S), {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator 1 g =
      ∑ ij ∈ certPairs eps k,
        {g : ℕ → ℝ | certOK eps (gapKeys g) k ij.1 ij.2}.indicator (1 : (ℕ → ℝ) → ℝ) g :=
  cert_indicator_ae_eq_sum hνac hσac hνpos hσpos S hk 1

/-- **Certificate decomposition, integrated.**  Under the hypotheses of
`cert_indicator_ae_eq_sum`, for integrable `F` the survival integral splits over the admissible
pairs. -/
theorem cert_integral_indicator_eq_sum {ν σ : ProbabilityMeasure ℝ}
    (hνac : (ν : Measure ℝ) ≪ volume) (hσac : (σ : Measure ℝ) ≪ volume)
    (hνpos : (ν : Measure ℝ) (Set.Iic 0) = 0) (hσpos : (σ : Measure ℝ) (Set.Iic 0) = 0)
    (S : Finset ℕ) {eps : ℝ} {k : ℕ} (hk : 2 * eps < k) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : (ℕ → ℝ) → E} (hF : Integrable F (wordLaw ν σ S)) :
    ∫ g, {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator F g ∂(wordLaw ν σ S) =
      ∑ ij ∈ certPairs eps k,
        ∫ g, {g : ℕ → ℝ | certOK eps (gapKeys g) k ij.1 ij.2}.indicator F g ∂(wordLaw ν σ S) := by
  rw [integral_congr_ae (cert_indicator_ae_eq_sum hνac hσac hνpos hσpos S hk F),
    integral_finsetSum]
  exact fun ij _ => hF.indicator (measurableSet_certOK eps k ij.1 ij.2)

end

end PGM
