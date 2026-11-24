import PLAStochastic.Index.LocalCount.RenewalMass
import PLAStochastic.Index.LocalCount.CyclicTwo
import PLAStochastic.Index.Endpoint.GammaClosure
import PLAStochastic.ForMathlib.Probability.LatticeConcentration.KestenUnconditional

/-!
# Local-count propagation: laws, decomposition and block independence

Source: `theory/proofs/proofK_local_count_core.tex` (`klc:thm:stopped-propagation`,
`klc:lem:cyclic-early-mark`).

* `LocalCountHyp P Z m θ B B₂`: `Z` is an iid pair sequence with counts `N ≥ 1`, the Gamma
  kernel, `E N = m > 0`, `E exp(θ N/m) ≤ B` and `E N² ≤ B₂ m²`.
  Consequences: the stop is almost surely finite (`LocalCountHyp.fin`), the gaps are almost
  surely positive (`LocalCountHyp.gap_pos`), shifts satisfy the same hypotheses
  (`LocalCountHyp.shift`), and `maximal_bernstein` applies (`LocalCountHyp.bernstein`).
* `cntLaw P Z` is the law of the count `N = (Z 0).2` on `ℤ` and
  `cntAtom P Z = lconc (cntLaw P Z) 1` its largest atom `p = sup_q P(N = q)`.
* `measure_pairRank_eq_convFin`, `measure_pairRank_seq_eq_convFin`:
  `P(S_t = k) = convFin t (law N) {k}` for `S_t = pairRank (seq Z ·) t = N₀ + ⋯ + N_{t-1}`.
* `measure_nextCount_eq_tsum` (decomposition): for `N⁺ = (nextLayer eps Z 0).2` and an almost
  surely finite stop `T = pairSegLen eps (seq Z ·)`, `P(N⁺ = k) = ∑' t, P(T = t ∧ S_t = k)`.
* `LocalCount.measure_past_inter_rank_le`, `LocalCount.measure_future_inter_rank_le` (half
  factorisation): an event of the first `r` pairs, or of the pairs from `r` on, meets
  `{S_{r+s} = k}` with probability at most its own probability times a bound on the atoms of the
  other half's count sum.

Generic helper lemmas live in the namespace `PLAStochastic.Index.LocalCount.Propagation`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset LocalCountBase
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × ℕ}

/-! ## Standing hypotheses and the count law -/

/-- The hypotheses of `klc:thm:stopped-propagation` on one layer: iid pairs, counts `N ≥ 1`,
the Gamma kernel, `E N = m > 0`, `E exp(θ N/m) ≤ B` and `E N² ≤ B₂ m²`. -/
structure LocalCountHyp (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) (m θ B B₂ : ℝ) : Prop where
  iid : IIDPairs P Z
  pos : ∀ᵐ ω ∂P, 1 ≤ (Z 0 ω).2
  gamma : GammaKernel P Z
  m_pos : 0 < m
  mean : ∫ ω, ((Z 0 ω).2 : ℝ) ∂P = m
  θ_pos : 0 < θ
  exp_int : Integrable (fun ω => Real.exp (θ * (Z 0 ω).2 / m)) P
  exp_le : ∫ ω, Real.exp (θ * (Z 0 ω).2 / m) ∂P ≤ B
  sq_int : Integrable (fun ω => ((Z 0 ω).2 : ℝ) ^ 2) P
  sq_le : ∫ ω, ((Z 0 ω).2 : ℝ) ^ 2 ∂P ≤ B₂ * m ^ 2

/-- The law of the count `N = (Z 0).2`, on `ℤ`. -/
def cntLaw (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : Measure ℤ :=
  P.map (fun ω => ((Z 0 ω).2 : ℤ))

/-- The largest atom `p = sup_q P(N = q)` of the count law. -/
def cntAtom (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : ℝ := lconc (cntLaw P Z) 1

namespace LocalCount

theorem measurable_intCast_snd : Measurable (fun x : ℝ × ℕ => ((x.2 : ℕ) : ℤ)) :=
  (Measurable.of_discrete (f := fun n : ℕ => (n : ℤ))).comp measurable_snd

theorem measurable_cnt {i : ℕ} (hZ : Measurable (Z i)) : Measurable fun ω => ((Z i ω).2 : ℤ) :=
  measurable_intCast_snd.comp hZ

end LocalCount

open LocalCount

theorem isProbabilityMeasure_cntLaw [IsProbabilityMeasure P] (hZ : Measurable (Z 0)) :
    IsProbabilityMeasure (cntLaw P Z) :=
  Measure.isProbabilityMeasure_map (measurable_cnt hZ).aemeasurable

theorem cntAtom_nonneg (P : Measure Ω) (Z : ℕ → Ω → ℝ × ℕ) : 0 ≤ cntAtom P Z :=
  lconc_nonneg _ _

theorem cntLaw_apply_natCast (hZ : Measurable (Z 0)) (k : ℕ) :
    cntLaw P Z {(k : ℤ)} = P {ω | (Z 0 ω).2 = k} := by
  rw [cntLaw, Measure.map_apply (measurable_cnt hZ) (measurableSet_singleton _)]
  congr 1
  ext ω
  simp

/-- The count law of every pair of an iid sequence is the law of the first count. -/
theorem IIDPairs.map_count_eq (h : IIDPairs P Z) (i : ℕ) :
    P.map (fun ω => ((Z i ω).2 : ℤ)) = cntLaw P Z :=
  ((h.ident i).comp measurable_intCast_snd).map_eq

/-- `P(S_t = k) = convFin t (law N) {k}`, with `S_t = N₀ + ⋯ + N_{t-1}`. -/
theorem measure_pairRank_eq_convFin [IsProbabilityMeasure P] (h : IIDPairs P Z) (t k : ℕ) :
    P {ω | ∑ i ∈ range t, (Z i ω).2 = k} = convFin t (fun _ => cntLaw P Z) {(k : ℤ)} := by
  set X : ℕ → Ω → ℤ := fun i ω => ((Z i ω).2 : ℤ) with hXdef
  have hX : ∀ i, Measurable (X i) := fun i => measurable_intCast_snd.comp (h.measurable i)
  have hind : iIndepFun X P := h.indep.comp (fun _ x => ((x.2 : ℕ) : ℤ))
    (fun _ => measurable_intCast_snd)
  have hlaw : ∀ i, P.map (X i) = cntLaw P Z := h.map_count_eq
  rw [← map_sum_range_eq_convFin hX hind hlaw t,
    Measure.map_apply (Finset.measurable_sum _ fun i _ => hX i) (measurableSet_singleton _)]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, hXdef]
  constructor
  · intro hk; rw [← hk]; push_cast; rfl
  · intro hk; exact_mod_cast hk

namespace LocalCount

omit mΩ in
/-- `pairRank` of the path is the sum of the first counts. -/
theorem pairRank_seq (Z : ℕ → Ω → ℝ × ℕ) (ω : Ω) (t : ℕ) :
    pairRank (seq Z ω) t = ∑ i ∈ range t, (Z i ω).2 := rfl

end LocalCount

open LocalCount

/-- `P(pairRank (seq Z ·) t = k) = convFin t (law N) {k}`. -/
theorem measure_pairRank_seq_eq_convFin [IsProbabilityMeasure P] (h : IIDPairs P Z) (t k : ℕ) :
    P {ω | pairRank (seq Z ω) t = k} = convFin t (fun _ => cntLaw P Z) {(k : ℤ)} :=
  measure_pairRank_eq_convFin h t k

/-- Real form: `P(pairRank t = k) = convFin t (law N) {k}`. -/
theorem measureReal_pairRank_eq_convFin [IsProbabilityMeasure P] (h : IIDPairs P Z) (t k : ℕ) :
    P.real {ω | pairRank (seq Z ω) t = k} =
      (convFin t (fun _ => cntLaw P Z) {(k : ℤ)}).toReal := by
  rw [measureReal_def]
  exact congrArg ENNReal.toReal (measure_pairRank_eq_convFin h t k)

/-! ## The decomposition over the stop -/

namespace LocalCount

theorem measurableSet_rank_eq (h : IIDPairs P Z) (t k : ℕ) :
    MeasurableSet {ω | ∑ i ∈ range t, (Z i ω).2 = k} :=
  (Finset.measurable_sum _ fun i _ => (h.measurable i).snd) (measurableSet_singleton k)

theorem measurable_pairSegLen_seq (h : IIDPairs P Z) (eps : ℝ) :
    Measurable fun ω => pairSegLen eps (seq Z ω) :=
  (measurable_pairSegLen eps).comp (measurable_seq h.measurable)

theorem measurableSet_stop_rank (h : IIDPairs P Z) (eps : ℝ) (t k : ℕ) :
    MeasurableSet {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} :=
  ((measurable_pairSegLen_seq h eps) (measurableSet_singleton _)).inter
    (measurableSet_rank_eq h t k)

omit mΩ in
/-- The next-layer count is the rank at the stop. -/
theorem nextLayer_zero_snd (eps : ℝ) (Z : ℕ → Ω → ℝ × ℕ) (ω : Ω) :
    (nextLayer eps Z 0 ω).2 = pairRank (seq Z ω) (pairSegLen eps (seq Z ω)).toNat := by
  rw [nextLayer_zero, firstBlock, Prod.snd_sum]
  rfl

end LocalCount

open LocalCount

/-- **Decomposition over the stop.**  For `N⁺ = (nextLayer eps Z 0).2` and an almost surely
finite stop `T`, `P(N⁺ = k) = ∑' t, P(T = t ∧ S_t = k)`. -/
theorem measure_nextCount_eq_tsum (h : IIDPairs P Z) (eps : ℝ)
    (hfin : ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤) (k : ℕ) :
    P {ω | (nextLayer eps Z 0 ω).2 = k} =
      ∑' t : ℕ, P {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} := by
  have hae : {ω | (nextLayer eps Z 0 ω).2 = k} =ᵐ[P]
      ⋃ t : ℕ, {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} := by
    refine Filter.eventuallyEq_set.2 (hfin.mono fun ω hω => ?_)
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, nextLayer_zero_snd]
    constructor
    · intro hk
      exact ⟨_, (ENat.natCast_toNat hω).symm, hk⟩
    · rintro ⟨t, ht, hk⟩
      rw [ht, ENat.toNat_natCast]
      exact hk
  rw [measure_congr hae, measure_iUnion _ fun t => measurableSet_stop_rank h eps t k]
  intro a b hab
  refine Set.disjoint_left.2 fun ω ha hb => hab ?_
  have := ha.1.symm.trans hb.1
  exact_mod_cast this

/-! ## Consequences of the standing hypotheses -/

namespace LocalCount

/-- Kesten's inequality with the constant `224` of `kesten_iid`. -/
theorem kestenIID_224 : KestenIID 224 := fun μ hμ _ hn hp => @kesten_iid μ hμ _ hn hp

end LocalCount

open LocalCount

namespace LocalCountHyp

variable {m θ B B₂ : ℝ}

/-- The Gamma kernel in the form used by `maximal_bernstein` (all `n`, including `n = 0`). -/
theorem gam_all (H : LocalCountHyp P Z m θ B B₂) (n : ℕ) (A : Set ℝ) (hA : MeasurableSet A) :
    P {ω | (Z 0 ω).1 ∈ A ∧ (Z 0 ω).2 = n} = P {ω | (Z 0 ω).2 = n} * gammaMeasure n 1 A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 := measure_count_eq_zero H.pos
    rw [h0, zero_mul]
    exact measure_mono_null (fun ω hω => hω.2) h0
  · exact H.gamma n A hA hn

/-- The first segment is almost surely finite. -/
theorem fin [IsProbabilityMeasure P] (H : LocalCountHyp P Z m θ B B₂) (eps : ℝ) :
    ∀ᵐ ω ∂P, pairSegLen eps (seq Z ω) ≠ ⊤ :=
  ae_pairSegLen_ne_top_of_gammaKernel H.iid H.gamma (measure_count_eq_zero H.pos) eps

private theorem gammaMeasure_Iic_zero' (a : ℝ) : gammaMeasure a 1 (Set.Iic 0) = 0 := by
  have h0 : gammaMeasure a 1 {0} = 0 :=
    withDensity_absolutelyContinuous _ _ (Real.volume_singleton)
  refine measure_mono_null (t := Set.Iio 0 ∪ {0}) (fun x hx => ?_)
    (measure_union_null (lcbb_gamma_Iio_zero a) h0)
  rcases (Set.mem_Iic.1 hx).lt_or_eq with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The gaps are almost surely positive. -/
theorem gap_pos (H : LocalCountHyp P Z m θ B B₂) (i : ℕ) : ∀ᵐ ω ∂P, 0 < (Z i ω).1 := by
  have h0 : ∀ᵐ ω ∂P, 0 < (Z 0 ω).1 := by
    rw [ae_iff]
    have e : {ω | ¬ 0 < (Z 0 ω).1} ⊆
        ⋃ n : ℕ, {ω | (Z 0 ω).1 ∈ Set.Iic 0 ∧ (Z 0 ω).2 = n} := by
      intro ω hω
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_Iic]
      exact ⟨_, not_lt.1 hω, rfl⟩
    refine measure_mono_null e (measure_iUnion_null fun n => ?_)
    rw [H.gam_all n _ measurableSet_Iic, gammaMeasure_Iic_zero', mul_zero]
  have hm : MeasurableSet {x : ℝ × ℕ | 0 < x.1} := measurable_fst measurableSet_Ioi
  exact (H.iid.ident i).symm.ae_mem_snd hm h0

/-- The shifted sequence `(Z (r + i))ᵢ` satisfies the same hypotheses. -/
theorem shift (H : LocalCountHyp P Z m θ B B₂) (r : ℕ) :
    LocalCountHyp P (fun i => Z (r + i)) m θ B B₂ := by
  have hid := H.iid.ident r
  have hN : Measurable fun x : ℝ × ℕ => ((x.2 : ℕ) : ℝ) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).comp measurable_snd
  refine
    { iid := H.iid.shift r
      pos := ?_
      gamma := ?_
      m_pos := H.m_pos
      mean := ?_
      θ_pos := H.θ_pos
      exp_int := ?_
      exp_le := ?_
      sq_int := ?_
      sq_le := ?_ }
  · exact hid.symm.ae_mem_snd (t := {x : ℝ × ℕ | 1 ≤ x.2})
      (measurable_snd measurableSet_Ici) H.pos
  · intro n A hA hn
    have e1 := hid.measure_mem_eq (s := {x : ℝ × ℕ | x.1 ∈ A ∧ x.2 = n})
      ((measurable_fst hA).inter (measurable_snd (measurableSet_singleton n)))
    have e2 := hid.measure_mem_eq (s := {x : ℝ × ℕ | x.2 = n})
      (measurable_snd (measurableSet_singleton n))
    change P {ω | (Z r ω).1 ∈ A ∧ (Z r ω).2 = n} =
      P {ω | (Z r ω).2 = n} * gammaMeasure n 1 A
    rw [show {ω | (Z r ω).1 ∈ A ∧ (Z r ω).2 = n} =
        Z r ⁻¹' {x : ℝ × ℕ | x.1 ∈ A ∧ x.2 = n} from rfl,
      show {ω | (Z r ω).2 = n} = Z r ⁻¹' {x : ℝ × ℕ | x.2 = n} from rfl, e1, e2]
    exact H.gamma n A hA hn
  · rw [← H.mean]
    exact (hid.comp hN).integral_eq
  · exact (hid.comp ((hN.const_mul θ).div_const m).exp).integrable_iff.2 H.exp_int
  · exact le_trans (le_of_eq (hid.comp ((hN.const_mul θ).div_const m).exp).integral_eq) H.exp_le
  · exact (hid.comp (hN.pow_const 2)).integrable_iff.2 H.sq_int
  · exact le_trans (le_of_eq (hid.comp (hN.pow_const 2)).integral_eq) H.sq_le

/-- `maximal_bernstein` under the standing hypotheses. -/
theorem bernstein [IsProbabilityMeasure P] (H : LocalCountHyp P Z m θ B B₂) (s : ℕ) (hs : 1 ≤ s)
    {x : ℝ} (hx : 0 < x) :
    P.real {ω | ∃ j ≤ s, x < |gapWalk m Z j ω|} ≤
      2 * Real.exp (-(bernsteinRate θ B * min (x ^ 2 / s) x)) :=
  maximal_bernstein H.iid H.θ_pos H.pos H.gam_all H.m_pos H.mean H.exp_int H.exp_le s hs hx

theorem B_pos [IsProbabilityMeasure P] (H : LocalCountHyp P Z m θ B B₂) : 0 < B :=
  (integral_exp_pos H.exp_int).trans_le H.exp_le

/-! ### The count law -/

theorem cntLaw_Iic_zero (H : LocalCountHyp P Z m θ B B₂) : cntLaw P Z (Set.Iic 0) = 0 := by
  rw [cntLaw, Measure.map_apply (measurable_cnt (H.iid.measurable 0)) measurableSet_Iic]
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 H.pos)
  simp only [Set.mem_preimage, Set.mem_Iic] at hω
  show ¬ 1 ≤ (Z 0 ω).2
  omega

theorem integrable_sq_cntLaw (H : LocalCountHyp P Z m θ B B₂) :
    Integrable (fun q : ℤ => (q : ℝ) ^ 2) (cntLaw P Z) := by
  rw [cntLaw, integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
    (measurable_cnt (H.iid.measurable 0)).aemeasurable]
  refine H.sq_int.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [Function.comp]

theorem integral_cntLaw (H : LocalCountHyp P Z m θ B B₂) :
    ∫ q, (q : ℝ) ∂(cntLaw P Z) = m := by
  rw [cntLaw, integral_map (measurable_cnt (H.iid.measurable 0)).aemeasurable
    Measurable.of_discrete.aestronglyMeasurable, ← H.mean]
  simp

theorem integral_sq_cntLaw_le (H : LocalCountHyp P Z m θ B B₂) :
    ∫ q, (q : ℝ) ^ 2 ∂(cntLaw P Z) ≤ B₂ * m ^ 2 := by
  rw [cntLaw, integral_map (measurable_cnt (H.iid.measurable 0)).aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  simpa using H.sq_le

end LocalCountHyp

/-- The count law of a shifted iid sequence is the count law. -/
theorem IIDPairs.cntLaw_shift (h : IIDPairs P Z) (r : ℕ) :
    cntLaw P (fun i => Z (r + i)) = cntLaw P Z :=
  h.map_count_eq r

/-! ## Half factorisation -/

namespace LocalCount

theorem measurable_past_rank (h : IIDPairs P Z) (r : ℕ) :
    Measurable[pairFiltration Z h.measurable r] (fun ω => ∑ i ∈ range r, (Z i ω).2) :=
  Finset.measurable_sum _ fun _ hi =>
    (pairFiltration_measurable_lt h.measurable (Finset.mem_range.1 hi)).snd

theorem measurableSet_past_rank (h : IIDPairs P Z) (r u : ℕ) :
    MeasurableSet[pairFiltration Z h.measurable r] {ω | ∑ i ∈ range r, (Z i ω).2 = u} :=
  measurable_past_rank h r (measurableSet_singleton u)

theorem measurable_past_gapWalk (h : IIDPairs P Z) (m : ℝ) {r j : ℕ} (hj : j ≤ r) :
    Measurable[pairFiltration Z h.measurable r] (gapWalk m Z j) := by
  have e : gapWalk m Z j = fun ω => ∑ i ∈ range j, ((Z i ω).1 / m - 1) := rfl
  rw [e]
  exact Finset.measurable_sum _ fun _ hi =>
    ((pairFiltration_measurable_lt h.measurable
      (lt_of_lt_of_le (Finset.mem_range.1 hi) hj)).fst.div_const m).sub_const 1

/-- The maximal event of the first `r` normalized gaps is an event of the first `r` pairs. -/
theorem measurableSet_past_max (h : IIDPairs P Z) (m x : ℝ) (r : ℕ) :
    MeasurableSet[pairFiltration Z h.measurable r] {ω | ∃ j ≤ r, x < |gapWalk m Z j ω|} := by
  have e : {ω | ∃ j ≤ r, x < |gapWalk m Z j ω|} =
      ⋃ j ∈ Finset.range (r + 1), {ω | x < |gapWalk m Z j ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    exact exists_congr fun j => and_congr_left' (by omega)
  rw [e]
  exact Finset.measurableSet_biUnion _ fun j hj =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp
      (measurable_past_gapWalk h m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))))

theorem measurableSet_seq_rank (s v : ℕ) :
    MeasurableSet {z : ℕ → ℝ × ℕ | ∑ i ∈ range s, (z i).2 = v} :=
  (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).snd) (measurableSet_singleton v)

theorem measurableSet_seq_max (m x : ℝ) (s : ℕ) :
    MeasurableSet {z : ℕ → ℝ × ℕ | ∃ j ≤ s, x < |∑ i ∈ range j, ((z i).1 / m - 1)|} := by
  have e : {z : ℕ → ℝ × ℕ | ∃ j ≤ s, x < |∑ i ∈ range j, ((z i).1 / m - 1)|} =
      ⋃ j ∈ Finset.range (s + 1), {z : ℕ → ℝ × ℕ | x < |∑ i ∈ range j, ((z i).1 / m - 1)|} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    exact exists_congr fun j => and_congr_left' (by omega)
  rw [e]
  exact Finset.measurableSet_biUnion _ fun j _ =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp
      (Finset.measurable_sum _ fun i _ => (((measurable_pi_apply i).fst).div_const m).sub_const 1))

omit mΩ in
/-- Splitting `{S_{r+s} = k}` according to the value of `S_r`. -/
theorem rank_add_subset (r s k : ℕ) :
    {ω | ∑ i ∈ range (r + s), (Z i ω).2 = k} ⊆
      ⋃ u ∈ Finset.range (k + 1), ({ω | ∑ i ∈ range r, (Z i ω).2 = u} ∩
        {ω | ∑ i ∈ range s, (Z (r + i) ω).2 = k - u}) := by
  intro ω hω
  simp only [Set.mem_ofPred_eq, Finset.sum_range_add] at hω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_range,
    exists_prop]
  exact ⟨_, by omega, rfl, by omega⟩

/-- **Half factorisation, past half.**  If `E` is an event of the first `r` pairs and every
atom of `S̃_s = N_r + ⋯ + N_{r+s-1}` is at most `L`, then `P(E ∩ {S_{r+s} = k}) ≤ L P(E)`. -/
theorem measure_past_inter_rank_le (h : IIDPairs P Z) {r : ℕ} {E : Set Ω}
    (hE : MeasurableSet[pairFiltration Z h.measurable r] E) (s k : ℕ) {L : ℝ≥0∞}
    (hL : ∀ v : ℕ, P {ω | ∑ i ∈ range s, (Z (r + i) ω).2 = v} ≤ L) :
    P (E ∩ {ω | ∑ i ∈ range (r + s), (Z i ω).2 = k}) ≤ L * P E := by
  set F : ℕ → Set Ω := fun u => E ∩ {ω | ∑ i ∈ range r, (Z i ω).2 = u} with hF
  have hFm : ∀ u, MeasurableSet[pairFiltration Z h.measurable r] (F u) := fun u =>
    hE.inter (measurableSet_past_rank h r u)
  have hsub : E ∩ {ω | ∑ i ∈ range (r + s), (Z i ω).2 = k} ⊆
      ⋃ u ∈ Finset.range (k + 1), (F u ∩ {ω | ∑ i ∈ range s, (Z (r + i) ω).2 = k - u}) := by
    intro ω ⟨hωE, hω⟩
    have := rank_add_subset r s k hω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop] at this ⊢
    obtain ⟨u, hu, h1, h2⟩ := this
    exact ⟨u, hu, ⟨hωE, h1⟩, h2⟩
  have hind : ∀ u v : ℕ, P (F u ∩ {ω | ∑ i ∈ range s, (Z (r + i) ω).2 = v}) =
      P (F u) * P {ω | ∑ i ∈ range s, (Z (r + i) ω).2 = v} := by
    intro u v
    have := measure_future_inter_pairFiltration h r (measurableSet_seq_rank s v) (hFm u)
    rw [Set.inter_comm, mul_comm]
    exact this
  have hdisj : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint F := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 fun ω ha hb => hab ?_
    exact ha.2.symm.trans hb.2
  calc P (E ∩ {ω | ∑ i ∈ range (r + s), (Z i ω).2 = k})
      ≤ P (⋃ u ∈ Finset.range (k + 1),
          (F u ∩ {ω | ∑ i ∈ range s, (Z (r + i) ω).2 = k - u})) := measure_mono hsub
    _ ≤ ∑ u ∈ Finset.range (k + 1),
          P (F u ∩ {ω | ∑ i ∈ range s, (Z (r + i) ω).2 = k - u}) :=
        measure_biUnion_finset_le _ _
    _ = ∑ u ∈ Finset.range (k + 1),
          P (F u) * P {ω | ∑ i ∈ range s, (Z (r + i) ω).2 = k - u} := by
        refine Finset.sum_congr rfl fun u _ => hind u (k - u)
    _ ≤ ∑ u ∈ Finset.range (k + 1), P (F u) * L := by
        gcongr with u _
        exact hL _
    _ = P (⋃ u ∈ Finset.range (k + 1), F u) * L := by
        rw [← Finset.sum_mul, measure_biUnion_finset hdisj fun u _ =>
          (pairFiltration Z h.measurable).le r _ (hFm u)]
    _ ≤ P E * L := by
        gcongr
        exact Set.iUnion₂_subset fun u _ => Set.inter_subset_left
    _ = L * P E := mul_comm _ _

/-- **Half factorisation, future half.**  If `A` is an event of the pairs from `r` on and every
atom of `S_r` is at most `L`, then `P(A ∩ {S_{r+s} = k}) ≤ L P(A)`. -/
theorem measure_future_inter_rank_le (h : IIDPairs P Z) {r : ℕ} {A : Set (ℕ → ℝ × ℕ)}
    (hA : MeasurableSet A) (s k : ℕ) {L : ℝ≥0∞}
    (hL : ∀ u : ℕ, P {ω | ∑ i ∈ range r, (Z i ω).2 = u} ≤ L) :
    P ((fun ω t => Z (r + t) ω) ⁻¹' A ∩ {ω | ∑ i ∈ range (r + s), (Z i ω).2 = k}) ≤
      L * P ((fun ω t => Z (r + t) ω) ⁻¹' A) := by
  set Y : Ω → ℕ → ℝ × ℕ := fun ω t => Z (r + t) ω with hY
  have hYm : Measurable Y := measurable_pi_lambda _ fun t => h.measurable (r + t)
  set A' : ℕ → Set (ℕ → ℝ × ℕ) := fun u => A ∩ {z | ∑ i ∈ range s, (z i).2 = k - u} with hA'
  have hA'm : ∀ u, MeasurableSet (A' u) := fun u => hA.inter (measurableSet_seq_rank s _)
  have hsub : Y ⁻¹' A ∩ {ω | ∑ i ∈ range (r + s), (Z i ω).2 = k} ⊆
      ⋃ u ∈ Finset.range (k + 1), (Y ⁻¹' A' u ∩ {ω | ∑ i ∈ range r, (Z i ω).2 = u}) := by
    intro ω ⟨hωA, hω⟩
    have := rank_add_subset r s k hω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop] at this ⊢
    obtain ⟨u, hu, h1, h2⟩ := this
    exact ⟨u, hu, ⟨hωA, h2⟩, h1⟩
  have hdisj : (↑(Finset.range (k + 1)) : Set ℕ).PairwiseDisjoint fun u => Y ⁻¹' A' u := by
    intro a ha b hb hab
    refine Set.disjoint_left.2 fun ω hωa hωb => hab ?_
    have e := hωa.2.symm.trans hωb.2
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    omega
  calc P (Y ⁻¹' A ∩ {ω | ∑ i ∈ range (r + s), (Z i ω).2 = k})
      ≤ P (⋃ u ∈ Finset.range (k + 1),
          (Y ⁻¹' A' u ∩ {ω | ∑ i ∈ range r, (Z i ω).2 = u})) := measure_mono hsub
    _ ≤ ∑ u ∈ Finset.range (k + 1), P (Y ⁻¹' A' u ∩ {ω | ∑ i ∈ range r, (Z i ω).2 = u}) :=
        measure_biUnion_finset_le _ _
    _ = ∑ u ∈ Finset.range (k + 1), P (Y ⁻¹' A' u) * P {ω | ∑ i ∈ range r, (Z i ω).2 = u} :=
        Finset.sum_congr rfl fun u _ =>
          measure_future_inter_pairFiltration h r (hA'm u) (measurableSet_past_rank h r u)
    _ ≤ ∑ u ∈ Finset.range (k + 1), P (Y ⁻¹' A' u) * L := by
        gcongr with u _
        exact hL _
    _ = P (⋃ u ∈ Finset.range (k + 1), Y ⁻¹' A' u) * L := by
        rw [← Finset.sum_mul, measure_biUnion_finset hdisj fun u _ => hYm (hA'm u)]
    _ ≤ P (Y ⁻¹' A) * L := by
        gcongr
        exact Set.iUnion₂_subset fun u _ => Set.preimage_mono Set.inter_subset_left
    _ = L * P (Y ⁻¹' A) := mul_comm _ _

end LocalCount

end

end PGM
