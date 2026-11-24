import PLAStochastic.Index.OneLayer.SegmentCount
import PLAStochastic.Index.Algorithm.RankHeightRecursion
import PLAStochastic.Index.Algorithm.MeasurableRankHeight
import PLAStochastic.Index.GRE.BlockCount
import PLAStochastic.ForMathlib.MeasureTheory.Integral.GoodEventSplit
import PLAStochastic.Index.GRE.LogLogArith
import PLAStochastic.Index.Endpoint.LargeEpsThreshold
import PLAStochastic.Index.Endpoint.LayerInduction

/-!
# H-G-RE: the expected rank-equispaced height under Model G

For fixed `n`, `eps` and a concentration level `t`, the good event says that every
lattice pair `(d, K)` with `d, K ≤ 2n` has its block-walk segment count in the
bracket `[aLow K/(d G₀) - t, 128 K/(d G₀) + t + 1]`.  Every layer of the actual
ALG-RE run uses such a pair, so `PLAStochastic.Index.Algorithm.RankHeightRecursion` bounds the height pathwise on
the good event; off it the height is at most `log₂ n + 1`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The bad event of one lattice pair. -/
def pairBad (eps : ℝ) (g : ℕ → Ω → ℝ) (G₀ : ℝ) (t : ℕ) (d K : ℕ) : Set Ω :=
  if 1 ≤ d ∧ 1 ≤ K then
    {ω | 128 * K / (d * G₀) + t + 1 < (blockCount eps g d K ω : ℝ)} ∪
      {ω | (blockCount eps g d K ω : ℝ) < aLow * K / (d * G₀) - t}
  else ∅

/-- The union of all pair bad events with `d, K ≤ 2n`. -/
def reBad (eps : ℝ) (g : ℕ → Ω → ℝ) (G₀ : ℝ) (t n : ℕ) : Set Ω :=
  ⋃ d ∈ range (2 * n + 1), ⋃ K ∈ range (2 * n + 1), pairBad eps g G₀ t d K

/-- Per-pair failure probability. -/
noncomputable def pairFail (t : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ t + Real.exp (-(Real.log (expBound (71 / 72))) * t)

theorem measurable_blockCount {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s)) (eps : ℝ)
    (d K : ℕ) : Measurable (blockCount eps g d K) := by
  have hX : ∀ j, Measurable (blockGap g d j) := fun j =>
    Finset.measurable_sum _ fun i _ => hg _
  have hq : Measurable fun ω => gapKeys (seq (blockGap g d) ω) :=
    measurable_gapKeys.comp (measurable_seq hX)
  exact measurable_finSegCount_comp eps hq measurable_const

theorem measurableSet_pairBad {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s)) (eps G₀ : ℝ)
    (t d K : ℕ) : MeasurableSet (pairBad eps g G₀ t d K) := by
  unfold pairBad
  split_ifs
  · have hm : Measurable fun ω => (blockCount eps g d K ω : ℝ) :=
      (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp (measurable_blockCount hg eps d K)
    exact (measurableSet_lt measurable_const hm).union (measurableSet_lt hm measurable_const)
  · exact MeasurableSet.empty

theorem measurableSet_reBad {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s)) (eps G₀ : ℝ)
    (t n : ℕ) : MeasurableSet (reBad eps g G₀ t n) :=
  MeasurableSet.biUnion (range (2 * n + 1)).countable_toSet fun d _ =>
    MeasurableSet.biUnion (range (2 * n + 1)).countable_toSet fun K _ =>
      measurableSet_pairBad hg eps G₀ t d K

/-- Per-pair bound: the block law is in the class, so both tails are small. -/
theorem measureReal_pairBad_le [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3) ≤ eps) (t d K : ℕ) :
    P.real (pairBad eps g (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) t d K) ≤ pairFail t := by
  unfold pairBad
  split_ifs with hdK
  swap
  · simp only [measureReal_empty]; unfold pairFail; positivity
  obtain ⟨hd, hK⟩ := hdK
  obtain ⟨hlaw, hv, hk, hGd⟩ := blockGap_class (eps := eps) hg hd
  have hμ := hlaw.mu_pos
  have hσ := hlaw.sigma_pos
  have hκ := hlaw.kappa_nonneg
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero _ _) heps
  have hepspos : 0 < eps := by linarith
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := largeConditions hμ hσ hκ hv hk heps
  set Gd := (d * μ₀) ^ 2 * eps ^ 2 / (Real.sqrt d * σ₀) ^ 2 with hGddef
  have hGd' : (d : ℝ) * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) = Gd := hGd.symm
  have hup := measureReal_segCount_gt_le hlaw hepspos hGddef K t
  have hlo := measureReal_segCount_lt_le_of_large hlaw hepspos hGddef c1 c2 c3 c4 K t
  rw [← hGd'] at hup hlo
  have hsets : ({ω | 128 * K / (d * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) + t + 1 <
        (blockCount eps g d K ω : ℝ)} : Set Ω) =
      {ω | 128 * K / (d * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) + t + 1 <
        (segCount eps (blockGap g d) K ω : ℝ)} := rfl
  have hsets2 : ({ω | (blockCount eps g d K ω : ℝ) <
        aLow * K / (d * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) - t} : Set Ω) =
      {ω | (segCount eps (blockGap g d) K ω : ℝ) <
        aLow * K / (d * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) - t} := rfl
  calc P.real (_ ∪ _) ≤ P.real _ + P.real _ := measureReal_union_le _ _
    _ ≤ pairFail t := by
        rw [hsets, hsets2]; unfold pairFail
        have e1 : 128 * (K : ℝ) / (d * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) =
            128 * K / ((d : ℝ) * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) := rfl
        linarith

/-- Probability of the global bad event. -/
theorem measureReal_reBad_le [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3) ≤ eps) (t n : ℕ) :
    P.real (reBad eps g (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) t n) ≤
      ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t :=
  measureReal_biUnion_pairs_le n _ fun d K _ _ => measureReal_pairBad_le hg heps t d K

/-! ## Pathwise bracket on the good event -/

/-- The concentration constant used in the recursion (`≤ 1`). -/
noncomputable def aRE : ℝ := min aLow 1

theorem aRE_pos : 0 < aRE := lt_min aLow_pos one_pos
theorem aRE_le_one : aRE ≤ 1 := min_le_right _ _
theorem aRE_le_aLow : aRE ≤ aLow := min_le_left _ _

omit mΩ in
/-- On the good event every layer of the actual ALG-RE run is in the count bracket. -/
theorem bracket_of_not_reBad {g : ℕ → Ω → ℝ} {eps G₀ : ℝ} (heps : 1 ≤ eps) (hG₀ : 0 < G₀)
    {n : ℕ} (hn : 1 ≤ n) (x0 : ℝ) (t : ℕ) {ω : Ω} (hω : ω ∉ reBad eps g G₀ t n) (ℓ : ℕ) :
    aRE * reMbar eps (fun s => x0 + ∑ i ∈ range s, g i ω) n G₀ ℓ - ((t : ℝ) + 1) ≤
        reSegs eps (fun s => x0 + ∑ i ∈ range s, g i ω) n ℓ ∧
      (reSegs eps (fun s => x0 + ∑ i ∈ range s, g i ω) n ℓ : ℝ) ≤
        128 * reMbar eps (fun s => x0 + ∑ i ∈ range s, g i ω) n G₀ ℓ + ((t : ℝ) + 1) := by
  set p : ℕ → ℝ := fun s => x0 + ∑ i ∈ range s, g i ω
  set d := reDelta eps p n ℓ
  set K := reSize eps p n ℓ
  have hd : 1 ≤ d := one_le_reDelta heps hn ℓ
  have hK : 1 ≤ K := one_le_reSize heps hn ℓ
  have hKd : K * d < 2 * n := reSize_mul_reDelta_lt heps hn ℓ
  have hd2 : d < 2 * n + 1 := by nlinarith
  have hK2 : K < 2 * n + 1 := by nlinarith
  have hnot : ω ∉ pairBad eps g G₀ t d K := by
    intro h
    exact hω (Set.mem_biUnion (mem_range.2 hd2) (Set.mem_biUnion (mem_range.2 hK2) h))
  unfold pairBad at hnot
  rw [if_pos ⟨hd, hK⟩] at hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot
  obtain ⟨hup, hlo⟩ := hnot
  have hM : reSegs eps p n ℓ = blockCount eps g d K ω := by
    rw [reSegs_eq_PLAcount heps hn (g := fun i => g i ω) (x0 := x0) (fun _ _ => rfl) ℓ]
    exact PLAcount_eq_blockCount eps g d K ω
  have hmbar : reMbar eps p n G₀ ℓ = (K : ℝ) / ((d : ℝ) * G₀) := rfl
  rw [hM, hmbar]
  have hmpos : 0 ≤ (K : ℝ) / ((d : ℝ) * G₀) := by positivity
  constructor
  · have h1 : aRE * ((K : ℝ) / ((d : ℝ) * G₀)) ≤ aLow * ((K : ℝ) / ((d : ℝ) * G₀)) :=
      mul_le_mul_of_nonneg_right aRE_le_aLow hmpos
    have h2 : aLow * ((K : ℝ) / ((d : ℝ) * G₀)) = aLow * K / (d * G₀) := by ring
    linarith
  · have h2 : 128 * ((K : ℝ) / ((d : ℝ) * G₀)) = 128 * K / (d * G₀) := by ring
    linarith

/-! ## Expected height for fixed parameters -/

/-- The pathwise upper bound on the good event. -/
noncomputable def reUpper (n : ℕ) (G₀ : ℝ) (t : ℕ) : ℝ :=
  Real.logb 2 (Real.log n / Real.log (G₀ / (4 * 128))) +
    Real.logb 2 (2 * (128 * (4 * ((t : ℝ) + 1) / aRE) + ((t : ℝ) + 1))) + 4

/-- The pathwise lower bound on the good event. -/
noncomputable def reLower (n : ℕ) (G₀ : ℝ) : ℝ :=
  Real.logb 2 (Real.log n / (2 * Real.log (2 / aRE * G₀)))

theorem integral_reHeight_le [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {eps : ℝ}
    (heps : epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3) ≤ eps) {n : ℕ} (hn : 1 ≤ n) (t : ℕ)
    (hq : 1 < μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128))
    (hqn : μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128) ≤ n) :
    ∫ ω, (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) ∂P ≤
      reUpper n (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) t +
        ((Nat.log 2 n : ℝ) + 1) * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) := by
  set G₀ := μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero _ _) heps
  have hG₀ : 0 < G₀ := by have := hg.mu_pos; have := hg.sigma_pos; positivity
  have hgm := hg.iid.measurable
  have hHm : Measurable fun ω => (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp
      (measurable_reHeight_partialSum eps n hx0 hgm)
  have hU0 : 0 ≤ reUpper n G₀ t := by
    unfold reUpper
    have hlogq : 0 < Real.log (G₀ / (4 * 128)) := Real.log_pos hq
    have h1 : 0 ≤ Real.logb 2 (Real.log n / Real.log (G₀ / (4 * 128))) := by
      apply Real.logb_nonneg (by norm_num)
      rw [le_div_iff₀ hlogq, one_mul]
      exact Real.log_le_log (by linarith) hqn
    have h2 : 0 ≤ Real.logb 2 (2 * (128 * (4 * ((t : ℝ) + 1) / aRE) + ((t : ℝ) + 1))) := by
      apply Real.logb_nonneg (by norm_num)
      have : 0 ≤ 128 * (4 * ((t : ℝ) + 1) / aRE) := by have := aRE_pos; positivity
      have : (1 : ℝ) ≤ (t : ℝ) + 1 := by have := (Nat.cast_nonneg t : (0:ℝ) ≤ t); linarith
      linarith
    linarith
  have hmain := integral_le_of_good (P := P)
    (H := fun ω => (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ))
    (measurableSet_reBad hgm eps G₀ t n) hHm.aestronglyMeasurable hU0
    (fun ω => Nat.cast_nonneg _)
    (Hmax := (Nat.log 2 n : ℝ) + 1)
    (fun ω => by exact_mod_cast reHeight_le_log heps1 hn)
    (fun ω hω => by
      have hbr := bracket_of_not_reBad heps1 hG₀ hn (x0 ω) t hω
      have ht1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by
        have := (Nat.cast_nonneg t : (0:ℝ) ≤ t); linarith
      exact reHeight_le_of_bracket heps1 hn aRE_pos aRE_le_one (by norm_num) ht1 hbr hq hqn)
  have hbad := measureReal_reBad_le hg heps t n
  have hlog0 : 0 ≤ (Nat.log 2 n : ℝ) + 1 := by positivity
  calc _ ≤ _ := hmain
    _ ≤ _ := by gcongr

theorem integral_reHeight_ge [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0) {eps : ℝ}
    (heps : epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3) ≤ eps) {n : ℕ} (hn : 1 ≤ n) (t : ℕ)
    (hA : 1 ≤ μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)
    (hsqrt : 4 * ((t : ℝ) + 1) / aRE ≤ Real.sqrt n)
    (hL0 : 0 ≤ reLower n (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) :
    reLower n (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) *
        (1 - ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) ≤
      ∫ ω, (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) ∂P := by
  set G₀ := μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2
  set L := reLower n G₀
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero _ _) heps
  have hG₀ : 0 < G₀ := by linarith
  have hgm := hg.iid.measurable
  set bad := reBad eps g G₀ t n
  have hbadm : MeasurableSet bad := measurableSet_reBad hgm eps G₀ t n
  have hHm : Measurable fun ω => (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp
      (measurable_reHeight_partialSum eps n hx0 hgm)
  have hHint : Integrable (fun ω => (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ))
      P := by
    refine Integrable.mono' (integrable_const ((Nat.log 2 n : ℝ) + 1)) hHm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast reHeight_le_log heps1 hn
  have hpt : ∀ ω, badᶜ.indicator (fun _ => L) ω ≤
      (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) := by
    intro ω
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_notMem (by simpa using hω)]; exact Nat.cast_nonneg _
    · rw [Set.indicator_of_mem (by simpa using hω)]
      have hbr := bracket_of_not_reBad heps1 hG₀ hn (x0 ω) t hω
      have ht1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by
        have := (Nat.cast_nonneg t : (0:ℝ) ≤ t); linarith
      exact (logb_lt_reHeight_of_bracket heps1 hn aRE_pos aRE_le_one ht1 hA
        (fun ℓ => (hbr ℓ).1) hsqrt).le
  have hint2 : Integrable (badᶜ.indicator (fun _ => L)) P :=
    (integrable_const L).indicator hbadm.compl
  have hmono := integral_mono hint2 hHint hpt
  rw [integral_indicator hbadm.compl, setIntegral_const, probReal_compl_eq_one_sub hbadm,
    smul_eq_mul] at hmono
  have hbad := measureReal_reBad_le hg heps t n
  calc L * (1 - ((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) ≤ L * (1 - P.real bad) := by
        gcongr
    _ = (1 - P.real bad) * L := by ring
    _ ≤ _ := hmono

end

end PGM
