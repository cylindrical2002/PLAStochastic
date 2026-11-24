import PLAStochastic.Swing.Ladder.Renewal.LadderPointCount
import PLAStochastic.Swing.Ladder.Renewal.EquilibriumOvershoot

/-! # The overshoot renewal identity for the actual ladder levels

`eq:overshootrenewalidentity` says that the tail of the overshoot above a level
is the residual-life integral of the ladder renewal measure.  The ladder levels
of the positive-drift Gaussian walk are a genuine renewal sequence, so the
identity is proved here by the one-step independence split followed by
summation against the renewal measure.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- One renewal step: an independent increment past a level. -/
theorem measure_le_and_lt_add_of_indepFun [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (h : IndepFun f g μ) (b c : ℝ) :
    μ ({ω | f ω ≤ b} ∩ {ω | c < f ω + g ω}) =
      ∫⁻ s in Iic b, (μ.map g) (Ioi (c-s)) ∂(μ.map f) := by
  have hpair : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
  have hprod : μ.map (fun ω => (f ω, g ω)) = (μ.map f).prod (μ.map g) :=
    (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mp h
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ b ∧ c < p.1 + p.2} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
  have hpre : (fun ω => (f ω, g ω)) ⁻¹' {p : ℝ × ℝ | p.1 ≤ b ∧ c < p.1 + p.2} =
      {ω | f ω ≤ b} ∩ {ω | c < f ω + g ω} := rfl
  rw [← hpre, ← Measure.map_apply hpair hS, hprod, Measure.prod_apply hS]
  have hslice : ∀ s : ℝ, (μ.map g) (Prod.mk s ⁻¹' {p : ℝ × ℝ | p.1 ≤ b ∧ c < p.1 + p.2}) =
      (Iic b).indicator (fun s => (μ.map g) (Ioi (c-s))) s := by
    intro s
    by_cases hs : s ≤ b
    · rw [Set.indicator_of_mem (show s ∈ Iic b from hs)]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioi]
      constructor
      · rintro ⟨-, h2⟩
        linarith
      · intro h2
        exact ⟨hs, by linarith⟩
    · rw [Set.indicator_of_notMem (show s ∉ Iic b from hs)]
      have hempty : Prod.mk s ⁻¹' {p : ℝ × ℝ | p.1 ≤ b ∧ c < p.1 + p.2} = ∅ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -⟩
        exact hs h1
      rw [hempty, measure_empty]
  rw [lintegral_congr hslice, lintegral_indicator measurableSet_Iic]

/-! ### The ladder levels increase to infinity -/

omit mΩ in
theorem gaussianLadderHeightAt_nonneg (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ gaussianLadderHeightAt X a n ω :=
  gaussianAscendingLadderHeight_nonneg (X := fun k (v : ℕ → ℝ) => v k) a _

omit mΩ in
theorem gaussianLadderSum_nonneg (X : ℕ → Ω → ℝ) (a : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ gaussianLadderSum X a n ω :=
  Finset.sum_nonneg (fun k _ => gaussianLadderHeightAt_nonneg X a k ω)

omit mΩ in
theorem gaussianLadderSum_monotone (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) :
    Monotone (fun n => gaussianLadderSum X a n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [gaussianLadderSum_succ]
  linarith [gaussianLadderHeightAt_nonneg X a n ω]

/-- Almost surely the ladder levels exceed every bound. -/
theorem gaussianLadderSum_exists_gt_ae [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, ∃ n : ℕ, b < gaussianLadderSum X a n ω := by
  have hkey : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∃ n : ℕ, (k : ℝ) < gaussianLadderSum X a n ω := by
    intro k
    have hsum : (∑' n : ℕ, μ {ω | gaussianLadderSum X a n ω ∈ Icc (0 : ℝ) (k : ℝ)}) ≠ ⊤ := by
      have heq := ladderRenewalMeasure_eq_tsum_ladderSum hX hi hG ha
        (A := Icc (0 : ℝ) (k : ℝ)) measurableSet_Icc
      have hbound := gaussianAscendingLadderRenewal_Icc_le hX hi hG ha haM
        (b := (k : ℝ)) (Nat.cast_nonneg k)
      rw [heq] at hbound
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
    have hbc := measure_limsup_atTop_eq_zero (μ := μ)
      (s := fun n => {ω | gaussianLadderSum X a n ω ∈ Icc (0 : ℝ) (k : ℝ)}) hsum
    have hae : ∀ᵐ ω ∂μ, ω ∉ Filter.limsup
        (fun n => {ω | gaussianLadderSum X a n ω ∈ Icc (0 : ℝ) (k : ℝ)}) atTop := by
      rw [ae_iff]
      simpa using hbc
    filter_upwards [hae] with ω hω
    by_contra hcon
    have hcon' : ∀ n : ℕ, gaussianLadderSum X a n ω ≤ (k : ℝ) := by
      intro n
      by_contra hn
      exact hcon ⟨n, lt_of_not_ge hn⟩
    apply hω
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    refine Set.mem_iInter.mpr fun m => ?_
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Nat.le_refl m, ?_⟩
    exact ⟨gaussianLadderSum_nonneg X a m ω, hcon' m⟩
  rw [← ae_all_iff] at hkey
  filter_upwards [hkey] with ω hω b
  obtain ⟨k, hk⟩ := exists_nat_gt b
  obtain ⟨n, hn⟩ := hω k
  exact ⟨n, lt_trans hk hn⟩

/-! ### The passage level and its overshoot -/

/-- The first ladder index whose level exceeds `b`. -/
def gaussianLadderPassage (X : ℕ → Ω → ℝ) (a b : ℝ) (ω : Ω) : ℕ :=
  if h : ∃ n : ℕ, b < gaussianLadderSum X a n ω then Nat.find h else 0

/-- The overshoot of the ladder levels above `b`. -/
def gaussianLadderOvershoot (X : ℕ → Ω → ℝ) (a b : ℝ) (ω : Ω) : ℝ :=
  gaussianLadderSum X a (gaussianLadderPassage X a b ω) ω - b

omit mΩ in
theorem gaussianLadderOvershoot_gt_iff (X : ℕ → Ω → ℝ) (a : ℝ) {b t : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) {ω : Ω}
    (hex : ∃ n : ℕ, b < gaussianLadderSum X a n ω) :
    t < gaussianLadderOvershoot X a b ω ↔
      ∃ n : ℕ, gaussianLadderSum X a n ω ≤ b ∧
        b+t < gaussianLadderSum X a (n+1) ω := by
  have hpass : gaussianLadderPassage X a b ω = Nat.find hex := by
    rw [gaussianLadderPassage, dif_pos hex]
  have hgt : b < gaussianLadderSum X a (Nat.find hex) ω := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, gaussianLadderSum X a j ω ≤ b :=
    fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hpos : 0 < Nat.find hex := by
    by_contra hcon
    have h0 : Nat.find hex = 0 := by omega
    rw [h0, gaussianLadderSum_zero] at hgt
    linarith
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m+1 := ⟨Nat.find hex - 1, by omega⟩
  constructor
  · intro hov
    refine ⟨m, hmin m (by omega), ?_⟩
    rw [← hm]
    rw [gaussianLadderOvershoot, hpass, hm] at hov
    rw [hm]
    linarith
  · rintro ⟨n, hn1, hn2⟩
    have hle : Nat.find hex ≤ n+1 := Nat.find_le (by linarith)
    have hge : n+1 ≤ Nat.find hex := by
      by_contra hcon
      have : Nat.find hex ≤ n := by omega
      have := gaussianLadderSum_monotone X a ω this
      have hgt' : b < gaussianLadderSum X a n ω := lt_of_lt_of_le hgt this
      linarith
    have heq : Nat.find hex = n+1 := le_antisymm hle hge
    rw [gaussianLadderOvershoot, hpass, heq]
    linarith

/-! ### The renewal identity -/

theorem gaussianLadderStep_indep [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IndepFun (gaussianLadderSum X a n) (gaussianLadderHeightAt X a n) μ := by
  have h := (gaussianLadderHeights_iIndepFun hX hi hG ha).indepFun_finsetSum_of_notMem
    (fun k => gaussianLadderHeightAt_measurable hX a k)
    (s := Finset.range n) (i := n) (by simp)
  have heq : (∑ j ∈ Finset.range n, gaussianLadderHeightAt X a j) =
      gaussianLadderSum X a n := by
    funext ω
    simp [gaussianLadderSum, Finset.sum_apply]
  rwa [heq] at h

theorem gaussianLadderStep_measure [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    (b t : ℝ) (n : ℕ) :
    μ ({ω | gaussianLadderSum X a n ω ≤ b} ∩
        {ω | b+t < gaussianLadderSum X a (n+1) ω}) =
      ∫⁻ s in Icc (0 : ℝ) b, (gaussianAscendingLadderLaw X μ a) (Ioi (b+t-s))
        ∂(measureConvPow (gaussianAscendingLadderLaw X μ a) n) := by
  have hset : {ω | gaussianLadderSum X a n ω ≤ b} ∩
      {ω | b+t < gaussianLadderSum X a (n+1) ω} =
      {ω | gaussianLadderSum X a n ω ≤ b} ∩
        {ω | b+t < gaussianLadderSum X a n ω + gaussianLadderHeightAt X a n ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, gaussianLadderSum_succ]
  rw [hset, measure_le_and_lt_add_of_indepFun (gaussianLadderSum_measurable hX a n)
    (gaussianLadderHeightAt_measurable hX a n)
    (gaussianLadderStep_indep hX hi hG ha n) b (b+t),
    gaussianLadderHeightAt_map hX hi hG ha n, gaussianLadderSum_map hX hi hG ha n]
  have hnull : (measureConvPow (gaussianAscendingLadderLaw X μ a) n) (Iio (0 : ℝ)) = 0 := by
    rw [← gaussianLadderSum_map hX hi hG ha n,
      Measure.map_apply (gaussianLadderSum_measurable hX a n) measurableSet_Iio]
    have hempty : (gaussianLadderSum X a n) ⁻¹' (Iio (0 : ℝ)) = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact gaussianLadderSum_nonneg X a n ω
    rw [hempty, measure_empty]
  have hae : Iic b =ᵐ[measureConvPow (gaussianAscendingLadderLaw X μ a) n] Icc (0 : ℝ) b := by
    rw [ae_eq_set]
    constructor
    · have hdiff : Iic b \ Icc (0 : ℝ) b ⊆ Iio (0 : ℝ) := by
        intro x hx
        have h1 : x ≤ b := hx.1
        have h2 : ¬ (0 ≤ x ∧ x ≤ b) := hx.2
        show x < 0
        by_contra hcon
        exact h2 ⟨le_of_not_gt hcon, h1⟩
      exact measure_mono_null hdiff hnull
    · have hempty2 : Icc (0 : ℝ) b \ Iic b = (∅ : Set ℝ) := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
          not_and, not_not]
        rintro ⟨-, h2⟩
        exact h2
      rw [hempty2, measure_empty]
  rw [Measure.restrict_congr_set hae]

/-- `eq:overshootrenewalidentity` for the actual ladder levels of the
positive-drift Gaussian walk: the overshoot tail above a level is the
residual-life integral against the ladder renewal measure. -/
theorem gaussianLadderOvershoot_tail_eq [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    μ {ω | t < gaussianLadderOvershoot X a b ω} =
      renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t := by
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  set E : ℕ → Set Ω := fun n => {ω | gaussianLadderSum X a n ω ≤ b} ∩
    {ω | b+t < gaussianLadderSum X a (n+1) ω} with hEdef
  have hEmeas : ∀ n, MeasurableSet (E n) := by
    intro n
    exact (measurableSet_le (gaussianLadderSum_measurable hX a n) measurable_const).inter
      (measurableSet_lt measurable_const (gaussianLadderSum_measurable hX a (n+1)))
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    intro ω hm hn
    rcases lt_or_gt_of_ne hmn with h | h
    · have hmono := gaussianLadderSum_monotone X a ω (show m+1 ≤ n by omega)
      have h1 : b+t < gaussianLadderSum X a (m+1) ω := hm.2
      have h2 : gaussianLadderSum X a n ω ≤ b := hn.1
      linarith
    · have hmono := gaussianLadderSum_monotone X a ω (show n+1 ≤ m by omega)
      have h1 : b+t < gaussianLadderSum X a (n+1) ω := hn.2
      have h2 : gaussianLadderSum X a m ω ≤ b := hm.1
      linarith
  have hae : {ω | t < gaussianLadderOvershoot X a b ω} =ᵐ[μ] (⋃ n, E n) := by
    filter_upwards [gaussianLadderSum_exists_gt_ae hX hi hG ha haM] with ω hω
    have hiff := gaussianLadderOvershoot_gt_iff X a hb ht (hω b)
    refine propext ?_
    show t < gaussianLadderOvershoot X a b ω ↔ ω ∈ ⋃ n, E n
    rw [Set.mem_iUnion]
    exact hiff
  have htailmeas : Measurable (fun s : ℝ => ν (Ioi (b+t-s))) :=
    (measurable_ladderTail ν).comp (measurable_const.sub measurable_id)
  calc μ {ω | t < gaussianLadderOvershoot X a b ω}
      = μ (⋃ n, E n) := measure_congr hae
    _ = ∑' n : ℕ, μ (E n) := measure_iUnion hdisj hEmeas
    _ = ∑' n : ℕ, ∫⁻ s in Icc (0 : ℝ) b, ν (Ioi (b+t-s)) ∂(measureConvPow ν n) := by
      refine tsum_congr fun n => ?_
      rw [hEdef, hνdef]
      exact gaussianLadderStep_measure hX hi hG ha b t n
    _ = ∫⁻ s in Icc (0 : ℝ) b, ν (Ioi (b+t-s)) ∂(ladderRenewalMeasure ν) := by
      rw [ladderRenewalMeasure, Measure.restrict_sum _ measurableSet_Icc,
        lintegral_sum_measure]
    _ = renewalOvershootTail ν b t := rfl

end SwingRepair
