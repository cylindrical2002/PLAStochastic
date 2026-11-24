import PLAStochastic.Index.CEPS.StripError.Pass
import PLAStochastic.Index.CEPS.Reward.Main
import PLAStochastic.Index.CEPS.Tails.Cramer

/-!
# WP9: first passages of the band walk as Wiener–Hopf passage transforms

For the gap walk `V_n = kWalk x β a g n` let `ξ g i = a g_i - β`, so that
`V_n = x - S_n(ξ g)` and the reflected walk `kWalk x (-β) (-a) g n = x + S_n(ξ g)`.
If `ν ∘ (a · - β)⁻¹ = ρY`, the increments `ξ g` have the path law `pathLaw ρY`.

* `stripPass_below_eq_passageTransform`: the passage of `V` below `0` from `x ≥ 0` with the
  absolute mark `e^{-tV}` (`Re t ≤ 0`) is the strict upcrossing transform
  `passageTransform ρY (e^{-q}) (-t) x` of W-6;
* `stripPass_reflected_eq_descending`: the passage of the reflected walk below `0` from `x ≥ 0`
  with the mark `e^{-t(l - V')}` (`Re t ≥ 0`) is `e^{-tl}` times the strict downcrossing
  transform `descendingPassageTransform ρY (e^{-q}) t x`;
* `passageTransform_zero_eq_asc`: at `x = 0` the upcrossing transform is the ladder transform.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open WienerHopf

/-! ## The walk in increment coordinates -/

/-- The increments `a g_i - β` of `-V`. -/
def stripIncr (β a : ℝ) (g : ℕ → ℝ) : ℕ → ℝ := fun i => a * g i - β

theorem measurable_stripIncr (β a : ℝ) : Measurable (stripIncr β a) :=
  measurable_pi_lambda _ fun i => (measurable_const.mul (measurable_pi_apply i)).sub_const _

theorem kWalk_eq_sub_partialSum (x β a : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    kWalk x β a g n = x - WienerHopf.partialSum n (stripIncr β a g) := by
  simp only [kWalk, gapKeys, WienerHopf.partialSum, stripIncr, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem kWalk_neg_eq_add_partialSum (x β a : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    kWalk x (-β) (-a) g n = x + WienerHopf.partialSum n (stripIncr β a g) := by
  simp only [kWalk, gapKeys, WienerHopf.partialSum, stripIncr, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem map_iidLaw_stripIncr (ν : ProbabilityMeasure ℝ) (β a : ℝ) :
    (iidLaw ν).map (stripIncr β a) = pathLaw ((ν : Measure ℝ).map fun x => a * x - β) := by
  have h := map_iidLaw_affine ν (-β) (-a)
  have e1 : (fun g : ℕ → ℝ => fun n => -β - -a * g n) = stripIncr β a := by
    funext g n
    simp only [stripIncr]
    ring
  have e2 : (fun x : ℝ => -β - -a * x) = fun x => a * x - β := by
    funext x
    ring
  rw [e1, e2] at h
  exact h

/-! ## Killed indicators as first entrance events -/

open Classical in
theorem krAlive_Ici_exit_eq_firstEntry {x : ℝ} (hx : 0 ≤ x) (β a : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    (krAlive (Ici 0) β a n x g : ℂ) * (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk x β a g (n + 1)) =
      if firstEntry (Ioi x) (stripIncr β a g) = ((n + 1 : ℕ) : ℕ∞) then 1 else 0 := by
  have hiff : firstEntry (Ioi x) (stripIncr β a g) = ((n + 1 : ℕ) : ℕ∞) ↔
      (∀ i ≤ n, kWalk x β a g i ∈ Ici 0) ∧ kWalk x β a g (n + 1) ∈ Iio 0 := by
    rw [firstEntry_eq_coe_iff]
    simp only [kWalk_eq_sub_partialSum, mem_Ici, mem_Iio, mem_Ioi, sub_nonneg, sub_neg]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨fun i hi => ?_, h1⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simpa using hx
      · exact not_lt.mp (h2 i hi0 (by omega))
    · rintro ⟨h1, h2⟩
      exact ⟨Nat.succ_pos n, h2, fun j _ hj hjA => absurd (h1 j (by omega)) (not_le.mpr hjA)⟩
  rw [krAlive_eq_ite]
  by_cases hA : ∀ i ≤ n, kWalk x β a g i ∈ Ici 0
  · by_cases hB : kWalk x β a g (n + 1) ∈ Iio 0
    · rw [if_pos hA, if_pos (hiff.mpr ⟨hA, hB⟩), indicator_of_mem hB]
      simp
    · rw [if_pos hA, if_neg (fun h => hB (hiff.mp h).2), indicator_of_notMem hB]
      simp
  · rw [if_neg hA, if_neg (fun h => hA (hiff.mp h).1)]
    simp

open Classical in
theorem krAlive_Ici_exit_neg_eq_firstEntry {x : ℝ} (hx : 0 ≤ x) (β a : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    (krAlive (Ici 0) (-β) (-a) n x g : ℂ) *
        (Iio 0).indicator (fun _ => (1 : ℂ)) (kWalk x (-β) (-a) g (n + 1)) =
      if firstEntry (Iio (-x)) (stripIncr β a g) = ((n + 1 : ℕ) : ℕ∞) then 1 else 0 := by
  have hiff : firstEntry (Iio (-x)) (stripIncr β a g) = ((n + 1 : ℕ) : ℕ∞) ↔
      (∀ i ≤ n, kWalk x (-β) (-a) g i ∈ Ici 0) ∧ kWalk x (-β) (-a) g (n + 1) ∈ Iio 0 := by
    rw [firstEntry_eq_coe_iff]
    simp only [kWalk_neg_eq_add_partialSum, mem_Ici, mem_Iio]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨fun i hi => ?_, by linarith⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simpa using hx
      · have := h2 i hi0 (by omega)
        push Not at this
        linarith
    · rintro ⟨h1, h2⟩
      exact ⟨Nat.succ_pos n, by linarith, fun j _ hj hjA => by
        have := h1 j (by omega)
        linarith⟩
  rw [krAlive_eq_ite]
  by_cases hA : ∀ i ≤ n, kWalk x (-β) (-a) g i ∈ Ici 0
  · by_cases hB : kWalk x (-β) (-a) g (n + 1) ∈ Iio 0
    · rw [if_pos hA, if_pos (hiff.mpr ⟨hA, hB⟩), indicator_of_mem hB]
      simp
    · rw [if_pos hA, if_neg (fun h => hB (hiff.mp h).2), indicator_of_notMem hB]
      simp
  · rw [if_neg hA, if_neg (fun h => hA (hiff.mp h).1)]
    simp

/-! ## Sums over the first entrance time -/

open Classical in
theorem tsum_ite_firstEntry_eq (A : Set ℝ) (ω : ℕ → ℝ) (F : ℕ → ℂ) :
    ∑' n : ℕ, (if firstEntry A ω = ((n + 1 : ℕ) : ℕ∞) then F n else 0) =
      if firstEntry A ω < ⊤ then F ((firstEntry A ω).toNat - 1) else 0 := by
  by_cases h : firstEntry A ω < ⊤
  · rw [if_pos h]
    obtain ⟨N, hN⟩ := firstEntry_lt_top_iff.mp h
    have hN0 : N ≠ 0 := by
      rintro rfl
      exact firstEntry_ne_zero (by simpa using hN)
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hN0
    rw [tsum_eq_single M fun n hn => by
      rw [if_neg]
      rw [hN]
      intro h'
      exact hn (by have := Nat.cast_injective h'; omega)]
    rw [if_pos hN, hN, ENat.toNat_natCast, Nat.add_sub_cancel]
  · rw [if_neg h]
    have : ∀ n : ℕ, firstEntry A ω ≠ ((n + 1 : ℕ) : ℕ∞) := fun n hn =>
      h (by rw [hn]; exact ENat.natCast_lt_top _)
    exact (tsum_congr fun n => if_neg (this n)).trans tsum_zero

open Classical in
theorem passageReward_eq_tsum (s a : ℂ) (x : ℝ) (ω : ℕ → ℝ) :
    passageReward s a x ω = ∑' n : ℕ, (if firstEntry (Ioi x) ω = ((n + 1 : ℕ) : ℕ∞) then
      s ^ (n + 1) * Complex.exp (-a * ((WienerHopf.partialSum (n + 1) ω - x : ℝ) : ℂ)) else 0) := by
  rw [tsum_ite_firstEntry_eq]
  unfold passageReward
  by_cases h : firstEntry (Ioi x) ω < ⊤
  · rw [if_pos h, if_pos h]
    obtain ⟨N, hN⟩ := firstEntry_lt_top_iff.mp h
    have hN0 : N ≠ 0 := by
      rintro rfl
      exact firstEntry_ne_zero (by simpa using hN)
    rw [hN, entryValue_of_eq hN]
    simp only [ENat.toNat_natCast]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0)]
  · rw [if_neg h, if_neg h]

open Classical in
theorem descendingPassageReward_eq_tsum (s a : ℂ) (x : ℝ) (ω : ℕ → ℝ) :
    descendingPassageReward s a x ω = ∑' n : ℕ, (if firstEntry (Iio (-x)) ω = ((n + 1 : ℕ) : ℕ∞) then
      s ^ (n + 1) * Complex.exp (-a * ((-WienerHopf.partialSum (n + 1) ω - x : ℝ) : ℂ)) else 0) := by
  rw [tsum_ite_firstEntry_eq]
  unfold descendingPassageReward
  by_cases h : firstEntry (Iio (-x)) ω < ⊤
  · rw [if_pos h, if_pos h]
    obtain ⟨N, hN⟩ := firstEntry_lt_top_iff.mp h
    have hN0 : N ≠ 0 := by
      rintro rfl
      exact firstEntry_ne_zero (by simpa using hN)
    rw [hN, entryValue_of_eq hN]
    simp only [ENat.toNat_natCast]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0)]
  · rw [if_neg h, if_neg h]

/-! ## The translation -/

/-- A series of first-entrance terms bounded by the entrance indicators can be integrated
termwise. -/
theorem integral_tsum_firstEntry {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P] (A : Set ℝ)
    (hA : MeasurableSet A) {F : ℕ → (ℕ → ℝ) → ℂ} (hFm : ∀ n, Measurable (F n))
    (hF : ∀ n ω, ‖F n ω‖ ≤ 1) :
    ∫ ω, ∑' n : ℕ, (if firstEntry A ω = ((n + 1 : ℕ) : ℕ∞) then F n ω else 0) ∂P =
      ∑' n : ℕ, ∫ ω, (if firstEntry A ω = ((n + 1 : ℕ) : ℕ∞) then F n ω else 0) ∂P := by
  classical
  have hmeas : ∀ n : ℕ, Measurable fun ω =>
      (if firstEntry A ω = ((n + 1 : ℕ) : ℕ∞) then F n ω else 0) := fun n =>
    Measurable.ite (measurableSet_firstEntry_eq hA (n + 1)) (hFm n) measurable_const
  rw [integral_tsum (fun n => (hmeas n).aestronglyMeasurable)]
  refine ne_top_of_le_ne_top (b := ∫⁻ _ : ℕ → ℝ, 1 ∂P) (by simp) ?_
  rw [← lintegral_tsum fun n => (hmeas n).enorm.aemeasurable]
  refine lintegral_mono fun ω => ?_
  have hle : ∀ n : ℕ, ‖(if firstEntry A ω = ((n + 1 : ℕ) : ℕ∞) then F n ω else 0)‖ₑ ≤
      (if firstEntry A ω = ((n + 1 : ℕ) : ℕ∞) then (1 : ENNReal) else 0) := by
    intro n
    split_ifs
    · rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (hF n ω)
    · simp
  refine (ENNReal.tsum_le_tsum hle).trans ?_
  by_cases h : firstEntry A ω < ⊤
  · obtain ⟨N, hN⟩ := firstEntry_lt_top_iff.mp h
    by_cases hN0 : N = 0
    · subst hN0
      exact absurd (by simpa using hN) firstEntry_ne_zero
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hN0
    rw [tsum_eq_single M fun n hn => by
      rw [if_neg]
      rw [hN]
      intro h'
      exact hn (by have := Nat.cast_injective h'; omega)]
    simp [hN]
  · have : ∀ n : ℕ, firstEntry A ω ≠ ((n + 1 : ℕ) : ℕ∞) := fun n hn =>
      h (by rw [hn]; exact ENat.natCast_lt_top _)
    rw [(tsum_congr fun n => if_neg (this n)).trans tsum_zero]
    exact zero_le_one

theorem norm_cexp_neg_q_pow_le {q : ℂ} (hq : 0 ≤ q.re) (n : ℕ) :
    ‖Complex.exp (-q) ^ n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr (by simp; linarith))

theorem cexp_neg_mul_succ_eq_pow (q : ℂ) (n : ℕ) :
    Complex.exp (-q * ((n : ℂ) + 1)) = Complex.exp (-q) ^ (n + 1) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Translation of the passage below `0`.** -/
theorem stripPass_below_eq_passageTransform (ν : ProbabilityMeasure ℝ) (β a : ℝ) {x : ℝ}
    (hx : 0 ≤ x) {t q : ℂ} (ht : t.re ≤ 0) (hq : 0 ≤ q.re) :
    stripPass ν (Ici 0) (Iio 0) β a x (fun v => Complex.exp (-t * (v : ℂ))) q =
      passageTransform ((ν : Measure ℝ).map fun x => a * x - β) (Complex.exp (-q)) (-t) x := by
  classical
  have : IsProbabilityMeasure ((ν : Measure ℝ).map fun x => a * x - β) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hmark : ∀ ω : ℕ → ℝ, ∀ n : ℕ,
      ‖Complex.exp (-q) ^ (n + 1) * Complex.exp (-(-t) * ((WienerHopf.partialSum (n + 1) ω - x : ℝ) : ℂ))‖ ≤ 1
        ∨ firstEntry (Ioi x) ω ≠ ((n + 1 : ℕ) : ℕ∞) := by
    intro ω n
    by_cases hN : firstEntry (Ioi x) ω = ((n + 1 : ℕ) : ℕ∞)
    · left
      have hS := (firstEntry_eq_coe_iff.mp hN).2.1
      simp only [mem_Ioi] at hS
      rw [norm_mul]
      refine mul_le_one₀ (norm_cexp_neg_q_pow_le hq _) (norm_nonneg _) ?_
      rw [Complex.norm_exp]
      refine Real.exp_le_one_iff.mpr ?_
      simp only [neg_neg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg ht (by linarith)
    · right
      exact hN
  -- the termwise functions with a cut-off making them bounded everywhere
  set F : ℕ → (ℕ → ℝ) → ℂ := fun n ω =>
    if firstEntry (Ioi x) ω = ((n + 1 : ℕ) : ℕ∞) then
      Complex.exp (-q) ^ (n + 1) * Complex.exp (-(-t) * ((WienerHopf.partialSum (n + 1) ω - x : ℝ) : ℂ))
    else 0 with hFdef
  have hFm : ∀ n, Measurable (F n) := fun n =>
    Measurable.ite (measurableSet_firstEntry_eq measurableSet_Ioi (n + 1))
      (measurable_const.mul (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_partialSum (n + 1)).sub_const x)))))
      measurable_const
  have hF1 : ∀ n ω, ‖F n ω‖ ≤ 1 := by
    intro n ω
    simp only [hFdef]
    split_ifs with h
    · exact (hmark ω n).resolve_right (not_not.mpr h)
    · simp
  have hFeq : ∀ ω, passageReward (Complex.exp (-q)) (-t) x ω =
      ∑' n : ℕ, (if firstEntry (Ioi x) ω = ((n + 1 : ℕ) : ℕ∞) then F n ω else 0) := by
    intro ω
    rw [passageReward_eq_tsum]
    refine tsum_congr fun n => ?_
    simp only [hFdef]
    split_ifs <;> rfl
  unfold passageTransform
  simp_rw [hFeq]
  rw [integral_tsum_firstEntry (Ioi x) measurableSet_Ioi hFm hF1]
  unfold stripPass
  refine tsum_congr fun n => ?_
  have hGm : Measurable fun ω : ℕ → ℝ =>
      (if firstEntry (Ioi x) ω = ((n + 1 : ℕ) : ℕ∞) then F n ω else 0) :=
    Measurable.ite (measurableSet_firstEntry_eq measurableSet_Ioi (n + 1)) (hFm n) measurable_const
  rw [← map_iidLaw_stripIncr, integral_map (measurable_stripIncr β a).aemeasurable
    hGm.aestronglyMeasurable]
  unfold stripPassTerm
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [mul_assoc, ← mul_assoc ((krAlive (Ici 0) β a n x g : ℂ)),
    krAlive_Ici_exit_eq_firstEntry hx]
  simp only [hFdef]
  split_ifs with h
  · rw [cexp_neg_mul_succ_eq_pow, kWalk_eq_sub_partialSum]
    have he : Complex.exp (-t * ((x - WienerHopf.partialSum (n + 1) (stripIncr β a g) : ℝ) : ℂ)) =
        Complex.exp (- -t * ((WienerHopf.partialSum (n + 1) (stripIncr β a g) - x : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [he]
    ring
  · simp

/-- **Translation of the reflected passage.** -/
theorem stripPass_reflected_eq_descending (ν : ProbabilityMeasure ℝ) (β a l : ℝ) {x : ℝ}
    (hx : 0 ≤ x) {t q : ℂ} (ht : 0 ≤ t.re) (hq : 0 ≤ q.re) :
    stripPass ν (Ici 0) (Iio 0) (-β) (-a) x
        (fun v => Complex.exp (-t * ((l - v : ℝ) : ℂ))) q =
      Complex.exp (-t * (l : ℂ)) * descendingPassageTransform
        ((ν : Measure ℝ).map fun x => a * x - β) (Complex.exp (-q)) t x := by
  classical
  have : IsProbabilityMeasure ((ν : Measure ℝ).map fun x => a * x - β) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  set F : ℕ → (ℕ → ℝ) → ℂ := fun n ω =>
    if firstEntry (Iio (-x)) ω = ((n + 1 : ℕ) : ℕ∞) then
      Complex.exp (-q) ^ (n + 1) * Complex.exp (-t * ((-WienerHopf.partialSum (n + 1) ω - x : ℝ) : ℂ))
    else 0 with hFdef
  have hFm : ∀ n, Measurable (F n) := fun n =>
    Measurable.ite (measurableSet_firstEntry_eq measurableSet_Iio (n + 1))
      (measurable_const.mul (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp (((measurable_partialSum (n + 1)).neg).sub_const x)))))
      measurable_const
  have hF1 : ∀ n ω, ‖F n ω‖ ≤ 1 := by
    intro n ω
    simp only [hFdef]
    split_ifs with h
    · have hS := (firstEntry_eq_coe_iff.mp h).2.1
      simp only [mem_Iio] at hS
      rw [norm_mul]
      refine mul_le_one₀ (norm_cexp_neg_q_pow_le hq _) (norm_nonneg _) ?_
      rw [Complex.norm_exp]
      refine Real.exp_le_one_iff.mpr ?_
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith
    · simp
  have hFeq : ∀ ω, descendingPassageReward (Complex.exp (-q)) t x ω =
      ∑' n : ℕ, (if firstEntry (Iio (-x)) ω = ((n + 1 : ℕ) : ℕ∞) then F n ω else 0) := by
    intro ω
    rw [descendingPassageReward_eq_tsum]
    refine tsum_congr fun n => ?_
    simp only [hFdef]
    split_ifs <;> rfl
  unfold descendingPassageTransform
  simp_rw [hFeq]
  rw [integral_tsum_firstEntry (Iio (-x)) measurableSet_Iio hFm hF1]
  unfold stripPass
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hGm : Measurable fun ω : ℕ → ℝ =>
      (if firstEntry (Iio (-x)) ω = ((n + 1 : ℕ) : ℕ∞) then F n ω else 0) :=
    Measurable.ite (measurableSet_firstEntry_eq measurableSet_Iio (n + 1)) (hFm n) measurable_const
  rw [← map_iidLaw_stripIncr, integral_map (measurable_stripIncr β a).aemeasurable
    hGm.aestronglyMeasurable]
  unfold stripPassTerm
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [mul_assoc, ← mul_assoc ((krAlive (Ici 0) (-β) (-a) n x g : ℂ)),
    krAlive_Ici_exit_neg_eq_firstEntry hx]
  simp only [hFdef]
  split_ifs with h
  · rw [cexp_neg_mul_succ_eq_pow, kWalk_neg_eq_add_partialSum]
    have he : Complex.exp (-t * ((l - (x + WienerHopf.partialSum (n + 1) (stripIncr β a g)) : ℝ) : ℂ)) =
        Complex.exp (-t * (l : ℂ)) *
          Complex.exp (-t * ((-WienerHopf.partialSum (n + 1) (stripIncr β a g) - x : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  · simp

/-- At `x = 0` the upcrossing transform is the strict ascending ladder transform. -/
theorem passageTransform_zero_eq_asc (ρ : Measure ℝ) (s a : ℂ) :
    passageTransform ρ s a 0 = ascTransform ρ s (-a) := by
  classical
  unfold passageTransform ascTransform entryTransform
  rw [← integral_indicator (measurableSet_firstEntry_lt_top measurableSet_Ioi)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  unfold passageReward
  by_cases h : firstEntry (Ioi 0) ω < ⊤
  · rw [if_pos h, indicator_of_mem (show ω ∈ {ω | firstEntry (Ioi 0) ω < ⊤} from h)]
    simp
  · rw [if_neg h, indicator_of_notMem (show ω ∉ {ω | firstEntry (Ioi 0) ω < ⊤} from h)]

end

end PGM
