import PLAStochastic.Index.CEPS.Reward.PathSplit
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Markov

/-! # First-passage rewards and their joint measurability -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def passageReward (s a : ℂ) (x : ℝ) (ω : ℕ → ℝ) : ℂ :=
  if firstEntry (Ioi x) ω < ⊤ then
    s ^ (firstEntry (Ioi x) ω).toNat * cexp (-a * (entryValue (Ioi x) ω - x : ℝ))
  else 0

def passageTransform (ρ : Measure ℝ) (s a : ℂ) (x : ℝ) : ℂ :=
  ∫ ω, passageReward s a x ω ∂pathLaw ρ

theorem measurable_jointFirstEntry :
    Measurable (fun p : ℝ × (ℕ → ℝ) => firstEntry (Ioi p.1) p.2) := by
  apply ENat.measurable_iff.mpr
  intro n
  change MeasurableSet {p : ℝ × (ℕ → ℝ) | firstEntry (Ioi p.1) p.2 = (n : ℕ∞)}
  simp_rw [firstEntry_eq_coe_iff]
  refine measurableSet_setOfPred.mpr (Measurable.and measurable_const
    (Measurable.and ?_ ?_))
  · exact measurable_fst.lt ((measurable_partialSum n).comp measurable_snd)
  · exact Measurable.forall fun j => Measurable.imp measurable_const
      (Measurable.imp measurable_const
        (measurable_fst.lt ((measurable_partialSum j).comp measurable_snd)).not)

theorem measurable_jointEntryValue :
    Measurable (fun p : ℝ × (ℕ → ℝ) => entryValue (Ioi p.1) p.2) :=
  measurable_partialSum_prod.comp (measurable_snd.prodMk
    ((Measurable.of_discrete (f := ENat.toNat)).comp measurable_jointFirstEntry))

theorem measurable_passageReward (s a : ℂ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => passageReward s a p.1 p.2) := by
  apply Measurable.ite
    (measurable_jointFirstEntry (MeasurableSet.of_discrete (s := Iio ⊤)))
  · have hs := (Measurable.of_discrete (f := fun n : ℕ => s ^ n)).comp
      ((Measurable.of_discrete (f := ENat.toNat)).comp measurable_jointFirstEntry)
    have he : Measurable (fun p : ℝ × (ℕ → ℝ) =>
        cexp (-a * (entryValue (Ioi p.1) p.2 - p.1 : ℝ))) := (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_jointEntryValue.sub measurable_fst))).cexp
    exact hs.mul he
  · exact measurable_const

theorem measurable_passageTransform (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (s a : ℂ) :
    Measurable (passageTransform ρ s a) :=
  (measurable_passageReward s a).stronglyMeasurable.integral_prod_right.measurable

theorem norm_passageReward_le_one {s a : ℂ} (hs : ‖s‖ ≤ 1) (ha : 0 ≤ a.re)
    (x : ℝ) (ω : ℕ → ℝ) : ‖passageReward s a x ω‖ ≤ 1 := by
  unfold passageReward
  split_ifs with h
  · have ho : 0 ≤ entryValue (Ioi x) ω - x := sub_nonneg.mpr (entryValue_mem h).le
    rw [norm_mul, norm_pow, norm_exp]
    have he : (-a * (entryValue (Ioi x) ω - x : ℝ)).re ≤ 0 := by
      simp only [mul_re, neg_re, neg_im, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) ho
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hs) (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr he)
  · simp

theorem integrable_passageReward {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {s a : ℂ} (hs : ‖s‖ ≤ 1) (ha : 0 ≤ a.re) (x : ℝ) :
    Integrable (passageReward s a x) (pathLaw ρ) :=
  (integrable_const (1 : ℝ)).mono'
    ((measurable_passageReward s a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Eventually.of_forall (norm_passageReward_le_one hs ha x))

theorem norm_passageTransform_le_one {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {s a : ℂ} (hs : ‖s‖ ≤ 1) (ha : 0 ≤ a.re) (x : ℝ) :
    ‖passageTransform ρ s a x‖ ≤ 1 := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : ℕ → ℝ, (1 : ℝ) ∂pathLaw ρ := integral_mono
      (integrable_passageReward hs ha x).norm (integrable_const _) (norm_passageReward_le_one hs ha x)
    _ = 1 := by simp

theorem passageReward_eq_of_asc_top {s a : ℂ} {x : ℝ} (hx : 0 ≤ x)
    {ω : ℕ → ℝ} (h : firstEntry (Ioi 0) ω = ⊤) : passageReward s a x ω = 0 := by
  simp [passageReward, firstEntry_Ioi_top_of_asc_top hx h]

theorem passageReward_split {s a : ℂ} {x : ℝ} (hx : 0 ≤ x) {ω : ℕ → ℝ} {n : ℕ}
    (hn : firstEntry (Ioi 0) ω = n) :
    passageReward s a x ω = s ^ n *
      (if x < partialSum n ω then cexp (-a * (partialSum n ω - x : ℝ))
       else passageReward s a (x - partialSum n ω) (shift n ω)) := by
  by_cases hh : x < partialSum n ω
  · have he := firstEntry_Ioi_eq_of_asc_above hx hn hh
    simp only [passageReward, he, ENat.natCast_lt_top, if_true, ENat.toNat_natCast,
      entryValue_of_eq he, hh]
  · rw [if_neg hh]
    have hle := not_lt.mp hh
    by_cases ht : firstEntry (Ioi (x - partialSum n ω)) (shift n ω) = ⊤
    · simp [passageReward, ht, firstEntry_Ioi_top_of_shift_top hx hn hle ht]
    · obtain ⟨m, hm⟩ := firstEntry_lt_top_iff.mp (lt_top_iff_ne_top.mpr ht)
      have he := firstEntry_Ioi_eq_add_of_asc_below hx hn hle hm
      have ho := entryOvershoot_eq_shift_of_asc_below hx hn hle hm
      simp only [passageReward, he, hm, ENat.natCast_lt_top, if_true, ENat.toNat_natCast,
        ho, pow_add, mul_assoc]

end PGM.WienerHopf
