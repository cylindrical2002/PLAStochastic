import PLAStochastic.Index.CEPS.Reward.Passage

/-! # First-passage rewards for bounded measurable overshoot tests -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def passageTestReward (s : ℂ) (φ : ℝ → ℂ) (x : ℝ) (ω : ℕ → ℝ) : ℂ :=
  if firstEntry (Ioi x) ω < ⊤ then
    s ^ (firstEntry (Ioi x) ω).toNat * φ (entryValue (Ioi x) ω - x)
  else 0

def passageTestTransform (ρ : Measure ℝ) (s : ℂ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ω, passageTestReward s φ x ω ∂pathLaw ρ

theorem measurable_passageTestReward (s : ℂ) {φ : ℝ → ℂ} (hφ : Measurable φ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => passageTestReward s φ p.1 p.2) := by
  apply Measurable.ite
    (measurable_jointFirstEntry (MeasurableSet.of_discrete (s := Iio ⊤)))
  · exact (((Measurable.of_discrete (f := fun n : ℕ => s ^ n)).comp
      ((Measurable.of_discrete (f := ENat.toNat)).comp measurable_jointFirstEntry)).mul
      (hφ.comp (measurable_jointEntryValue.sub measurable_fst)))
  · exact measurable_const

theorem measurable_passageTestTransform (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (s : ℂ) {φ : ℝ → ℂ} (hφ : Measurable φ) : Measurable (passageTestTransform ρ s φ) :=
  (measurable_passageTestReward s hφ).stronglyMeasurable.integral_prod_right.measurable

theorem norm_passageTestReward_le {s : ℂ} (hs : ‖s‖ ≤ 1) {φ : ℝ → ℂ}
    {B : ℝ} (hB : 0 ≤ B) (hφB : ∀ y, ‖φ y‖ ≤ B) (x : ℝ) (ω : ℕ → ℝ) :
    ‖passageTestReward s φ x ω‖ ≤ B := by
  unfold passageTestReward
  split_ifs
  · rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hs)
      (norm_nonneg _)).trans (by simpa using hφB _)
  · simpa using hB

theorem integrable_passageTestReward {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {s : ℂ} (hs : ‖s‖ ≤ 1) {φ : ℝ → ℂ} (hφ : Measurable φ)
    {B : ℝ} (hB : 0 ≤ B) (hφB : ∀ y, ‖φ y‖ ≤ B) (x : ℝ) :
    Integrable (passageTestReward s φ x) (pathLaw ρ) :=
  (integrable_const B).mono'
    ((measurable_passageTestReward s hφ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Eventually.of_forall (norm_passageTestReward_le hs hB hφB x))

theorem norm_passageTestTransform_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {s : ℂ} (hs : ‖s‖ ≤ 1) {φ : ℝ → ℂ} (hφ : Measurable φ)
    {B : ℝ} (hB : 0 ≤ B) (hφB : ∀ y, ‖φ y‖ ≤ B) (x : ℝ) :
    ‖passageTestTransform ρ s φ x‖ ≤ B := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ _ : ℕ → ℝ, B ∂pathLaw ρ := integral_mono
      (integrable_passageTestReward hs hφ hB hφB x).norm (integrable_const _)
      (norm_passageTestReward_le hs hB hφB x)
    _ = B := by simp

theorem passageTestReward_eq_of_asc_top {s : ℂ} {φ : ℝ → ℂ} {x : ℝ}
    (hx : 0 ≤ x) {ω : ℕ → ℝ} (h : firstEntry (Ioi 0) ω = ⊤) :
    passageTestReward s φ x ω = 0 := by
  simp [passageTestReward, firstEntry_Ioi_top_of_asc_top hx h]

theorem passageTestReward_split {s : ℂ} {φ : ℝ → ℂ} {x : ℝ} (hx : 0 ≤ x)
    {ω : ℕ → ℝ} {n : ℕ} (hn : firstEntry (Ioi 0) ω = n) :
    passageTestReward s φ x ω = s ^ n *
      (if x < partialSum n ω then φ (partialSum n ω - x)
       else passageTestReward s φ (x - partialSum n ω) (shift n ω)) := by
  by_cases hh : x < partialSum n ω
  · have he := firstEntry_Ioi_eq_of_asc_above hx hn hh
    simp only [passageTestReward, he, ENat.natCast_lt_top, if_true, ENat.toNat_natCast,
      entryValue_of_eq he, hh]
  · rw [if_neg hh]
    have hle := not_lt.mp hh
    by_cases ht : firstEntry (Ioi (x - partialSum n ω)) (shift n ω) = ⊤
    · simp [passageTestReward, ht, firstEntry_Ioi_top_of_shift_top hx hn hle ht]
    · obtain ⟨m, hm⟩ := firstEntry_lt_top_iff.mp (lt_top_iff_ne_top.mpr ht)
      have he := firstEntry_Ioi_eq_add_of_asc_below hx hn hle hm
      have ho := entryOvershoot_eq_shift_of_asc_below hx hn hle hm
      simp only [passageTestReward, he, hm, ENat.natCast_lt_top, if_true,
        ENat.toNat_natCast, ho, pow_add, mul_assoc]

end PGM.WienerHopf
