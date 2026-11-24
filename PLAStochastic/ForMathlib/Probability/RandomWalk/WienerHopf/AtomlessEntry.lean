import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LadderHeight

/-! # Strict and weak barrier entrances agree for steps with a density -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Complex Filter
namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {f : ℝ → ℝ}

/-- Every finite entrance has an atomless height law, including at the barrier itself. -/
theorem ae_entryHeight_ne (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    {B : Set ℝ} (hB : MeasurableSet B) (c : ℝ) :
    ∀ᶠ ω in ae (pathLaw ρ), ∀ n : ℕ, firstEntry B ω = n → partialSum n ω ≠ c := by
  apply ae_all_iff.mpr
  intro n
  cases n with
  | zero =>
    exact Eventually.of_forall fun _ hn => False.elim (firstEntry_ne_zero hn)
  | succ n =>
    have hm := congrArg (fun ν : Measure ℝ => ν {c})
      (map_firstEntry_succ_eq_withDensity (ρ := ρ) hB hfm hρ n)
    have hz : (volume.withDensity (B.indicator (ladderKernelENN ρ f B n))) {c} = 0 :=
      measure_singleton c
    rw [hz] at hm
    rw [Measure.map_apply (measurable_partialSum _)
      (measurableSet_singleton c), Measure.restrict_apply
      ((measurableSet_singleton c).preimage (measurable_partialSum _))] at hm
    rw [ae_iff]
    simpa [Set.preimage, Set.inter_def, and_comm] using hm


theorem ae_firstEntry_Iic_eq_Iio (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y))) (c : ℝ) :
    firstEntry (Iic c) =ᶠ[ae (pathLaw ρ)] firstEntry (Iio c) := by
  filter_upwards [ae_entryHeight_ne hfm hρ measurableSet_Iic c] with ω hω
  by_cases ht : firstEntry (Iic c) ω = ⊤
  · have hs : firstEntry (Iio c) ω = ⊤ := by
      by_contra hn
      obtain ⟨n, he⟩ := firstEntry_lt_top_iff.mp (lt_top_iff_ne_top.mpr hn)
      obtain ⟨hn0, hnc, _⟩ := firstEntry_eq_coe_iff.mp he
      have hb : (n : ℕ∞) < firstEntry (Iic c) ω := by rw [ht]; exact ENat.natCast_lt_top n
      exact coe_lt_firstEntry_iff.mp hb n hn0 le_rfl (show partialSum n ω ≤ c from (show partialSum n ω < c from hnc).le)
    rw [ht, hs]
  · obtain ⟨n, hn⟩ := firstEntry_lt_top_iff.mp (lt_top_iff_ne_top.mpr ht)
    obtain ⟨hn0, hnc, hbefore⟩ := firstEntry_eq_coe_iff.mp hn
    have hs : firstEntry (Iio c) ω = n := firstEntry_eq_coe_iff.mpr
      ⟨hn0, lt_of_le_of_ne hnc (hω n hn), fun j hj hjn hjc => hbefore j hj hjn (show partialSum j ω ≤ c from (show partialSum j ω < c from hjc).le)⟩
    rw [hn, hs]

theorem entryTransform_Iic_eq_Iio (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y))) (c : ℝ) (s z : ℂ) :
    entryTransform ρ (Iic c) s z = entryTransform ρ (Iio c) s z := by
  unfold entryTransform
  rw [← integral_indicator (measurableSet_firstEntry_lt_top measurableSet_Iic),
    ← integral_indicator (measurableSet_firstEntry_lt_top measurableSet_Iio)]
  apply integral_congr_ae
  filter_upwards [ae_firstEntry_Iic_eq_Iio hfm hρ c] with ω hω
  simp only [Set.indicator_apply, mem_ofPred_eq, entryValue, hω]

end PGM.WienerHopf
