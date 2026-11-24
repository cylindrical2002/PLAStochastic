import PLAStochastic.ForMathlib.Probability.FirstExceedance.Time

/-!
# Ordered approximation of a first-exceedance lifetime

Pointwise error approximations from below give convergence of their extended
lifetimes. This lemma requires no strict crossing or atomlessness: the lifetime
is defined by the first strict exceedance, and infinity is preserved.
-/

open Filter
open scoped ENNReal NNReal Topology

namespace BrownianAffine

theorem firstExceedance_lt_iff_exists {D : ℝ≥0 → ℝ} {ε : ℝ} {b : ℝ≥0∞} :
    firstExceedance D ε < b ↔ ∃ t : ℝ≥0, ε < D t ∧ (t : ℝ≥0∞) < b := by
  classical
  unfold firstExceedance
  rw [iInf_lt_iff]
  constructor
  · rintro ⟨t, ht⟩
    by_cases hD : ε < D t
    · exact ⟨t, hD, by simpa only [if_pos hD] using ht⟩
    · simp only [if_neg hD, not_top_lt] at ht
  · rintro ⟨t, hD, ht⟩
    exact ⟨t, by simpa only [if_pos hD] using ht⟩

/-- Each late exceedance is eventually detected by a convergent approximation. -/
theorem eventually_firstExceedance_lt {ι : Type*} {l : Filter ι}
    {D : ℝ≥0 → ℝ} {A : ι → ℝ≥0 → ℝ} {ε : ℝ} {b : ℝ≥0∞}
    (hconv : ∀ t, Tendsto (fun i => A i t) l (𝓝 (D t)))
    (hb : firstExceedance D ε < b) :
    ∀ᶠ i in l, firstExceedance (A i) ε < b := by
  obtain ⟨t, hD, ht⟩ := firstExceedance_lt_iff_exists.mp hb
  filter_upwards [(hconv t).eventually_const_lt hD] with i hi
  exact (firstExceedance_le_of_exceeds hi).trans_lt ht

/-- Sampling applications must separately prove the actual error order and
pointwise convergence; no approximation hypothesis is supplied by the lifetime definition. -/
theorem tendsto_firstExceedance_of_ordered_approximation {ι : Type*} {l : Filter ι}
    {D : ℝ≥0 → ℝ} {A : ι → ℝ≥0 → ℝ} (ε : ℝ)
    (hbelow : ∀ i t, A i t ≤ D t)
    (hconv : ∀ t, Tendsto (fun i => A i t) l (𝓝 (D t))) :
    Tendsto (fun i => firstExceedance (A i) ε) l (𝓝 (firstExceedance D ε)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le (firstExceedance_antitone_error (hbelow i))
  · intro b hb
    exact eventually_firstExceedance_lt hconv hb

end BrownianAffine
