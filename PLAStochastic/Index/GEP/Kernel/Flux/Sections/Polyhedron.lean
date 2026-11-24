import PLAStochastic.Index.GEP.Kernel.Flux.Sections.LinearEndpoint

/-!
# Finite affine-inequality sections and their actual endpoint measures

The coefficients of the varied coordinate are deterministic.  The remaining
coordinates enter through measurable right-hand sides.  Positive, negative,
and zero coefficients are kept separate, including empty and unbounded sections.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter Finset

/-- A measurable choice among candidates with positive-local absolutely
continuous laws preserves positive-local absolute continuity. -/
theorem fluxEndpoint_local_ac_selection {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] (P : Measure Ω) {F : ι → Ω → ℝ} {E : Ω → ℝ}
    (hF : ∀ i, Measurable (F i)) (hE : Measurable E)
    (hac : ∀ i, (P.map (F i)).restrict (Ioi 0) ≪ volume)
    (hsel : ∀ᵐ ω ∂P, 0 < E ω → ∃ i, E ω = F i ω) :
    (P.map E).restrict (Ioi 0) ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.restrict_apply hs, Measure.map_apply hE (hs.inter measurableSet_Ioi)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  have havoid : ∀ᵐ ω ∂P, ∀ i, ¬ (F i ω ∈ s ∧ 0 < F i ω) := by
    rw [ae_all_iff]
    intro i
    have hi := hac i hs0
    rw [Measure.restrict_apply hs, Measure.map_apply (hF i) (hs.inter measurableSet_Ioi)] at hi
    exact measure_eq_zero_iff_ae_notMem.mp hi
  filter_upwards [havoid, hsel] with ω hω hselω
  rintro ⟨hsω, hpos⟩
  obtain ⟨i, hi⟩ := hselω hpos
  exact hω i ⟨hi ▸ hsω, hi ▸ hpos⟩

/-- Any finite homogeneous linear form has a positive-local density.  If all
coefficients vanish its law is concentrated at zero, which contributes no
mass on the open positive half-line. -/
theorem flux_infinitePi_linear_ac_positive {μ : ℕ → Measure ℝ}
    [∀ l, IsProbabilityMeasure (μ l)] (T : Finset ℕ) (c : ℕ → ℝ)
    (hac : ∀ m ∈ T, μ m ≪ volume) :
    ((Measure.infinitePi μ).map (fun g : ℕ → ℝ => ∑ l ∈ T, c l * g l)).restrict (Ioi 0) ≪
      volume := by
  classical
  by_cases h : ∃ m ∈ T, c m ≠ 0
  · obtain ⟨m, hm, hcm⟩ := h
    exact Measure.absolutelyContinuous_restrict.trans
      (flux_infinitePi_linear_ac hm hcm (hac m hm))
  · have hc : ∀ m ∈ T, c m = 0 := by simpa only [not_exists, not_and, not_not] using h
    have hf : (fun g : ℕ → ℝ => ∑ l ∈ T, c l * g l) = fun _ => (0 : ℝ) := by
      funext g
      exact sum_eq_zero fun m hm => by rw [hc m hm, zero_mul]
    rw [hf, Measure.map_const, measure_univ, one_smul, restrict_dirac]
    simp

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

def fluxNeg (c : ι → ℝ) : Finset ι := univ.filter fun q => c q < 0
def fluxPos (c : ι → ℝ) : Finset ι := univ.filter fun q => 0 < c q

/-- The lower endpoint includes the positive-gap boundary zero. -/
def fluxPolyLower (c : ι → ℝ) (d : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  if h : (fluxNeg c).Nonempty then max 0 ((fluxNeg c).sup' h fun q => d q ω / c q) else 0

/-- The finite upper endpoint, used only when a positive coefficient exists. -/
def fluxPolyUpper (c : ι → ℝ) (d : ι → Ω → ℝ) (h : (fluxPos c).Nonempty) (ω : Ω) : ℝ :=
  (fluxPos c).inf' h fun q => d q ω / c q

omit [MeasurableSpace Ω] in
theorem fluxPolyLower_nonneg (c : ι → ℝ) (d : ι → Ω → ℝ) (ω : Ω) :
    0 ≤ fluxPolyLower c d ω := by
  unfold fluxPolyLower
  split
  · exact le_max_left _ _
  · exact le_rfl

theorem measurable_fluxPolyLower (c : ι → ℝ) {d : ι → Ω → ℝ}
    (hd : ∀ q, Measurable (d q)) : Measurable (fluxPolyLower c d) := by
  unfold fluxPolyLower
  split_ifs with h
  · apply measurable_const.max
    have hh : Measurable (fun ω => ((fluxNeg c).sup' h (fun q ω => d q ω / c q)) ω) :=
      Finset.measurable_sup' h fun q _ => (hd q).div_const (c q)
    simpa only [Finset.sup'_apply] using hh
  · exact measurable_const

theorem measurable_fluxPolyUpper (c : ι → ℝ) {d : ι → Ω → ℝ}
    (hd : ∀ q, Measurable (d q)) (h : (fluxPos c).Nonempty) :
    Measurable (fluxPolyUpper c d h) := by
  have he : fluxPolyUpper c d h = (fluxPos c).inf' h (fun q ω => d q ω / c q) := by
    funext ω
    exact (Finset.inf'_apply h (fun q ω => d q ω / c q) ω).symm
  rw [he]
  exact Finset.inf'_induction h _ (fun _ hf _ hg => hf.inf hg)
    (fun q _ => (hd q).div_const (c q))

omit [MeasurableSpace Ω] in
theorem fluxPolyLower_le_iff (c : ι → ℝ) (d : ι → Ω → ℝ) (ω : Ω) {x : ℝ} (hx : 0 ≤ x) :
    fluxPolyLower c d ω ≤ x ↔ ∀ q, c q < 0 → c q * x ≤ d q ω := by
  classical
  unfold fluxPolyLower
  split_ifs with h
  · rw [max_le_iff, and_iff_right hx, Finset.sup'_le_iff]
    simp only [fluxNeg, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall_congr'
    intro q
    constructor <;> intro hq hc
    · simpa only [mul_comm] using (div_le_iff_of_neg hc).mp (hq hc)
    · exact (div_le_iff_of_neg hc).mpr (by simpa only [mul_comm] using hq hc)
  · simp only [hx, true_iff]
    intro q hc
    exact False.elim (h ⟨q, by simp [fluxNeg, hc]⟩)

omit [MeasurableSpace Ω] in
theorem le_fluxPolyUpper_iff (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : (fluxPos c).Nonempty) (ω : Ω) (x : ℝ) :
    x ≤ fluxPolyUpper c d h ω ↔ ∀ q, 0 < c q → c q * x ≤ d q ω := by
  rw [fluxPolyUpper, Finset.le_inf'_iff]
  simp only [fluxPos, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro q
  constructor <;> intro hq hc
  · have := (le_div_iff₀ hc).mp (hq hc)
    simpa only [mul_comm] using this
  · exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hq hc)

/-- The zero-coefficient inequalities are a genuine feasibility condition. -/
def fluxPolyZeroOK (c : ι → ℝ) (d : ι → Ω → ℝ) : Set Ω :=
  {ω | ∀ q, c q = 0 → 0 ≤ d q ω}

theorem measurableSet_fluxPolyZeroOK (c : ι → ℝ) {d : ι → Ω → ℝ}
    (hd : ∀ q, Measurable (d q)) : MeasurableSet (fluxPolyZeroOK c d) := by
  unfold fluxPolyZeroOK
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  by_cases hc : c q = 0
  · simpa only [hc, forall_true_left] using measurableSet_le measurable_const (hd q)
  · simp only [hc, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

omit [MeasurableSpace Ω] in
/-- Exact bounded section, including the nonempty condition through its two endpoints. -/
theorem fluxPoly_iff_interval (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : (fluxPos c).Nonempty) (ω : Ω) {x : ℝ} (hx : 0 < x) :
    (∀ q, c q * x ≤ d q ω) ↔
      ω ∈ fluxPolyZeroOK c d ∧ fluxPolyLower c d ω ≤ x ∧ x ≤ fluxPolyUpper c d h ω := by
  rw [fluxPolyLower_le_iff c d ω hx.le, le_fluxPolyUpper_iff]
  constructor
  · intro H
    exact ⟨fun q hq => by simpa only [hq, zero_mul] using H q,
      fun q _ => H q, fun q _ => H q⟩
  · rintro ⟨h0, hn, hp⟩ q
    rcases lt_trichotomy (c q) 0 with hq | hq | hq
    · exact hn q hq
    · simpa only [hq, zero_mul] using h0 q hq
    · exact hp q hq

omit [MeasurableSpace Ω] in
/-- If there are no positive coefficients, the section is a half-line. -/
theorem fluxPoly_iff_halfLine (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : ¬ (fluxPos c).Nonempty) (ω : Ω) {x : ℝ} (hx : 0 < x) :
    (∀ q, c q * x ≤ d q ω) ↔ ω ∈ fluxPolyZeroOK c d ∧ fluxPolyLower c d ω ≤ x := by
  rw [fluxPolyLower_le_iff c d ω hx.le]
  constructor
  · intro H
    exact ⟨fun q hq => by simpa only [hq, zero_mul] using H q, fun q _ => H q⟩
  · rintro ⟨h0, hn⟩ q
    rcases lt_trichotomy (c q) 0 with hq | hq | hq
    · exact hn q hq
    · simpa only [hq, zero_mul] using h0 q hq
    · exact False.elim (h ⟨q, by simp [fluxPos, hq]⟩)

end

end PGM
