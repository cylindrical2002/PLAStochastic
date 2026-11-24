import PLAStochastic.Swing.Entrance.Deterministic.Selection

/-!
# The native first-rejection quantities on the local event

For the anchored sample path `y = entrancePath X ω` on the local event
`EntranceLocalEvent y E n T`, the native first segment is identified with the local process
after the cut `n`:

* (E13) the first rejected index is `J = n + T`, i.e. `nativeFirstDuration X E ω = n + T - 1`;
  the rejection side is the cut side, the frozen endpoint is unchanged, and the native
  overshoot `O♮` is the local overshoot;
* (E17)–(E19), G9: the native width `U♮ = N (b_N - a_N)` is exactly the late-constraint width
  and `0 ≤ U♮ - U ≤ (N - n) d_E / n` for the local undershoot `U`;
* (E21)–(E22): the native slope is the clipped least-squares slope; a nonnegative signed area
  `∑_{i ≤ N} i (s y_i - s β i)` selects the frozen endpoint, an area at most `-(U♮/N) ∑ i²`
  selects the active endpoint;
* (E26)–(E27), G13: if `|β| < E` and the native slope is an endpoint, the first margin is
  `R_{1,E} = -O♮ - s♮ β♮ - (if χ♮ then 0 else U♮)` in the native quantities.

Finally the local event follows from the truncated good event `entranceGood` of the cut together
with the window conditions `T ≤ q_E` and `|Q_j| ≤ E/2` for `j ≤ q_E`.
-/

namespace SwingRepair

noncomputable section

variable {Ω : Type*} {X : ℕ → Ω → ℝ} {E : ℝ} {ω : Ω} {n T : ℕ}

/-- The active endpoint at the first rejection: `a_N` for an upper rejection, else `b_N`. -/
def entranceRejectActive (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  let y := entrancePath X ω
  let N := nativeFirstDuration X E ω
  if entranceRejectSide X E ω = 1 then entranceLower y E N else entranceUpper y E N

namespace EntranceLocalEvent

/-- (E13): the first native duration is `N = n + T - 1`. -/
theorem nativeFirstDuration_eq (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    nativeFirstDuration X E ω = n + T - 1 :=
  (nativeFirst_duration_of_threshold X E ω (by have := h.facts.two_le; omega)
    h.nativePrefixFeasible_iff).1

/-- (E13): the first rejected index is `J = N + 1 = n + T`. -/
theorem rejected_index (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    nativeFirstDuration X E ω + 1 = n + T := by
  rw [h.nativeFirstDuration_eq]
  have := h.one_le_crossing
  omega

/-- (E13): the native rejection side is the side of the cut. -/
theorem entranceRejectSide_eq (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    entranceRejectSide X E ω = entranceSide (entrancePath X ω) E n := by
  have hJ := h.rejected_index
  have hO := h.overshoot_eq
  have hOp := h.overshoot_pos
  have hE := h.one_le
  unfold entranceRejectSide
  simp only []
  rw [hJ, h.nativeFirstDuration_eq]
  rcases entranceSide_eq_one_or (y := entrancePath X ω) (E := E) n with hs | hs
  · rw [hs] at hO ⊢
    rw [if_pos]
    rw [h.upper_eq_frozen hs]
    linarith
  · rw [hs] at hO ⊢
    rw [if_neg]
    have hc := h.frozen_mem_cone
    have hJ0 : (0 : ℝ) ≤ ((n + T : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right hc.2 hJ0
    push Not
    linarith

/-- (E13): the native frozen endpoint is the frozen endpoint of the cut. -/
theorem entranceRejectFrozen_eq (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    entranceRejectFrozen X E ω = entranceFrozenSlope (entrancePath X ω) E n := by
  unfold entranceRejectFrozen
  simp only []
  rw [h.entranceRejectSide_eq, h.nativeFirstDuration_eq]
  rcases entranceSide_eq_one_or (y := entrancePath X ω) (E := E) n with hs | hs
  · rw [if_pos hs, h.upper_eq_frozen hs]
  · rw [if_neg (by rw [hs]; norm_num), h.lower_eq_frozen hs]

/-- (E13): the native overshoot `O♮ = s (y_J - β J) - E` is the local overshoot. -/
theorem entranceRejectOvershoot_eq (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    entranceRejectOvershoot X E ω = entranceOvershoot (entrancePath X ω) E n := by
  unfold entranceRejectOvershoot
  simp only []
  rw [h.entranceRejectSide_eq, h.entranceRejectFrozen_eq, h.rejected_index, h.overshoot_eq]

/-- The native active endpoint is `β - s U♮ / N`. -/
theorem entranceRejectActive_eq (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    entranceRejectActive X E ω = entranceFrozenSlope (entrancePath X ω) E n -
      entranceSide (entrancePath X ω) E n *
        (entranceRejectWidth X E ω / (nativeFirstDuration X E ω : ℝ)) := by
  have hNpos : (0 : ℝ) < ((n + T - 1 : ℕ) : ℝ) := by exact_mod_cast h.one_le_last
  unfold entranceRejectActive entranceRejectWidth
  simp only []
  rw [h.entranceRejectSide_eq, h.nativeFirstDuration_eq, entranceWidth]
  rcases entranceSide_eq_one_or (y := entrancePath X ω) (E := E) n with hs | hs
  · rw [if_pos hs, hs, ← h.upper_eq_frozen hs]
    field_simp
    ring
  · rw [if_neg (by rw [hs]; norm_num), hs, ← h.lower_eq_frozen hs]
    field_simp
    ring

/-- (E19), G9: `0 ≤ U♮ - U ≤ (N - n) d_E / n`. -/
theorem entranceRejectWidth_sub_undershoot (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    0 ≤ entranceRejectWidth X E ω - entranceUndershoot (entrancePath X ω) E n ∧
      entranceRejectWidth X E ω - entranceUndershoot (entrancePath X ω) E n ≤
        ((nativeFirstDuration X E ω : ℝ) - n) * entranceCutLevel E / n := by
  unfold entranceRejectWidth
  rw [h.nativeFirstDuration_eq]
  exact ⟨sub_nonneg.mpr h.undershoot_le_width, h.width_sub_undershoot_le⟩

/-- The native first slope is the path-level native slope of the final prefix. -/
theorem nativeFirstSelectedSlope_eq (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    nativeFirstSelectedSlope X E ω =
      entrancePathSlope (entrancePath X ω) E (nativeFirstDuration X E ω) :=
  nativeFirstSelectedSlope_eq_path X E ω (by have := h.facts.two_le; omega)
    h.nativePrefixFeasible_iff

/-- (E21), window part: the rescaled signed area up to `N` differs from the cut area
`entranceGridArea` by at most `E^{-5} (N - n) N E`. -/
theorem area_sub_gridArea_le (h : EntranceLocalEvent (entrancePath X ω) E n T) :
    |E⁻¹ ^ 5 * ∑ i ∈ Finset.Icc 1 (nativeFirstDuration X E ω), (i : ℝ) *
        (entranceSide (entrancePath X ω) E n * entrancePath X ω i -
          entranceSide (entrancePath X ω) E n * entranceFrozenSlope (entrancePath X ω) E n * i) -
      entranceGridArea (entrancePath X ω) E n| ≤
      E⁻¹ ^ 5 * (((nativeFirstDuration X E ω : ℝ) - n) * nativeFirstDuration X E ω * E) := by
  have hE : (0 : ℝ) < E⁻¹ ^ 5 := by have := h.one_le; positivity
  rw [entranceGridArea, ← mul_sub, abs_mul, abs_of_pos hE, h.nativeFirstDuration_eq]
  exact mul_le_mul_of_nonneg_left h.area_sub_cut_area_le hE.le

/-- (E22), frozen branch: a nonnegative signed area selects the frozen endpoint. -/
theorem entranceSelectsFrozen_of_area_nonneg (h : EntranceLocalEvent (entrancePath X ω) E n T)
    (hA : 0 ≤ ∑ i ∈ Finset.Icc 1 (nativeFirstDuration X E ω), (i : ℝ) *
      (entranceSide (entrancePath X ω) E n * entrancePath X ω i -
        entranceSide (entrancePath X ω) E n * entranceFrozenSlope (entrancePath X ω) E n * i)) :
    entranceSelectsFrozen X E ω := by
  unfold entranceSelectsFrozen
  rw [h.nativeFirstSelectedSlope_eq, h.entranceRejectFrozen_eq, h.nativeFirstDuration_eq]
  rw [h.nativeFirstDuration_eq] at hA
  exact h.slope_eq_frozen_of_area_nonneg hA

/-- (E22), active branch: a signed area at most `-(U♮ / N) ∑ i²` selects the active endpoint. -/
theorem selects_active_of_area_le (h : EntranceLocalEvent (entrancePath X ω) E n T)
    (hA : ∑ i ∈ Finset.Icc 1 (nativeFirstDuration X E ω), (i : ℝ) *
      (entranceSide (entrancePath X ω) E n * entrancePath X ω i -
        entranceSide (entrancePath X ω) E n * entranceFrozenSlope (entrancePath X ω) E n * i) ≤
      -(entranceRejectWidth X E ω / (nativeFirstDuration X E ω : ℝ)) *
        ∑ i ∈ Finset.Icc 1 (nativeFirstDuration X E ω), (i : ℝ) ^ 2) :
    nativeFirstSelectedSlope X E ω = entranceRejectActive X E ω := by
  rw [h.entranceRejectActive_eq, h.nativeFirstSelectedSlope_eq]
  unfold entranceRejectWidth at hA ⊢
  rw [h.nativeFirstDuration_eq] at hA ⊢
  exact h.slope_eq_active_of_area_le hA

end EntranceLocalEvent

namespace EntranceLocalEvent

/-- (E26)–(E27): with `s β > -E` the first margin is `-O - s β - N s (β - m_N)`. -/
theorem nativeFirstMargin_eq (h : EntranceLocalEvent (entrancePath X ω) E n T)
    (hβ : -E < entranceSide (entrancePath X ω) E n * entranceFrozenSlope (entrancePath X ω) E n) :
    nativeFirstMargin X E ω = -entranceOvershoot (entrancePath X ω) E n -
      entranceSide (entrancePath X ω) E n * entranceFrozenSlope (entrancePath X ω) E n -
        (nativeFirstDuration X E ω : ℝ) * (entranceSide (entrancePath X ω) E n *
          (entranceFrozenSlope (entrancePath X ω) E n - nativeFirstSelectedSlope X E ω)) := by
  have hK : 1 < n + T := by have := h.facts.two_le; omega
  rw [nativeFirstMargin, nativeFirstNext_eq_path X E ω hK h.nativePrefixFeasible_iff,
    h.nativeFirstSelectedSlope_eq, h.nativeFirstDuration_eq]
  exact h.margin_eq hβ

/-- `-E < s β` as soon as `|β| < E`. -/
theorem neg_lt_side_mul_frozen (y : ℕ → ℝ) (n : ℕ)
    (hβ : |entranceFrozenSlope y E n| < E) :
    -E < entranceSide y E n * entranceFrozenSlope y E n := by
  have := abs_lt.mp hβ
  rcases entranceSide_eq_one_or (y := y) (E := E) n with hs | hs <;> rw [hs] <;> linarith

/-- (E22) and (E27), frozen branch: a nonnegative signed area gives `R_{1,E} = -O♮ - s♮ β♮`. -/
theorem nativeFirstMargin_eq_of_area_nonneg (h : EntranceLocalEvent (entrancePath X ω) E n T)
    (hβ : |entranceFrozenSlope (entrancePath X ω) E n| < E)
    (hA : 0 ≤ ∑ i ∈ Finset.Icc 1 (nativeFirstDuration X E ω), (i : ℝ) *
      (entranceSide (entrancePath X ω) E n * entrancePath X ω i -
        entranceSide (entrancePath X ω) E n * entranceFrozenSlope (entrancePath X ω) E n * i)) :
    entranceSelectsFrozen X E ω ∧
      nativeFirstMargin X E ω = -entranceRejectOvershoot X E ω -
        entranceRejectSide X E ω * entranceRejectFrozen X E ω := by
  have hsel := h.entranceSelectsFrozen_of_area_nonneg hA
  refine ⟨hsel, ?_⟩
  rw [h.nativeFirstMargin_eq (neg_lt_side_mul_frozen _ n hβ), h.entranceRejectOvershoot_eq,
    h.entranceRejectSide_eq, h.entranceRejectFrozen_eq]
  unfold entranceSelectsFrozen at hsel
  rw [hsel, h.entranceRejectFrozen_eq]
  ring

/-- (E22) and (E27), active branch: a signed area at most `-(U♮ / N) ∑ i²` gives
`R_{1,E} = -O♮ - s♮ β♮ - U♮`. -/
theorem nativeFirstMargin_eq_of_area_le (h : EntranceLocalEvent (entrancePath X ω) E n T)
    (hβ : |entranceFrozenSlope (entrancePath X ω) E n| < E)
    (hA : ∑ i ∈ Finset.Icc 1 (nativeFirstDuration X E ω), (i : ℝ) *
      (entranceSide (entrancePath X ω) E n * entrancePath X ω i -
        entranceSide (entrancePath X ω) E n * entranceFrozenSlope (entrancePath X ω) E n * i) ≤
      -(entranceRejectWidth X E ω / (nativeFirstDuration X E ω : ℝ)) *
        ∑ i ∈ Finset.Icc 1 (nativeFirstDuration X E ω), (i : ℝ) ^ 2) :
    nativeFirstSelectedSlope X E ω = entranceRejectActive X E ω ∧
      nativeFirstMargin X E ω = -entranceRejectOvershoot X E ω -
        entranceRejectSide X E ω * entranceRejectFrozen X E ω - entranceRejectWidth X E ω := by
  have hsel := h.selects_active_of_area_le hA
  refine ⟨hsel, ?_⟩
  rw [h.nativeFirstMargin_eq (neg_lt_side_mul_frozen _ n hβ), h.entranceRejectOvershoot_eq,
    h.entranceRejectSide_eq, h.entranceRejectFrozen_eq, hsel, h.entranceRejectActive_eq]
  unfold entranceRejectWidth
  rw [h.nativeFirstDuration_eq, h.active_term_eq]

end EntranceLocalEvent

/-! ## From the truncated good event to the local event -/

/-- The truncation conditions of `entranceGood` hold at the cut. -/
theorem entranceGood_at {y : ℕ → ℝ} {δ M : ℝ} (hgood : entranceGood y E δ M)
    (hcut : entranceCut y E = n) :
    δ * E ^ 2 ≤ n ∧ (n : ℝ) ≤ M * E ^ 2 ∧ |E * entranceFrozenSlope y E n| ≤ M ∧
      entranceCutLevel E / 2 ≤ entranceWidth y E n ∧
        entranceWidth y E n ≤ entranceCutLevel E := by
  obtain ⟨m, hm, h1, h2, h3, h4, h5⟩ := hgood
  have : m = n := by
    rw [hcut] at hm
    exact_mod_cast hm.symm
  subst this
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The good event of the cut with the window conditions `T ≤ q_E` and `|Q_j| ≤ E / 2` for
`j ≤ q_E` gives the local event. -/
theorem entranceLocalEvent_of_good {y : ℕ → ℝ} {δ M : ℝ} (hy0 : y 0 = 0) (hE : 1 ≤ E)
    (hgood : entranceGood y E δ M) (hcut : entranceCut y E = n)
    (hT : entranceCrossing y E n = T) (hTq : T ≤ entranceWindow E)
    (hQ : ∀ j ≤ entranceWindow E, |entranceLocal y E n j| ≤ E / 2) :
    EntranceLocalEvent y E n T := by
  obtain ⟨-, -, -, hD, -⟩ := entranceGood_at hgood hcut
  have hd := entranceCutLevel_pos (show (0 : ℝ) < E by linarith)
  refine ⟨hy0, hE, hcut, by linarith, hT, fun j _ hj => ?_⟩
  have := abs_le.mp (hQ j (by omega))
  linarith

/-- On the good event with `M < E`, the frozen slope satisfies `|β| < E`. -/
theorem abs_entranceFrozenSlope_lt_of_good {y : ℕ → ℝ} {δ M : ℝ} (hE : 1 ≤ E) (hME : M < E)
    (hgood : entranceGood y E δ M) (hcut : entranceCut y E = n) :
    |entranceFrozenSlope y E n| < E := by
  obtain ⟨-, -, hβ, -, -⟩ := entranceGood_at hgood hcut
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < E by linarith)] at hβ
  by_contra hc
  push Not at hc
  nlinarith

end

end SwingRepair
