import PLAStochastic.Index.Model.IIDGaps

/-!
# WP4 `SurvivalBound`: the minimal-slope certificate (geometry)

Source: `research/2026-09-28-gep-closure/analytic-response.md` §2 (AR (4)–(5)); task P1 of
`research/2026-09-30-lean-gep-direct-term/task-cert.md`.

For keys `p 0, …, p k` the residual at slope `a` is `r_t(a) = t - a p_t` (`certResid`).  The
*lower slope* of a pair `i < j` is `a_{ij} = (j - i - 2ε) / (p_j - p_i)` (`certSlope`); every slope
of a line of half-width `ε` through the keys is at least `a_{ij}` (`cert_lowerSlope_le_iff`).
The band condition `certBand eps a p k i` says that the residuals `r_t(a)`, `t ≤ k`, lie in
`[r_i(a), r_i(a) + 2ε]`; the pair `(i, j)` is a *certificate* (`certOK`) when the band condition
holds at its own lower slope.  The admissible pairs `i < j ≤ k` with `2ε < j - i` form the finset
`certPairs eps k`.

* A band at any slope gives a line of half-width `ε` (`cert_feasible_of_band`, intercept
  `r_i + ε`); with `p 0 = 0` it keeps `|k - a p_k| ≤ 2ε` (`cert_abs_sub_le_of_band`).
* **Decomposition** (`cert_prefixAffineFeasible_iff`): for `2ε < k` and keys strictly increasing
  on `[0, k]`, the first `k + 1` keys are feasible iff some admissible pair is a certificate.
  Route: take a feasible slope `a₀` and a pair `(i, j)` maximizing the lower slope `a_-`.  Then
  `a_- ≤ a₀`, so `a_-` also respects every upper constraint (the residual difference of a
  reversed pair is increasing in the slope), hence `a_-` is feasible; the pair `(0, k)` makes
  `a_- > 0`, so `j - i > 2ε`; and `r_j(a_-) - r_i(a_-) = 2ε` puts all residuals in
  `[r_i, r_i + 2ε]`.  No sign condition on `ε` and no normalization `p 0 = 0` is needed.
* **Ties** (`cert_slope_eq`, `cert_tie`): the slope of a certificate is feasible, hence at least
  the lower slope of every other pair; two certificates therefore have the same slope `a_-`, i.e.
  `(j - i - 2ε)(p_{j'} - p_{i'}) = (j' - i' - 2ε)(p_j - p_i)`.  Distinctness is not needed.
* Gap form (`cert_lt_gapSegLen_iff`): for positive gaps `g 0, …, g (k-1)` and `2ε < k`,
  `k < gapSegLen eps g` iff some admissible pair is a certificate of `gapKeys g`.
-/

namespace PGM

noncomputable section

open Finset

/-! ## Residuals, lower slopes and certificates -/

/-- The residual `r_t(a) = t - a p_t` of key `t` at slope `a`. -/
def certResid (a : ℝ) (p : ℕ → ℝ) (t : ℕ) : ℝ := (t : ℝ) - a * p t

/-- The lower slope of the pair `(i, j)`: `a_{ij} = (j - i - 2ε) / (p_j - p_i)`. -/
def certSlope (eps : ℝ) (p : ℕ → ℝ) (i j : ℕ) : ℝ := ((j : ℝ) - i - 2 * eps) / (p j - p i)

/-- The band condition at slope `a`: the residuals of the keys `0, …, k` lie in
`[r_i(a), r_i(a) + 2ε]`. -/
def certBand (eps a : ℝ) (p : ℕ → ℝ) (k i : ℕ) : Prop :=
  ∀ t ≤ k, 0 ≤ certResid a p t - certResid a p i ∧ certResid a p t - certResid a p i ≤ 2 * eps

/-- The pair `(i, j)` is a certificate for the keys `p 0, …, p k`: at its lower slope
`a = certSlope eps p i j` all residuals `r_t(a)`, `t ≤ k`, lie in `[r_i(a), r_i(a) + 2ε]`. -/
def certOK (eps : ℝ) (p : ℕ → ℝ) (k i j : ℕ) : Prop :=
  certBand eps (certSlope eps p i j) p k i

/-- `certOK` unfolded: `∀ t ≤ k, 0 ≤ r_t(a) - r_i(a) ≤ 2ε` with `r_t(a) = t - a p_t`,
`a = (j - i - 2ε) / (p_j - p_i)`. -/
theorem certOK_iff {eps : ℝ} {p : ℕ → ℝ} {k i j : ℕ} :
    certOK eps p k i j ↔ ∀ t ≤ k,
      0 ≤ ((t : ℝ) - certSlope eps p i j * p t) - ((i : ℝ) - certSlope eps p i j * p i) ∧
      ((t : ℝ) - certSlope eps p i j * p t) - ((i : ℝ) - certSlope eps p i j * p i) ≤ 2 * eps :=
  Iff.rfl

/-- The admissible certificate pairs: `i < j ≤ k` with `2ε < j - i`. -/
def certPairs (eps : ℝ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (range (k + 1) ×ˢ range (k + 1)).filter fun ij => ij.1 < ij.2 ∧ 2 * eps < (ij.2 : ℝ) - ij.1

theorem mem_certPairs {eps : ℝ} {k : ℕ} {ij : ℕ × ℕ} :
    ij ∈ certPairs eps k ↔ ij.1 < ij.2 ∧ ij.2 ≤ k ∧ 2 * eps < (ij.2 : ℝ) - ij.1 := by
  simp only [certPairs, mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, h3, h4⟩
    exact ⟨h3, by omega, h4⟩
  · rintro ⟨h3, h2, h4⟩
    exact ⟨⟨by omega, by omega⟩, h3, h4⟩

theorem certResid_sub (a : ℝ) (p : ℕ → ℝ) (s t : ℕ) :
    certResid a p t - certResid a p s = ((t : ℝ) - s) - a * (p t - p s) := by
  unfold certResid
  ring

/-- **Lower slope constraint.**  For `p_s < p_t`, the slope `a` keeps the residual rise
`r_t(a) - r_s(a)` at most `2ε` exactly when `a` is at least the lower slope `a_{st}`. -/
theorem cert_lowerSlope_le_iff {eps a : ℝ} {p : ℕ → ℝ} {s t : ℕ} (h : p s < p t) :
    certSlope eps p s t ≤ a ↔ certResid a p t - certResid a p s ≤ 2 * eps := by
  rw [certSlope, div_le_iff₀ (sub_pos.2 h), certResid_sub]
  constructor <;> intro h' <;> linarith

/-- At its own lower slope the pair `(i, j)` has residual rise exactly `2ε`. -/
theorem certResid_sub_certSlope {eps : ℝ} {p : ℕ → ℝ} {i j : ℕ} (h : p i ≠ p j) :
    certResid (certSlope eps p i j) p j - certResid (certSlope eps p i j) p i = 2 * eps := by
  rw [certResid_sub, certSlope, div_mul_cancel₀ _ (sub_ne_zero.2 h.symm)]
  ring

/-- The lower slope of an admissible pair of increasing keys is positive. -/
theorem certSlope_pos {eps : ℝ} {p : ℕ → ℝ} {i j : ℕ} (hL : 2 * eps < (j : ℝ) - i)
    (h : p i < p j) : 0 < certSlope eps p i j :=
  div_pos (by linarith) (sub_pos.2 h)

/-! ## Bands and feasibility -/

/-- A band at any slope `a` is a line of half-width `ε`: slope `a`, intercept `r_i(a) + ε`. -/
theorem cert_feasible_of_band {eps a : ℝ} {p : ℕ → ℝ} {k i : ℕ} (h : certBand eps a p k i) :
    prefixAffineFeasible eps p (k + 1) := by
  refine ⟨a, certResid a p i + eps, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h t (by omega)
  unfold certResid at h1 h2 ⊢
  rw [abs_le]
  constructor <;> linarith

/-- In a band the residuals oscillate by at most `2ε`. -/
theorem cert_band_osc {eps a : ℝ} {p : ℕ → ℝ} {k i : ℕ} (h : certBand eps a p k i) {s t : ℕ}
    (hs : s ≤ k) (ht : t ≤ k) : certResid a p t - certResid a p s ≤ 2 * eps := by
  obtain ⟨_, h2⟩ := h t ht
  obtain ⟨h3, _⟩ := h s hs
  linarith

/-- A band slope is at least the lower slope of every pair of the prefix. -/
theorem cert_lowerSlope_le_of_band {eps a : ℝ} {p : ℕ → ℝ} {k i s t : ℕ}
    (h : certBand eps a p k i) (hs : s ≤ k) (ht : t ≤ k) (hst : p s < p t) :
    certSlope eps p s t ≤ a :=
  (cert_lowerSlope_le_iff hst).2 (cert_band_osc h hs ht)

/-- With `p 0 = 0`, a band at slope `a` keeps the last key near the line: `|k - a p_k| ≤ 2ε`
(the residuals `r_0 = 0` and `r_k` lie in one band of width `2ε`). -/
theorem cert_abs_sub_le_of_band {eps a : ℝ} {p : ℕ → ℝ} {k i : ℕ} (hp0 : p 0 = 0)
    (h : certBand eps a p k i) : |(k : ℝ) - a * p k| ≤ 2 * eps := by
  have h1 := cert_band_osc h (Nat.zero_le k) le_rfl
  have h2 := cert_band_osc h le_rfl (Nat.zero_le k)
  simp only [certResid, hp0, Nat.cast_zero, mul_zero, sub_zero] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- A feasible prefix has a slope whose residuals oscillate by at most `2ε`. -/
theorem cert_osc_of_feasible {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}
    (h : prefixAffineFeasible eps p n) :
    ∃ a, ∀ s < n, ∀ t < n, certResid a p t - certResid a p s ≤ 2 * eps := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a, fun s hs t ht => ?_⟩
  have h1 := (abs_le.mp (hab t ht)).2
  have h2 := (abs_le.mp (hab s hs)).1
  unfold certResid
  linarith

/-! ## The decomposition -/

/-- **Minimal-slope certificate decomposition** (AR (4)–(5)).  If `2ε < k` and the keys are
strictly increasing on `[0, k]`, the first `k + 1` keys admit a line of half-width `ε` iff some
pair `i < j ≤ k` with `2ε < j - i` is a certificate. -/
theorem cert_prefixAffineFeasible_iff {eps : ℝ} {p : ℕ → ℝ} {k : ℕ} (hk : 2 * eps < k)
    (hp : ∀ s t, s < t → t ≤ k → p s < p t) :
    prefixAffineFeasible eps p (k + 1) ↔
      ∃ i j, i < j ∧ j ≤ k ∧ 2 * eps < ((j : ℝ) - i) ∧ certOK eps p k i j := by
  constructor
  · intro hfeas
    obtain ⟨a₀, ha₀⟩ := cert_osc_of_feasible hfeas
    have heps : 0 ≤ eps := by
      obtain ⟨a, b, hab⟩ := hfeas
      exact (abs_nonneg _).trans (hab 0 (Nat.succ_pos k))
    have hk0 : 0 < k := by
      have : (0 : ℝ) < k := by linarith
      exact_mod_cast this
    set Q := (range (k + 1) ×ˢ range (k + 1)).filter fun st : ℕ × ℕ => st.1 < st.2 with hQ
    have hmemQ : ∀ s t, (s, t) ∈ Q ↔ s < t ∧ t ≤ k := by
      intro s t
      simp only [hQ, mem_filter, mem_product, mem_range]
      omega
    have hQne : Q.Nonempty := ⟨(0, k), (hmemQ 0 k).2 ⟨hk0, le_rfl⟩⟩
    obtain ⟨⟨i, j⟩, hijQ, hmax⟩ :=
      Q.exists_max_image (fun st => certSlope eps p st.1 st.2) hQne
    obtain ⟨hij, hjk⟩ := (hmemQ i j).1 hijQ
    have hmax' : ∀ s t, s < t → t ≤ k → certSlope eps p s t ≤ certSlope eps p i j :=
      fun s t hst htk => hmax (s, t) ((hmemQ s t).2 ⟨hst, htk⟩)
    -- the maximal lower slope lies below the feasible slope `a₀`
    have haa₀ : certSlope eps p i j ≤ a₀ :=
      (cert_lowerSlope_le_iff (hp i j hij hjk)).2 (ha₀ i (by omega) j (by omega))
    -- hence it is feasible
    have hosc : ∀ s ≤ k, ∀ t ≤ k,
        certResid (certSlope eps p i j) p t - certResid (certSlope eps p i j) p s ≤ 2 * eps := by
      intro s hs t ht
      rcases lt_trichotomy s t with hst | rfl | hts
      · exact (cert_lowerSlope_le_iff (hp s t hst ht)).1 (hmax' s t hst ht)
      · simp only [sub_self]
        linarith
      · have h1 := ha₀ s (by omega) t (by omega)
        have h2 := hp t s hts hs
        rw [certResid_sub] at h1 ⊢
        nlinarith [mul_nonneg (sub_nonneg.2 haa₀) (sub_nonneg.2 h2.le)]
    -- the pair `(0, k)` makes it positive, so the maximizing pair is admissible
    have hpos : 0 < certSlope eps p i j := by
      have h0k : 0 < certSlope eps p 0 k :=
        certSlope_pos (by push_cast; linarith) (hp 0 k hk0 le_rfl)
      exact h0k.trans_le (hmax' 0 k hk0 le_rfl)
    have hL : 2 * eps < (j : ℝ) - i := by
      have hd := sub_pos.2 (hp i j hij hjk)
      have := (div_pos_iff_of_pos_right hd).1 hpos
      linarith
    refine ⟨i, j, hij, hjk, hL, fun t ht => ⟨?_, hosc i (by omega) t ht⟩⟩
    have hrise := certResid_sub_certSlope (eps := eps) (hp i j hij hjk).ne
    have := hosc t ht j hjk
    linarith
  · rintro ⟨i, j, -, -, -, h⟩
    exact cert_feasible_of_band h

/-- The decomposition for strictly increasing keys. -/
theorem cert_prefixAffineFeasible_iff_of_strictMono {eps : ℝ} {p : ℕ → ℝ} {k : ℕ}
    (hk : 2 * eps < k) (hp : StrictMono p) :
    prefixAffineFeasible eps p (k + 1) ↔
      ∃ i j, i < j ∧ j ≤ k ∧ 2 * eps < ((j : ℝ) - i) ∧ certOK eps p k i j :=
  cert_prefixAffineFeasible_iff hk fun _ _ h _ => hp h

/-! ## Ties -/

/-- **Ties.**  Two certificates (pairs of `[0, k]`, keys strictly increasing on `[0, k]`) have the
same slope: each certificate slope is feasible, hence at least the other lower slope. -/
theorem cert_slope_eq {eps : ℝ} {p : ℕ → ℝ} {k i j i' j' : ℕ}
    (hp : ∀ s t, s < t → t ≤ k → p s < p t) (hij : i < j) (hj : j ≤ k) (hij' : i' < j')
    (hj' : j' ≤ k) (h : certOK eps p k i j) (h' : certOK eps p k i' j') :
    certSlope eps p i j = certSlope eps p i' j' :=
  le_antisymm (cert_lowerSlope_le_of_band h' (by omega) hj (hp i j hij hj))
    (cert_lowerSlope_le_of_band h (by omega) hj' (hp i' j' hij' hj'))

/-- **Ties, cross-multiplied.**  Two certificates satisfy
`(j - i - 2ε)(p_{j'} - p_{i'}) = (j' - i' - 2ε)(p_j - p_i)`. -/
theorem cert_tie {eps : ℝ} {p : ℕ → ℝ} {k i j i' j' : ℕ}
    (hp : ∀ s t, s < t → t ≤ k → p s < p t) (hij : i < j) (hj : j ≤ k) (hij' : i' < j')
    (hj' : j' ≤ k) (h : certOK eps p k i j) (h' : certOK eps p k i' j') :
    ((j : ℝ) - i - 2 * eps) * (p j' - p i') = ((j' : ℝ) - i' - 2 * eps) * (p j - p i) := by
  have e := cert_slope_eq hp hij hj hij' hj' h h'
  unfold certSlope at e
  rwa [div_eq_div_iff (sub_pos.2 (hp i j hij hj)).ne' (sub_pos.2 (hp i' j' hij' hj')).ne'] at e

/-! ## Gap sequences -/

/-- Positive gaps `g 0, …, g (k-1)` make the keys `gapKeys g` strictly increasing on `[0, k]`. -/
theorem cert_gapKeys_lt {g : ℕ → ℝ} {k : ℕ} (hg : ∀ l < k, 0 < g l) :
    ∀ s t, s < t → t ≤ k → gapKeys g s < gapKeys g t := by
  intro s t hst htk
  unfold gapKeys
  rw [← Finset.sum_range_add_sum_Ico _ hst.le]
  have : 0 < ∑ l ∈ Ico s t, g l :=
    Finset.sum_pos (fun l hl => hg l (by rw [mem_Ico] at hl; omega)) (nonempty_Ico.2 hst)
  linarith

/-- **Decomposition, gap form.**  For `2ε < k` and positive gaps `g 0, …, g (k-1)`, the first
segment has more than `k` keys iff some admissible pair is a certificate of `gapKeys g`. -/
theorem cert_lt_gapSegLen_iff {eps : ℝ} {g : ℕ → ℝ} {k : ℕ} (hk : 2 * eps < k)
    (hg : ∀ l < k, 0 < g l) :
    (k : ℕ∞) < gapSegLen eps g ↔
      ∃ i j, i < j ∧ j ≤ k ∧ 2 * eps < ((j : ℝ) - i) ∧ certOK eps (gapKeys g) k i j := by
  rw [gapSegLen, lt_segLen_iff]
  exact cert_prefixAffineFeasible_iff hk (cert_gapKeys_lt hg)

/-- A certificate of `gapKeys g` (for any pair) forces `k < gapSegLen eps g`. -/
theorem cert_lt_gapSegLen_of_certOK {eps : ℝ} {g : ℕ → ℝ} {k i j : ℕ}
    (h : certOK eps (gapKeys g) k i j) : (k : ℕ∞) < gapSegLen eps g := by
  rw [gapSegLen, lt_segLen_iff]
  exact cert_feasible_of_band h

end

end PGM
