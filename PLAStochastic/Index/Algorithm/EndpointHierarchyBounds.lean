import PLAStochastic.Index.Algorithm.EndpointHierarchy

/-!
# Deterministic bounds for the endpoint hierarchy

With `eps ≥ 1` every ALG-OPT segment has at least three keys.  Hence the number
of layer-`ℓ` pivots below input rank `n` drops by a factor three from one layer to
the next, the height is at most `ℓ + K_ℓ - 1`, and the leading hyper-segment grows
with the layer.  Everything here is pathwise, on the event that all segments of
all layers are finite.
-/

namespace PGM

noncomputable section

open Classical Finset

variable {eps : ℝ} {z : ℕ → ℝ × ℕ}

theorem three_le_segLen (heps : 1 ≤ eps) (p : ℕ → ℝ) : (3 : ℕ∞) ≤ segLen eps p := by
  have C := ConstantLineLengthCertificate.of_nonneg (show 0 ≤ eps by linarith)
  have h3 : 3 ≤ C.q := C.q_ge_three heps
  exact le_trans (by exact_mod_cast h3) (constantLine_le_segLen C p)

theorem three_mul_le_blockStart (heps : 1 ≤ eps) (hfin : AllSegmentsFinite eps z) :
    ∀ j, 3 * j ≤ blockStart eps z j
  | 0 => by simp [blockStart]
  | j + 1 => by
    rw [blockStart_succ]
    have h3 := three_le_segLen heps (pairKeys ((pairShift eps)^[j] z))
    have h3' : 3 ≤ (pairSegLen eps ((pairShift eps)^[j] z)).toNat := by
      change (3 : ℕ∞) ≤ pairSegLen eps _ at h3
      have := hfin j
      rw [← ENat.natCast_toNat this] at h3
      exact_mod_cast h3
    have := three_mul_le_blockStart heps hfin j
    omega

/-- Number of layer-`ℓ` pivots whose input rank is below `n`. -/
def layerCount (eps : ℝ) (z : ℕ → ℝ × ℕ) (n ℓ : ℕ) : ℕ :=
  sInf {j | n ≤ pairRank (pairLayer eps ℓ z) j}

/-- The leading hyper-segment of layer `ℓ` (number of input gaps it spans). -/
def leadSpan (eps : ℝ) (z : ℕ → ℝ × ℕ) (ℓ : ℕ) : ℕ := (pairLayer eps ℓ z 0).2

theorem layerCount_spec (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) (n ℓ : ℕ) (i : ℕ) :
    n ≤ pairRank (pairLayer eps ℓ z) i ↔ layerCount eps z n ℓ ≤ i := by
  have hex : {j | n ≤ pairRank (pairLayer eps ℓ z) j}.Nonempty := exists_le_pairRank (hpos ℓ) n
  unfold layerCount
  constructor
  · intro h; exact Nat.sInf_le h
  · intro h; exact (Nat.sInf_mem hex).trans (pairRank_mono _ h)

theorem layerCount_pos (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) {n : ℕ} (hn : 1 ≤ n)
    (ℓ : ℕ) : 1 ≤ layerCount eps z n ℓ := by
  by_contra h
  have h0 : layerCount eps z n ℓ ≤ 0 := by omega
  have := (layerCount_spec hpos n ℓ 0).2 h0
  rw [pairRank_zero] at this
  omega

theorem layerCount_eq_one_iff (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) {n : ℕ} (hn : 1 ≤ n)
    (ℓ : ℕ) : layerCount eps z n ℓ = 1 ↔ n ≤ leadSpan eps z ℓ := by
  have h1 := layerCount_pos hpos hn ℓ
  have hs := layerCount_spec hpos n ℓ 1
  rw [pairRank_one] at hs
  unfold leadSpan
  constructor
  · intro h; exact hs.2 h.le
  · intro h; have := hs.1 h; omega

/-- The count drops by a factor three from one layer to the next. -/
theorem layerCount_succ_le (heps : 1 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) (n ℓ : ℕ) :
    3 * layerCount eps z n (ℓ + 1) ≤ layerCount eps z n ℓ + 2 := by
  set K := layerCount eps z n ℓ
  set j₀ := (K + 2) / 3
  have hb : K ≤ blockStart eps (pairLayer eps ℓ z) j₀ :=
    le_trans (by omega) (three_mul_le_blockStart heps (hfin ℓ) j₀)
  have hle : layerCount eps z n (ℓ + 1) ≤ j₀ := by
    apply (layerCount_spec hpos n (ℓ + 1) j₀).1
    rw [pairLayer_succ, pairRank_layerMap]
    exact (layerCount_spec hpos n ℓ _).2 hb
  omega

/-- The leading hyper-segment grows with the layer. -/
theorem leadSpan_le_succ (heps : 0 ≤ eps) (hfin : AllLayersFinite eps z) (ℓ : ℕ) :
    leadSpan eps z ℓ ≤ leadSpan eps z (ℓ + 1) := by
  unfold leadSpan
  rw [← pairRank_one, ← pairRank_one, pairLayer_succ, pairRank_layerMap]
  apply pairRank_mono
  have := le_blockStart heps (hfin ℓ) 1
  exact this

theorem leadSpan_mono (heps : 0 ≤ eps) (hfin : AllLayersFinite eps z) :
    Monotone (leadSpan eps z) :=
  monotone_nat_of_le_succ (leadSpan_le_succ heps hfin)

/-- The infinite-hierarchy height: first layer `ℓ ≥ 1` whose leading hyper-segment
    spans `n` input gaps. -/
def spanHeight (eps : ℝ) (z : ℕ → ℝ × ℕ) (n : ℕ) : ℕ :=
  sInf {ℓ | 1 ≤ ℓ ∧ n ≤ leadSpan eps z ℓ}

theorem spanHeight_le {n ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (h : n ≤ leadSpan eps z ℓ) : spanHeight eps z n ≤ ℓ :=
  Nat.sInf_le ⟨hℓ, h⟩

/-- `H > ℓ` exactly when the layer-`ℓ` leading hyper-segment is short (`ℓ ≥ 1`). -/
theorem lt_spanHeight_iff (heps : 0 ≤ eps) (hfin : AllLayersFinite eps z) {n ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hex : ∃ ℓ', 1 ≤ ℓ' ∧ n ≤ leadSpan eps z ℓ') :
    ℓ < spanHeight eps z n ↔ leadSpan eps z ℓ < n := by
  constructor
  · intro h
    by_contra hc
    exact absurd (spanHeight_le hℓ (not_lt.mp hc)) (not_le.mpr h)
  · intro h
    by_contra hc
    have hle : spanHeight eps z n ≤ ℓ := not_lt.mp hc
    have hmem : spanHeight eps z n ∈ {ℓ | 1 ≤ ℓ ∧ n ≤ leadSpan eps z ℓ} := Nat.sInf_mem hex
    have := leadSpan_mono heps hfin hle
    exact absurd (hmem.2.trans this) (not_le.mpr h)

/-- **Height bound by the layer count**: `H ≤ ℓ + K_ℓ - 1` for every `ℓ ≥ 1`. -/
theorem spanHeight_le_add_layerCount (heps : 1 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) {n : ℕ} (hn : 1 ≤ n) :
    ∀ d ℓ, 1 ≤ ℓ → layerCount eps z n ℓ ≤ d + 1 → spanHeight eps z n ≤ ℓ + d := by
  intro d
  induction d with
  | zero =>
    intro ℓ hℓ hK
    have h1 := layerCount_pos hpos hn ℓ
    have hK1 : layerCount eps z n ℓ = 1 := by omega
    exact le_trans (spanHeight_le hℓ ((layerCount_eq_one_iff hpos hn ℓ).1 hK1)) (by omega)
  | succ d ih =>
    intro ℓ hℓ hK
    by_cases h1 : layerCount eps z n ℓ = 1
    · exact le_trans (spanHeight_le hℓ ((layerCount_eq_one_iff hpos hn ℓ).1 h1)) (by omega)
    · have h2 := layerCount_pos hpos hn ℓ
      have hs := layerCount_succ_le heps hfin hpos n ℓ
      have : layerCount eps z n (ℓ + 1) ≤ d + 1 := by omega
      have := ih (ℓ + 1) (by omega) this
      omega

/-- The finite ALG-PGM height equals `spanHeight` on the all-finite event. -/
theorem epHeight_eq_spanHeight (heps : 0 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ t, 1 ≤ (z t).2) (hrank0 : ∀ j, pairRank z j = j) (x0 : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    epHeight eps (fun t => x0 + pairKeys z t) n = spanHeight eps z n :=
  epHeight_eq heps hfin hpos hrank0 x0 hn

/-- On the all-finite event some layer `ℓ ≥ 1` has a leading hyper-segment spanning `n`. -/
theorem exists_leadSpan_ge (heps : 1 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) {n : ℕ} (hn : 1 ≤ n) :
    ∃ ℓ, 1 ≤ ℓ ∧ n ≤ leadSpan eps z ℓ := by
  have key : ∀ d ℓ, 1 ≤ ℓ → layerCount eps z n ℓ ≤ d + 1 →
      ∃ ℓ', 1 ≤ ℓ' ∧ n ≤ leadSpan eps z ℓ' := by
    intro d
    induction d with
    | zero =>
      intro ℓ hℓ hK
      have h1 := layerCount_pos hpos hn ℓ
      exact ⟨ℓ, hℓ, (layerCount_eq_one_iff hpos hn ℓ).1 (by omega)⟩
    | succ d ih =>
      intro ℓ hℓ hK
      by_cases h1 : layerCount eps z n ℓ = 1
      · exact ⟨ℓ, hℓ, (layerCount_eq_one_iff hpos hn ℓ).1 h1⟩
      · have h2 := layerCount_pos hpos hn ℓ
        have hs := layerCount_succ_le heps hfin hpos n ℓ
        exact ih (ℓ + 1) (by omega) (by omega)
  exact key (layerCount eps z n 1) 1 le_rfl (by omega)

theorem one_le_spanHeight (heps : 1 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ spanHeight eps z n :=
  (Nat.sInf_mem (exists_leadSpan_ge heps hfin hpos hn)).1

theorem spanHeight_le_n (heps : 1 ≤ eps) (hfin : AllLayersFinite eps z)
    (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) {n : ℕ} (hn : 1 ≤ n)
    (hK1 : layerCount eps z n 1 ≤ n) : spanHeight eps z n ≤ n := by
  have := spanHeight_le_add_layerCount heps hfin hpos hn (n - 1) 1 le_rfl (by omega)
  omega

theorem layerCount_le (hpos : ∀ ℓ t, 1 ≤ (pairLayer eps ℓ z t).2) (n ℓ : ℕ) :
    layerCount eps z n ℓ ≤ n :=
  (layerCount_spec hpos n ℓ n).1 (le_pairRank (hpos ℓ) n)

end

end PGM
