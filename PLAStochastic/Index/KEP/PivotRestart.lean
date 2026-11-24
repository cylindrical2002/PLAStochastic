import PLAStochastic.Index.KEP.PrefixStability
import PLAStochastic.Index.KEP.PivotStopping
import PLAStochastic.Index.Algorithm.EndpointTop
import PLAStochastic.Index.Algorithm.MeasurableEndpointHeight

/-!
# Restarting the endpoint hierarchy at a pivot

For a base pair sequence `z` (all counts `1`) the layer-`L` base pivots are
`layerPivot eps z L j` (`PLAStochastic.Index.KEP.PrefixStability`).

* **Shift at a pivot** (`pairLayer_shift_layerPivot`, `layerPivot_shift`,
  `layerPivot_succ_sub`).  Let `ρ = layerPivot eps z L i` and `zρ t = z (ρ + t)`.  The
  layer-`L` sequence of `zρ` is the layer-`L` sequence of `z` read from index `i`, so the
  later layer-`L` pivots of `z` are `ρ` plus the layer-`L` pivots of `zρ`; in particular
  the next layer-`L` gap is the leading layer-`L` pivot of `zρ`.  Below layer `L`, `ρ` is
  a block start, so the layers of `zρ` below `L` are restarts of the layers of `z` and
  inherit finite segments (`allSegmentsFinite_shift_layerPivot`).  From layer `L` on the
  layers of `zρ` are not restarts of those of `z`; with eventually vanishing gaps every
  restart has finite segments on all layers (`allLayersFinite_shift_of_fst_eq_zero`).
* **Height via the leading pivot** (`epHeight_le_iff_of_lt`, `epHeight_le_iff_layerPivot`).
  For `eps ≥ 1/2`, `n ≥ 1`, `L ≥ 1`: ALG-PGM on the first `n` base keys has height at most
  `L` iff the leading layer-`L` pivot is at least `n`.  Only the layers below `L` need
  finite segments, which makes the statement applicable to `zρ`
  (`le_layerPivot_sub_iff_epHeight_le`: the next layer-`L` gap is at least `n` iff ALG-PGM
  on the `n` base keys following `ρ` has height at most `L`).
* **Pivot separation** (`pow_le_layerPivot_sub`, `card_layerPivot_le`).  Consecutive
  layer-`L` pivots are at least `q ^ L` apart, `q = ⌊2 eps⌋ + 1`, so at most
  `(b - a) / q ^ L + 1` layer-`L` pivots lie in `[a, b)`.
* **Layer size** (`epLayer_snd_eq_card_layerPivot`): layer `L` of ALG-PGM on `n` base keys
  has as many keys as there are layer-`L` pivots below `n`.
-/

namespace PGM

noncomputable section

open Classical Finset

section

variable {eps : ℝ} {z : ℕ → ℝ × ℕ}

/-! ## Restarting the hierarchy at a pivot -/

/-- Restarting a pair sequence at its `k`-th block start shifts its next layer by `k`. -/
theorem layerMap_pairShift_iterate (eps : ℝ) (w : ℕ → ℝ × ℕ) (k : ℕ) :
    layerMap eps ((pairShift eps)^[k] w) = fun j => layerMap eps w (k + j) := by
  funext j
  simp only [layerMap]
  rw [← Function.iterate_add_apply, Nat.add_comm]

/-- **Shift at a pivot.**  Restarting the base sequence at the layer-`L` pivot
    `ρ = layerPivot eps z L i` restarts the layer-`L` sequence at index `i`. -/
theorem pairLayer_shift_layerPivot (hz : ∀ t, (z t).2 = 1) :
    ∀ L i, pairLayer eps L (fun t => z (layerPivot eps z L i + t)) =
      fun t => pairLayer eps L z (i + t)
  | 0, i => by rw [layerPivot_zero hz]; rfl
  | L + 1, i => by
    rw [layerPivot_succ, pairLayer_succ, pairLayer_shift_layerPivot hz L,
      ← pairShift_iterate eps (pairLayer eps L z) i, layerMap_pairShift_iterate,
      pairLayer_succ]

/-- **Shift at a pivot**, pivot form: the layer-`L` pivots of `z` from index `i` on are
    `ρ = layerPivot eps z L i` plus the layer-`L` pivots of `t ↦ z (ρ + t)`. -/
theorem layerPivot_shift (hz : ∀ t, (z t).2 = 1) (L i j : ℕ) :
    layerPivot eps z L (i + j) =
      layerPivot eps z L i + layerPivot eps (fun t => z (layerPivot eps z L i + t)) L j := by
  have h : layerPivot eps (fun t => z (layerPivot eps z L i + t)) L j =
      pairRank (fun t => pairLayer eps L z (i + t)) j := by
    rw [← pairLayer_shift_layerPivot hz L i]
    rfl
  rw [h]
  simp only [layerPivot, pairRank, sum_range_add]

/-- The next layer-`L` gap after `ρ = layerPivot eps z L i` is the leading layer-`L`
    pivot of `t ↦ z (ρ + t)`. -/
theorem layerPivot_succ_sub (hz : ∀ t, (z t).2 = 1) (L i : ℕ) :
    layerPivot eps z L (i + 1) - layerPivot eps z L i =
      layerPivot eps (fun t => z (layerPivot eps z L i + t)) L 1 := by
  rw [layerPivot_shift hz L i 1, Nat.add_sub_cancel_left]

/-- Below layer `L`, a layer-`L` pivot is a block start: the layers of the restarted
    sequence below `L` are restarts of the layers of `z` at block starts. -/
theorem pairLayer_shift_layerPivot_eq_iterate (hz : ∀ t, (z t).2 = 1) :
    ∀ L i, ∀ ℓ < L, ∃ k, pairLayer eps ℓ (fun t => z (layerPivot eps z L i + t)) =
      (pairShift eps)^[k] (pairLayer eps ℓ z)
  | 0, _, ℓ, h => absurd h (Nat.not_lt_zero ℓ)
  | L + 1, i, ℓ, h => by
    rw [layerPivot_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact pairLayer_shift_layerPivot_eq_iterate hz L _ ℓ h
    · exact ⟨i, by rw [pairLayer_shift_layerPivot hz, pairShift_iterate]⟩

/-- The layers of the sequence restarted at a layer-`L` pivot have finite segments below
    layer `L`. -/
theorem allSegmentsFinite_shift_layerPivot (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (L i : ℕ) :
    ∀ ℓ < L, AllSegmentsFinite eps (pairLayer eps ℓ (fun t => z (layerPivot eps z L i + t))) := by
  intro ℓ hℓ j
  obtain ⟨k, hk⟩ := pairLayer_shift_layerPivot_eq_iterate hz L i ℓ hℓ
  rw [hk, ← Function.iterate_add_apply]
  exact hfin ℓ (j + k)

/-- With eventually vanishing gaps, every restart has finite segments on every layer. -/
theorem allLayersFinite_shift_of_fst_eq_zero {M : ℕ} (h : ∀ t, M ≤ t → (z t).1 = 0) (ρ : ℕ) :
    AllLayersFinite eps (fun t => z (ρ + t)) :=
  allLayersFinite_of_fst_eq_zero (M := M) fun t ht => h _ (by omega)

/-! ## Pivot separation -/

/-- A finite segment has at least `q = ⌊2 eps⌋ + 1` keys. -/
theorem floor_add_one_le_toNat_pairSegLen (heps : 0 ≤ eps) {w : ℕ → ℝ × ℕ}
    (h : pairSegLen eps w ≠ ⊤) : ⌊2 * eps⌋₊ + 1 ≤ (pairSegLen eps w).toNat := by
  have h1 := floor_add_one_le_segLen heps (pairKeys w)
  change _ ≤ pairSegLen eps w at h1
  rw [← ENat.natCast_toNat h] at h1
  exact_mod_cast h1

/-- Block starts advance by at least `q = ⌊2 eps⌋ + 1` per block. -/
theorem blockStart_add_mul_le (heps : 0 ≤ eps) {w : ℕ → ℝ × ℕ} (hfin : AllSegmentsFinite eps w)
    (a : ℕ) : ∀ k, blockStart eps w a + (⌊2 * eps⌋₊ + 1) * k ≤ blockStart eps w (a + k)
  | 0 => by simp
  | k + 1 => by
    rw [← Nat.add_assoc, blockStart_succ, Nat.mul_succ]
    have h1 := floor_add_one_le_toNat_pairSegLen heps (hfin (a + k))
    have h2 := blockStart_add_mul_le heps hfin a k
    omega

/-- `k` consecutive layer-`ℓ` gaps span at least `q ^ ℓ * k` base ranks. -/
theorem layerPivot_add_pow_mul_le (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) :
    ∀ ℓ a k, layerPivot eps z ℓ a + (⌊2 * eps⌋₊ + 1) ^ ℓ * k ≤ layerPivot eps z ℓ (a + k)
  | 0, a, k => by simp [layerPivot_zero hz]
  | ℓ + 1, a, k => by
    rw [layerPivot_succ, layerPivot_succ]
    have hb := blockStart_add_mul_le heps (hfin ℓ) a k
    obtain ⟨d, hd⟩ : ∃ d, blockStart eps (pairLayer eps ℓ z) (a + k) =
        blockStart eps (pairLayer eps ℓ z) a + d := ⟨_, (Nat.add_sub_cancel' (le_trans
          (Nat.le_add_right _ _) hb)).symm⟩
    have ih := layerPivot_add_pow_mul_le heps hz hfin ℓ (blockStart eps (pairLayer eps ℓ z) a) d
    rw [hd]
    have hqd : (⌊2 * eps⌋₊ + 1) * k ≤ d := by omega
    calc layerPivot eps z ℓ (blockStart eps (pairLayer eps ℓ z) a) +
          (⌊2 * eps⌋₊ + 1) ^ (ℓ + 1) * k
        = layerPivot eps z ℓ (blockStart eps (pairLayer eps ℓ z) a) +
          (⌊2 * eps⌋₊ + 1) ^ ℓ * ((⌊2 * eps⌋₊ + 1) * k) := by rw [pow_succ, Nat.mul_assoc]
      _ ≤ layerPivot eps z ℓ (blockStart eps (pairLayer eps ℓ z) a) +
          (⌊2 * eps⌋₊ + 1) ^ ℓ * d := Nat.add_le_add_left (Nat.mul_le_mul_left _ hqd) _
      _ ≤ _ := ih

/-- **Pivot separation.**  Consecutive layer-`L` pivots are at least `q ^ L` apart,
    `q = ⌊2 eps⌋ + 1`. -/
theorem pow_le_layerPivot_sub (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (L j : ℕ) :
    (⌊2 * eps⌋₊ + 1) ^ L ≤ layerPivot eps z L (j + 1) - layerPivot eps z L j := by
  have := layerPivot_add_pow_mul_le heps hz hfin L j 1
  omega

/-- **Pivot count in a window.**  At most `(b - a) / q ^ L + 1` layer-`L` pivots lie in
    `[a, b)`, `q = ⌊2 eps⌋ + 1` (counted over any finite set `S` of layer indices; with
    `S = range b` every pivot in `[a, b)` is counted). -/
theorem card_layerPivot_le (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (L a b : ℕ) (S : Finset ℕ) :
    #{j ∈ S | a ≤ layerPivot eps z L j ∧ layerPivot eps z L j < b} ≤
      (b - a) / (⌊2 * eps⌋₊ + 1) ^ L + 1 := by
  set T := {j ∈ S | a ≤ layerPivot eps z L j ∧ layerPivot eps z L j < b} with hT
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h, card_empty]
    exact Nat.zero_le _
  set j₀ := T.min' h
  set j₁ := T.max' h
  have h₀ : a ≤ layerPivot eps z L j₀ := (mem_filter.1 (T.min'_mem h)).2.1
  have h₁ : layerPivot eps z L j₁ < b := (mem_filter.1 (T.max'_mem h)).2.2
  have hle : j₀ ≤ j₁ := T.min'_le _ (T.max'_mem h)
  have hsub : T ⊆ Icc j₀ j₁ := fun j hj => mem_Icc.2 ⟨T.min'_le j hj, T.le_max' j hj⟩
  have hsep := layerPivot_add_pow_mul_le heps hz hfin L j₀ (j₁ - j₀)
  rw [Nat.add_sub_cancel' hle] at hsep
  have hq : 0 < (⌊2 * eps⌋₊ + 1) ^ L := pow_pos (Nat.succ_pos _) L
  have hd : j₁ - j₀ ≤ (b - a) / (⌊2 * eps⌋₊ + 1) ^ L := by
    rw [Nat.le_div_iff_mul_le hq, Nat.mul_comm]
    omega
  calc #T ≤ #(Icc j₀ j₁) := card_le_card hsub
    _ = j₁ + 1 - j₀ := Nat.card_Icc _ _
    _ ≤ (b - a) / (⌊2 * eps⌋₊ + 1) ^ L + 1 := by omega

/-! ## The finite run through the layers below `L` -/

theorem pairLayer_pos_of_lt (heps : 0 ≤ eps) {L : ℕ}
    (hfin : ∀ ℓ < L, AllSegmentsFinite eps (pairLayer eps ℓ z)) (hpos : ∀ t, 1 ≤ (z t).2) :
    ∀ ℓ ≤ L, ∀ t, 1 ≤ (pairLayer eps ℓ z t).2
  | 0, _, t => hpos t
  | ℓ + 1, h, t => by
    rw [pairLayer_succ]
    exact one_le_layerMap_snd heps (hfin ℓ (by omega))
      (pairLayer_pos_of_lt heps hfin hpos ℓ (by omega)) t

/-- `epLayer_spec` through layer `L`, with finite segments required only below `L`. -/
theorem epLayer_spec_of_lt (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1) {L : ℕ}
    (hfin : ∀ ℓ < L, AllSegmentsFinite eps (pairLayer eps ℓ z)) (x0 : ℝ) (n : ℕ) :
    ∀ ℓ ≤ L, ∃ hex : ∃ j, n ≤ pairRank (pairLayer eps ℓ z) j,
      (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).2 = Nat.find hex ∧
      ∀ j < Nat.find hex,
        (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).1 j = x0 + pairKeys (pairLayer eps ℓ z) j
  | 0, _ => by
    have hrank0 : ∀ j, pairRank z j = j := pairRank_of_unit hz
    have hex : ∃ j, n ≤ pairRank (pairLayer eps 0 z) j := ⟨n, by simp [pairLayer, hrank0]⟩
    refine ⟨hex, ?_, fun j _ => rfl⟩
    show n = Nat.find hex
    have e : ∀ j, pairRank (pairLayer eps 0 z) j = j := fun j => hrank0 j
    apply le_antisymm
    · have := Nat.find_spec hex
      rw [e] at this
      exact this
    · exact Nat.find_min' hex (by rw [e])
  | ℓ + 1, hℓ => by
    have hpos : ∀ t, 1 ≤ (z t).2 := fun t => (hz t).ge
    obtain ⟨hex, hK, hq⟩ := epLayer_spec_of_lt heps hz hfin x0 n ℓ (by omega)
    have hfinℓ : AllSegmentsFinite eps (pairLayer eps ℓ z) := hfin ℓ (by omega)
    set w := pairLayer eps ℓ z with hw
    set q := (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).1 with hqdef
    set K := (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).2 with hKdef
    have hRmono : Monotone (pairRank w) := pairRank_mono w
    have hsplit : ∀ i, n ≤ pairRank w i ↔ K ≤ i := by
      intro i; rw [hK]; exact le_iff_find_le hRmono hex i
    set b := blockStart eps w with hb
    have hbmono : Monotone b := blockStart_mono eps w
    have hbge : ∀ j, j ≤ b j := le_blockStart heps hfinℓ
    have hcut : ∀ j, finCut eps q K j = min (b j) K := by
      intro j
      have h1 : finCut eps q K j = finCut eps (fun t => x0 + pairKeys w t) K j :=
        finCut_congr (fun i hi => hq i (by rw [← hK]; exact hi)) j
      have h2 := finCut_eq_min eps (fun t => x0 + pairKeys w t) K j
      rw [cut_pairKeys eps hfinℓ x0 j] at h2
      rw [h1]
      rcases le_total (b j) K with hle | hle
      · rw [min_eq_left (by exact_mod_cast hle)] at h2
        rw [min_eq_left hle]; exact_mod_cast h2
      · rw [min_eq_right (by exact_mod_cast hle)] at h2
        rw [min_eq_right hle]; exact_mod_cast h2
    have hex' : ∃ j, n ≤ pairRank (pairLayer eps (ℓ + 1) z) j :=
      exists_le_pairRank (pairLayer_pos_of_lt heps hfin hpos (ℓ + 1) hℓ) n
    have hRsucc : ∀ j, pairRank (pairLayer eps (ℓ + 1) z) j = pairRank w (b j) := by
      intro j; rw [pairLayer_succ, pairRank_layerMap]
    have hfind : ∀ j, (n ≤ pairRank (pairLayer eps (ℓ + 1) z) j ↔ K ≤ b j) := by
      intro j; rw [hRsucc, hsplit]
    refine ⟨hex', ?_, ?_⟩
    · show finSegCount eps q K = Nat.find hex'
      unfold finSegCount
      have hpred : (fun j => finCut eps q K j < K) = fun j => b j < K := by
        funext j; rw [hcut]; exact propext ⟨fun h => by omega, fun h => by omega⟩
      simp only [hpred]
      have hnot : ¬ b (K + 1) < K := by have := hbge (K + 1); omega
      rw [count_eq_find_of_downward (fun j hj => lt_of_le_of_lt (hbmono (Nat.le_succ j)) hj) hnot]
      apply le_antisymm
      · exact Nat.find_min' _ (not_lt.mpr ((hfind _).1 (Nat.find_spec hex')))
      · exact Nat.find_min' _ ((hfind _).2 (not_lt.mp (Nat.find_spec
          (⟨K + 1, hnot⟩ : ∃ j, ¬ b j < K))))
    · intro j hj
      have hbj : b j < K := by
        by_contra hc
        exact (not_le.mpr hj) (Nat.find_min' hex' ((hfind j).2 (not_lt.mp hc)))
      show q (finCut eps q K j) = _
      rw [hcut, min_eq_left hbj.le, hq _ (by rw [← hK]; exact hbj), pairLayer_succ,
        pairKeys_layerMap]

/-- Through layer `L`, a layer of the finite run has one key exactly when the leading
    pivot of that layer is at least `n`. -/
theorem epLayer_snd_eq_one_iff_of_lt (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1) {L : ℕ}
    (hfin : ∀ ℓ < L, AllSegmentsFinite eps (pairLayer eps ℓ z)) (x0 : ℝ) {n : ℕ} (hn : 1 ≤ n)
    {ℓ : ℕ} (hℓ : ℓ ≤ L) :
    (epLayer eps (fun t => x0 + pairKeys z t) n ℓ).2 = 1 ↔ n ≤ layerPivot eps z ℓ 1 := by
  obtain ⟨hex, hK, -⟩ := epLayer_spec_of_lt heps hz hfin x0 n ℓ hℓ
  rw [hK]
  have h0 : ¬ n ≤ pairRank (pairLayer eps ℓ z) 0 := by rw [pairRank_zero]; omega
  constructor
  · intro hf
    have := Nat.find_spec hex
    rwa [hf] at this
  · intro hr
    refine le_antisymm (Nat.find_min' hex hr) ?_
    by_contra hc
    have hf0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [hf0] at this
    exact h0 this

/-- The leading pivot does not decrease with the layer, through layer `L`. -/
theorem layerPivot_le_layerPivot_of_lt (heps : 0 ≤ eps) {L : ℕ}
    (hfin : ∀ ℓ < L, AllSegmentsFinite eps (pairLayer eps ℓ z)) (j ℓ : ℕ) :
    ∀ d, ℓ + d ≤ L → layerPivot eps z ℓ j ≤ layerPivot eps z (ℓ + d) j
  | 0, _ => le_rfl
  | d + 1, h => by
    refine (layerPivot_le_layerPivot_of_lt heps hfin j ℓ d (by omega)).trans ?_
    rw [← Nat.add_assoc, layerPivot_succ]
    exact layerPivot_mono eps z _ (le_blockStart heps (hfin (ℓ + d) (by omega)) j)

/-- For `eps ≥ 1/2` the finite run reaches a single key: every segment of at least two
    keys is feasible, so the layer sizes contract by `q = ⌊2 eps⌋ + 1 ≥ 2`. -/
theorem exists_epLayer_snd_eq_one (heps : 1 / 2 ≤ eps) (p : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ ℓ, 1 ≤ ℓ ∧ (epLayer eps p n ℓ).2 = 1 := by
  set q := ⌊2 * eps⌋₊ + 1 with hqdef
  have hq : 1 < q := by
    have : 1 ≤ ⌊2 * eps⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  set j := Nat.log q n + 1 with hj
  have hpow : n < q ^ j := Nat.lt_pow_succ_log_self hq _
  have h : (epLayer eps p n (0 + j)).2 ≤ (epLayer eps p n 0).2 ⌈/⌉ q ^ j :=
    epLayer_add_snd_le (by linarith) p n 0 j
  rw [Nat.zero_add] at h
  have h1 : (epLayer eps p n 0).2 ⌈/⌉ q ^ j ≤ 1 :=
    (ceilDiv_le_iff_le_mul (pow_pos (by omega) j)).2 (by rw [Nat.mul_one]; exact hpow.le)
  have h0 := one_le_epLayer_snd (eps := eps) p hn j
  exact ⟨j, by omega, by omega⟩

/-! ## Height via the leading pivot -/

/-- **Height via the leading pivot**, with finite segments required only below `L`.
    For `eps ≥ 1/2`, `n ≥ 1` and `L ≥ 1`, ALG-PGM on the first `n` base keys has height
    at most `L` iff the leading layer-`L` pivot is at least `n`. -/
theorem epHeight_le_iff_of_lt (heps : 1 / 2 ≤ eps) (hz : ∀ t, (z t).2 = 1) {L : ℕ}
    (hfin : ∀ ℓ < L, AllSegmentsFinite eps (pairLayer eps ℓ z)) (x0 : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hL : 1 ≤ L) :
    epHeight eps (fun t => x0 + pairKeys z t) n ≤ L ↔ n ≤ layerPivot eps z L 1 := by
  have heps0 : 0 ≤ eps := by linarith
  constructor
  · intro h
    have hmem := Nat.sInf_mem (exists_epLayer_snd_eq_one heps (fun t => x0 + pairKeys z t) hn)
    set H := epHeight eps (fun t => x0 + pairKeys z t) n with hH
    change 1 ≤ H ∧ (epLayer eps (fun t => x0 + pairKeys z t) n H).2 = 1 at hmem
    have hr := (epLayer_snd_eq_one_iff_of_lt heps0 hz hfin x0 hn h).1 hmem.2
    have hmono := layerPivot_le_layerPivot_of_lt heps0 hfin 1 H (L - H) (by omega)
    rw [Nat.add_sub_cancel' h] at hmono
    exact hr.trans hmono
  · intro h
    exact Nat.sInf_le ⟨hL, (epLayer_snd_eq_one_iff_of_lt heps0 hz hfin x0 hn le_rfl).2 h⟩

/-- **Height via the leading pivot.**  For `eps ≥ 1/2`, `n ≥ 1` and `L ≥ 1`, ALG-PGM on the
    first `n` base keys has height at most `L` iff the leading layer-`L` pivot is at
    least `n`. -/
theorem epHeight_le_iff_layerPivot (heps : 1 / 2 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (x0 : ℝ) {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) :
    epHeight eps (fun t => x0 + pairKeys z t) n ≤ L ↔ n ≤ layerPivot eps z L 1 :=
  epHeight_le_iff_of_lt heps hz (fun ℓ _ => hfin ℓ) x0 hn hL

/-- **The next layer-`L` gap and the restarted height.**  For `eps ≥ 1/2`, `n ≥ 1` and
    `L ≥ 1`, the gap after the layer-`L` pivot `ρ = layerPivot eps z L i` is at least `n`
    iff ALG-PGM on the `n` base keys from `ρ` on has height at most `L`. -/
theorem le_layerPivot_sub_iff_epHeight_le (heps : 1 / 2 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (x0 : ℝ) {n L : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (i : ℕ) :
    n ≤ layerPivot eps z L (i + 1) - layerPivot eps z L i ↔
      epHeight eps (fun t => x0 + pairKeys (fun t => z (layerPivot eps z L i + t)) t) n ≤ L := by
  rw [layerPivot_succ_sub hz,
    epHeight_le_iff_of_lt heps (fun t => hz _) (allSegmentsFinite_shift_layerPivot hz hfin L i)
      x0 hn hL]

/-! ## Layer size -/

/-- **Layer size.**  Layer `L` of ALG-PGM on the first `n` base keys has as many keys as
    there are layer-`L` pivots below `n`. -/
theorem epLayer_snd_eq_card_layerPivot (heps : 0 ≤ eps) (hz : ∀ t, (z t).2 = 1)
    (hfin : AllLayersFinite eps z) (x0 : ℝ) (n L : ℕ) :
    (epLayer eps (fun t => x0 + pairKeys z t) n L).2 =
      #{j ∈ range n | layerPivot eps z L j < n} := by
  obtain ⟨hex, hK, -⟩ := epLayer_spec heps hfin (fun t => (hz t).ge) (pairRank_of_unit hz) x0 n L
  rw [hK]
  have hsplit : ∀ i, n ≤ layerPivot eps z L i ↔ Nat.find hex ≤ i :=
    le_iff_find_le (pairRank_mono _) hex
  have hle : Nat.find hex ≤ n :=
    Nat.find_min' hex (le_pairRank (pairLayer_pos heps hfin (fun t => (hz t).ge) L) n)
  have hset : {j ∈ range n | layerPivot eps z L j < n} = range (Nat.find hex) := by
    ext j
    simp only [mem_filter, mem_range]
    have := hsplit j
    constructor
    · rintro ⟨-, h⟩
      by_contra hc
      exact absurd (this.2 (not_lt.mp hc)) (not_le.mpr h)
    · intro h
      exact ⟨lt_of_lt_of_le h hle, not_le.mp fun h' => absurd (this.1 h') (not_le.mpr h)⟩
  rw [hset, card_range]

end

end

end PGM
