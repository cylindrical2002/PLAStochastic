import PLAStochastic.Index.Model.IIDGaps

/-!
# Almost sure finiteness of the first segment from two-sided gap mass

If an iid gap sequence puts positive mass on `[0, 2]` and on `[8, ∞)`, then the first
ALG-OPT segment is almost surely finite, for every `eps` (`ae_gapSegLen_ne_top`).

With `k > 4 eps`, a window of `k` gaps in `[0, 2]` followed by `k` gaps in `[8, ∞)` is not
`eps`-feasible (`not_prefixAffineFeasible_of_block`): the three keys at the start, middle
and end of the window force a slope `a > 1/4` and `8 k a ≤ k + 2 eps`.  Disjoint windows
of length `2 k` are independent, so the probability that none of the first `J` windows is
of this kind is `(1 - q)^J → 0` with `q > 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace PGM

/-- A window of `k` gaps in `[0, 2]` followed by `k` gaps in `[8, ∞)` is not
`eps`-feasible once `4 eps < k`. -/
theorem not_prefixAffineFeasible_of_block {eps : ℝ} {k : ℕ} (hk : 0 < k)
    (hke : 4 * eps < k) {y : ℕ → ℝ} (h1 : ∀ i < k, y i ∈ Icc (0 : ℝ) 2)
    (h2 : ∀ i < k, 8 ≤ y (k + i)) :
    ¬ prefixAffineFeasible eps (gapKeys y) (2 * k + 1) := by
  rintro ⟨a, b, hab⟩
  have e0 := hab 0 (by omega)
  have e1 := hab k (by omega)
  have e2 := hab (2 * k) (by omega)
  rw [gapKeys_zero] at e0
  have hK1 : gapKeys y k ≤ 2 * k := by
    unfold gapKeys
    calc ∑ s ∈ Finset.range k, y s ≤ ∑ s ∈ Finset.range k, (2 : ℝ) :=
          Finset.sum_le_sum fun s hs => (h1 s (Finset.mem_range.1 hs)).2
      _ = 2 * k := by simp [mul_comm]
  have hK0 : 0 ≤ gapKeys y k :=
    Finset.sum_nonneg fun s hs => (h1 s (Finset.mem_range.1 hs)).1
  have hK2 : gapKeys y k + 8 * k ≤ gapKeys y (2 * k) := by
    have e : gapKeys y (2 * k) = gapKeys y k + ∑ i ∈ Finset.range k, y (k + i) := by
      unfold gapKeys
      rw [two_mul, Finset.sum_range_add]
    rw [e]
    have : (8 : ℝ) * k ≤ ∑ i ∈ Finset.range k, y (k + i) := by
      calc (8 : ℝ) * k = ∑ i ∈ Finset.range k, (8 : ℝ) := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun i hi => h2 i (Finset.mem_range.1 hi)
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [Nat.cast_zero, mul_zero, zero_add, zero_sub, abs_neg] at e0
  rw [abs_le] at e0 e1 e2
  push_cast at e2
  have ha1 : (k : ℝ) / 2 < a * gapKeys y k := by linarith [e0.1, e0.2, e1.1, e1.2]
  have hapos : 0 < a := by
    by_contra hneg
    push Not at hneg
    have : a * gapKeys y k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hK0
    linarith
  have ha4 : 1 / 4 < a := by
    by_contra hneg
    push Not at hneg
    have : a * gapKeys y k ≤ 1 / 4 * (2 * k) := mul_le_mul hneg hK1 hK0 (by norm_num)
    linarith
  have hD : a * (8 * k) ≤ a * (gapKeys y (2 * k) - gapKeys y k) :=
    mul_le_mul_of_nonneg_left (by linarith) hapos.le
  have h8 : 2 * (k : ℝ) < a * (8 * k) := by nlinarith
  have hup : a * (gapKeys y (2 * k) - gapKeys y k) ≤ k + 2 * eps := by
    linarith [e1.1, e2.2]
  linarith

/-- The window pattern: `k` coordinates in `[0, 2]` followed by `k` coordinates in `[8, ∞)`. -/
def blockBox (k : ℕ) (i : Fin (2 * k)) : Set ℝ :=
  if (i : ℕ) < k then Icc 0 2 else Ici 8

theorem measurableSet_blockBox (k : ℕ) (i : Fin (2 * k)) : MeasurableSet (blockBox k i) := by
  unfold blockBox
  split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ici

/-- A window with the pattern `blockBox` makes the first segment finite. -/
theorem gapSegLen_ne_top_of_block {eps : ℝ} {k : ℕ} (hk : 0 < k) (hke : 4 * eps < k)
    {x : ℕ → ℝ} {r : ℕ} (hx : seqPrefix (2 * k) (fun t => x (r + t)) ∈ univ.pi (blockBox k)) :
    gapSegLen eps x ≠ ⊤ := by
  intro htop
  have hall := segLen_eq_top_iff.1 htop (r + (2 * k + 1))
  have hw := prefixAffineFeasible_window hall (le_refl _)
  have hy : prefixAffineFeasible eps (gapKeys (fun t => x (r + t))) (2 * k + 1) := by
    have e : gapKeys (fun t => x (r + t)) =
        fun i => 1 * gapKeys x (r + i) + (-gapKeys x r) := by
      funext i
      rw [gapKeys_shift]
      ring
    rw [e, prefixAffineFeasible_affine_iff one_ne_zero]
    exact hw
  refine not_prefixAffineFeasible_of_block hk hke (y := fun t => x (r + t)) ?_ ?_ hy
  · intro i hi
    have := hx ⟨i, by omega⟩ (mem_univ _)
    simpa [blockBox, seqPrefix, hi] using this
  · intro i hi
    have := hx ⟨k + i, by omega⟩ (mem_univ _)
    simpa [blockBox, seqPrefix] using this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}

/-- **Almost sure finiteness of the first segment.**  If the iid gaps put positive mass on
`[0, 2]` and on `[8, ∞)`, the first ALG-OPT segment is almost surely finite. -/
theorem ae_gapSegLen_ne_top [IsProbabilityMeasure P] (h : IIDSeq P X) (eps : ℝ)
    (h1 : P {ω | X 0 ω ∈ Icc (0 : ℝ) 2} ≠ 0) (h2 : P {ω | 8 ≤ X 0 ω} ≠ 0) :
    ∀ᵐ ω ∂P, gapSegLen eps (seq X ω) ≠ ⊤ := by
  set k : ℕ := ⌈4 * eps⌉₊ + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos _
  have hke : 4 * eps < k := by
    rw [hkdef]; push_cast
    linarith [Nat.le_ceil (4 * eps)]
  set L : ℕ := 2 * k with hL
  set W : Set (Fin L → ℝ) := univ.pi (blockBox k) with hWdef
  have hW : MeasurableSet W := MeasurableSet.univ_pi (measurableSet_blockBox k)
  have hXm := h.measurable
  set D : ℕ → Set (ℕ → ℝ) := fun J =>
    {x | ∀ j < J, seqPrefix L (fun t => x (L * j + t)) ∉ W} with hDdef
  have hD : ∀ J, MeasurableSet (D J) := by
    intro J
    have e : D J = ⋂ j ∈ Finset.range J,
        (fun x : ℕ → ℝ => seqPrefix L (fun t => x (L * j + t))) ⁻¹' Wᶜ := by
      ext x
      simp [hDdef]
    rw [e]
    refine Finset.measurableSet_biInter _ fun j _ => ?_
    exact (measurable_pi_lambda _ fun i => measurable_pi_apply _) hW.compl
  set q : ℝ≥0∞ := P ((fun ω => seqPrefix L (seq X ω)) ⁻¹' W) with hq
  have hprefm : Measurable (fun ω => seqPrefix L (seq X ω)) :=
    (measurable_seqPrefix L).comp (measurable_seq hXm)
  have hqne : q ≠ 0 := by
    have hind : iIndepFun (fun i : Fin L => X i) P :=
      h.indep.precomp (g := fun i : Fin L => (i : ℕ)) Fin.val_injective
    have e : (fun ω => seqPrefix L (seq X ω)) ⁻¹' W =
        ⋂ i ∈ (Finset.univ : Finset (Fin L)), (fun i : Fin L => X i) i ⁻¹' blockBox k i := by
      ext ω
      simp [hWdef, seqPrefix, seq]
    rw [hq, e, hind.measure_inter_preimage_eq_mul _ fun i _ => measurableSet_blockBox k i]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [(h.ident i).measure_mem_eq (measurableSet_blockBox k i)]
    unfold blockBox
    split_ifs
    · exact h1
    · exact h2
  have hlaw : ∀ J, P (seq X ⁻¹' D J) = (1 - q) ^ J := by
    intro J
    induction J with
    | zero =>
      have : D 0 = univ := by ext x; simp [hDdef]
      rw [this, preimage_univ, measure_univ, pow_zero]
    | succ J ih =>
      have e : seq X ⁻¹' D (J + 1) = (fun ω (t : ℕ) => X (L + t) ω) ⁻¹' D J ∩
          (fun ω => seqPrefix L (seq X ω)) ⁻¹' Wᶜ := by
        ext ω
        simp only [hDdef, mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
        constructor
        · intro hall
          refine ⟨fun j hj => ?_, ?_⟩
          · have := hall (j + 1) (by omega)
            have e2 : seqPrefix L (fun t => seq X ω (L * (j + 1) + t)) =
                seqPrefix L (fun t => X (L + (L * j + t)) ω) := by
              funext i
              simp only [seqPrefix, seq]
              congr 1
              ring
            rwa [e2] at this
          · simpa using hall 0 (by omega)
        · rintro ⟨hJ, h0⟩ j hj
          cases j with
          | zero => simpa using h0
          | succ j =>
            have := hJ j (by omega)
            have e2 : seqPrefix L (fun t => seq X ω (L * (j + 1) + t)) =
                seqPrefix L (fun t => X (L + (L * j + t)) ω) := by
              funext i
              simp only [seqPrefix, seq]
              congr 1
              ring
            rwa [e2]
      rw [e]
      have hmB : MeasurableSet[MeasurableSpace.comap (fun ω (t : ℕ) => X (L + t) ω)
          inferInstance] ((fun ω (t : ℕ) => X (L + t) ω) ⁻¹' D J) := ⟨D J, hD J, rfl⟩
      have hmA : MeasurableSet[MeasurableSpace.comap (fun ω => seqPrefix L (seq X ω))
          inferInstance] ((fun ω => seqPrefix L (seq X ω)) ⁻¹' Wᶜ) := ⟨Wᶜ, hW.compl, rfl⟩
      rw [(Indep_iff _ _ P).mp (indep_future_prefix hXm h.indep L) _ _ hmB hmA,
        (identDistrib_future hXm h.indep h.ident L).measure_mem_eq (hD J), ih,
        preimage_compl, prob_compl_eq_one_sub (hprefm hW), pow_succ]
  have hbad : ∀ J, P {ω | gapSegLen eps (seq X ω) = ⊤} ≤ (1 - q) ^ J := by
    intro J
    rw [← hlaw J]
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω
    simp only [hDdef, mem_preimage, mem_ofPred_eq]
    intro j _ hj
    exact gapSegLen_ne_top_of_block hk hke hj hω
  have hlt : 1 - q < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hqne
  have hzero : P {ω | gapSegLen eps (seq X ω) = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hbad)
      zero_le
  rw [ae_iff]
  simpa using hzero

end PGM
