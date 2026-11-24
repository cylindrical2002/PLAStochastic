import PLAStochastic.Index.Algorithm.MeasurableRankHeight
import PLAStochastic.Index.Algorithm.EndpointHierarchy
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of the ALG-PGM height

The layers `epLayer eps p n ℓ = (q_ℓ, K_ℓ)` of ALG-PGM are measurable functions
of the key sequence `p : ℕ → ℝ` into `(ℕ → ℝ) × ℕ` (product σ-algebra on the keys,
discrete σ-algebra on the count), by induction on `ℓ`: the keys of layer `ℓ + 1`
are `j ↦ q_ℓ (finCut eps q_ℓ K_ℓ j)`, a measurable key sequence evaluated at a
measurable `ℕ`-valued index (`measurable_comp_nat`), and the count is
`finSegCount eps q_ℓ K_ℓ` (`measurable_finSegCount_comp`).  Hence `epHeight` is
measurable, as the infimum of a set of `ℕ` with measurable membership events.

Both finite runs read only the keys `p 0, …, p (n-1)` (`epHeight_congr`,
`reHeight_congr`).  So for a finite tuple `v : Fin n → ℝ` the heights may be
evaluated on `extendKeys v` (the tuple extended by `0`), and they are measurable
functions of `v`.  No probabilistic hypothesis is used, and no condition on `eps`.
-/

namespace PGM

noncomputable section

open Classical MeasureTheory Set

/-! ## The ALG-PGM run -/

theorem measurable_epLayer (eps : ℝ) (n : ℕ) :
    ∀ ℓ, Measurable fun p : ℕ → ℝ => epLayer eps p n ℓ
  | 0 => measurable_id.prodMk measurable_const
  | ℓ + 1 => by
    have ih := measurable_epLayer eps n ℓ
    have hq : Measurable fun p : ℕ → ℝ => (epLayer eps p n ℓ).1 := measurable_fst.comp ih
    have hK : Measurable fun p : ℕ → ℝ => (epLayer eps p n ℓ).2 := measurable_snd.comp ih
    have hcut : ∀ j, Measurable fun p : ℕ → ℝ =>
        finCut eps (epLayer eps p n ℓ).1 (epLayer eps p n ℓ).2 j := fun j =>
      measurable_comp_nat (G := fun (r : ℕ → ℝ) k => finCut eps r k j)
        (fun k => measurable_finCut eps k j) hq hK
    have hkeys : Measurable fun (p : ℕ → ℝ) (j : ℕ) =>
        (epLayer eps p n ℓ).1 (finCut eps (epLayer eps p n ℓ).1 (epLayer eps p n ℓ).2 j) :=
      measurable_pi_lambda _ fun j =>
        measurable_comp_nat (G := fun (r : ℕ → ℝ) m => r m)
          (fun m => measurable_pi_apply m) hq (hcut j)
    exact hkeys.prodMk (measurable_finSegCount_comp eps hq hK)

theorem measurable_epHeight (eps : ℝ) (n : ℕ) :
    Measurable fun p : ℕ → ℝ => epHeight eps p n :=
  measurable_sInf_nat fun ℓ =>
    (MeasurableSet.const (1 ≤ ℓ)).inter
      ((measurable_snd.comp (measurable_epLayer eps n ℓ)) (measurableSet_singleton 1))

theorem measurable_epHeight_comp {Ω : Type*} [MeasurableSpace Ω] (eps : ℝ) (n : ℕ)
    {keys : Ω → ℕ → ℝ} (hkeys : Measurable keys) :
    Measurable fun ω => epHeight eps (keys ω) n :=
  (measurable_epHeight eps n).comp hkeys

/-! ## Only the first `n` keys matter -/

/-- The segments counted by `finSegCount` start inside the list. -/
theorem finCut_lt_of_lt_finSegCount {eps : ℝ} {p : ℕ → ℝ} {K j : ℕ}
    (hj : j < finSegCount eps p K) : finCut eps p K j < K := by
  by_contra hc
  have hsub : (Finset.range (K + 1)).filter (fun i => finCut eps p K i < K) ⊆
      Finset.range j := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    by_contra hij
    exact hc (lt_of_le_of_lt (finCut_mono eps p K (not_lt.mp hij)) hi.2)
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  unfold finSegCount at hj
  rw [Nat.count_eq_card_filter_range] at hj
  omega

/-- The ALG-PGM layers of two key sequences that agree on `p 0, …, p (n-1)`. -/
theorem epLayer_congr {eps : ℝ} {p p' : ℕ → ℝ} {n : ℕ} (hpp : ∀ i < n, p i = p' i) :
    ∀ ℓ, (epLayer eps p n ℓ).2 = (epLayer eps p' n ℓ).2 ∧
      ∀ j < (epLayer eps p n ℓ).2, (epLayer eps p n ℓ).1 j = (epLayer eps p' n ℓ).1 j
  | 0 => ⟨rfl, hpp⟩
  | ℓ + 1 => by
    obtain ⟨hK, hq⟩ := epLayer_congr hpp ℓ
    set q := (epLayer eps p n ℓ).1 with hqdef
    set K := (epLayer eps p n ℓ).2 with hKdef
    set q' := (epLayer eps p' n ℓ).1 with hq'def
    have hqq : ∀ i < K, q i = q' i := hq
    have hK' : (epLayer eps p' n ℓ).2 = K := hK.symm
    have hcnt : finSegCount eps q K = finSegCount eps q' K := finSegCount_congr hqq
    refine ⟨?_, fun j hj => ?_⟩
    · show finSegCount eps q K = finSegCount eps q' (epLayer eps p' n ℓ).2
      rw [hK', hcnt]
    · show q (finCut eps q K j) = q' (finCut eps q' (epLayer eps p' n ℓ).2 j)
      rw [hK', ← finCut_congr hqq j]
      exact hqq _ (finCut_lt_of_lt_finSegCount hj)

/-- The ALG-PGM height reads only the keys `p 0, …, p (n-1)`. -/
theorem epHeight_congr {eps : ℝ} {p p' : ℕ → ℝ} {n : ℕ} (hpp : ∀ i < n, p i = p' i) :
    epHeight eps p n = epHeight eps p' n := by
  unfold epHeight
  simp only [fun ℓ => (epLayer_congr (eps := eps) hpp ℓ).1]

/-- The ALG-RE layer `ℓ` reads only lattice keys of rank below `n`. -/
theorem mul_reDelta_lt_of_lt_reSize {eps : ℝ} {p : ℕ → ℝ} {n : ℕ} :
    ∀ ℓ j, j < (reLayer eps p n ℓ).2 → j * (reLayer eps p n ℓ).1 < n
  | 0, j, hj => by simpa [reLayer] using hj
  | ℓ + 1, j, hj => by
    set d := (reLayer eps p n ℓ).2 /
      finSegCount eps (fun i => p (i * (reLayer eps p n ℓ).1)) (reLayer eps p n ℓ).2 with hd
    have hj' : j < (reLayer eps p n ℓ).2 ⌈/⌉ d := hj
    show j * (d * (reLayer eps p n ℓ).1) < n
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0] at hj'
      simp at hj'
    · have := mul_reDelta_lt_of_lt_reSize ℓ (j * d) ((lt_ceilDiv_iff_mul_lt hpos).1 hj')
      rwa [← Nat.mul_assoc]

/-- The ALG-RE layers of two key sequences that agree on `p 0, …, p (n-1)`. -/
theorem reLayer_congr {eps : ℝ} {p p' : ℕ → ℝ} {n : ℕ} (hpp : ∀ i < n, p i = p' i) :
    ∀ ℓ, reLayer eps p n ℓ = reLayer eps p' n ℓ
  | 0 => rfl
  | ℓ + 1 => by
    have ih := reLayer_congr (eps := eps) hpp ℓ
    have hcnt : finSegCount eps (fun j => p (j * (reLayer eps p n ℓ).1)) (reLayer eps p n ℓ).2 =
        finSegCount eps (fun j => p' (j * (reLayer eps p n ℓ).1)) (reLayer eps p n ℓ).2 :=
      finSegCount_congr fun i hi => hpp _ (mul_reDelta_lt_of_lt_reSize ℓ i hi)
    show ((reLayer eps p n ℓ).2 / finSegCount eps (fun j => p (j * (reLayer eps p n ℓ).1))
        (reLayer eps p n ℓ).2 * (reLayer eps p n ℓ).1, _) =
      ((reLayer eps p' n ℓ).2 / finSegCount eps (fun j => p' (j * (reLayer eps p' n ℓ).1))
        (reLayer eps p' n ℓ).2 * (reLayer eps p' n ℓ).1, _)
    rw [← ih, hcnt]

/-- The ALG-RE height reads only the keys `p 0, …, p (n-1)`. -/
theorem reHeight_congr {eps : ℝ} {p p' : ℕ → ℝ} {n : ℕ} (hpp : ∀ i < n, p i = p' i) :
    reHeight eps p n = reHeight eps p' n := by
  unfold reHeight
  simp only [reLayer_congr (eps := eps) hpp]

/-! ## Finite key tuples -/

/-- A finite key tuple extended to a sequence by the junk value `0`. -/
def extendKeys {n : ℕ} (v : Fin n → ℝ) : ℕ → ℝ := fun i => if h : i < n then v ⟨i, h⟩ else 0

theorem extendKeys_of_lt {n : ℕ} (v : Fin n → ℝ) {i : ℕ} (h : i < n) :
    extendKeys v i = v ⟨i, h⟩ := dif_pos h

theorem measurable_extendKeys {n : ℕ} : Measurable (extendKeys (n := n)) :=
  measurable_pi_lambda _ fun i => by
    by_cases h : i < n
    · simp only [extendKeys, h, dif_pos]
      exact measurable_pi_apply _
    · simp only [extendKeys, h, dif_neg, not_false_eq_true]
      exact measurable_const

/-- The ALG-PGM height of a sequence is that of its first `n` keys, extended by `0`. -/
theorem epHeight_eq_extendKeys {eps : ℝ} {n : ℕ} {p : ℕ → ℝ} {v : Fin n → ℝ}
    (hv : ∀ i : Fin n, p i = v i) : epHeight eps p n = epHeight eps (extendKeys v) n :=
  epHeight_congr fun i hi => by rw [extendKeys_of_lt v hi, ← hv ⟨i, hi⟩]

/-- The ALG-RE height of a sequence is that of its first `n` keys, extended by `0`. -/
theorem reHeight_eq_extendKeys {eps : ℝ} {n : ℕ} {p : ℕ → ℝ} {v : Fin n → ℝ}
    (hv : ∀ i : Fin n, p i = v i) : reHeight eps p n = reHeight eps (extendKeys v) n :=
  reHeight_congr fun i hi => by rw [extendKeys_of_lt v hi, ← hv ⟨i, hi⟩]

theorem measurable_epHeight_extendKeys (eps : ℝ) (n : ℕ) :
    Measurable fun v : Fin n → ℝ => epHeight eps (extendKeys v) n :=
  (measurable_epHeight eps n).comp measurable_extendKeys

theorem measurable_reHeight_extendKeys (eps : ℝ) (n : ℕ) :
    Measurable fun v : Fin n → ℝ => reHeight eps (extendKeys v) n :=
  (measurable_reHeight eps n).comp measurable_extendKeys

end

end PGM
