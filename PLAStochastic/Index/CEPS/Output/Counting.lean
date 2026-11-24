import PLAStochastic.Index.CEPS.Output.Grouping
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Track O: counting insertion sequences

* `card_outCount_fiber_le`: at most `j^j` sequences `c : Fin j → Fin n` have prescribed
  counts (all of them are `c₀ ∘ φ` for one fixed `c₀` and some `φ : Fin j → Fin j`).
* `outCount_eq_high_add`: `outCount c = outHigh c + 1_{outSingles c}`.
* `card_outHigh_fiber_le`: at most `n^k j^j` sequences have high part `β`, where
  `k = j - ∑ β` is the number of single insertions.
* `card_outHigh_pairs_le`: at most `n^k j^{2j}` pairs `(c, c')` with high part `β` share
  their singles.

These are the counting inputs of `output-closure.md` (O6)–(O8); the multinomial
coefficients of the source are replaced by these crude bounds, which do not depend on `n`
beyond the factor `n^k`.
-/

noncomputable section

open Finset

namespace PGM

variable {n : ℕ}

/-- At most `j^j` insertion sequences have prescribed counts. -/
theorem card_outCount_fiber_le {j : ℕ} (α : Fin n → ℕ) :
    #{c : Fin j → Fin n | outCount c = α} ≤ j ^ j := by
  classical
  set s := ({c : Fin j → Fin n | outCount c = α} : Finset (Fin j → Fin n)) with hs
  rcases s.eq_empty_or_nonempty with he | ⟨c₀, hc₀⟩
  · rw [he, Finset.card_empty]; exact Nat.zero_le _
  have hc₀' : outCount c₀ = α := by simpa [hs] using hc₀
  have hex : ∀ c ∈ s, ∀ t : Fin j, ∃ t' : Fin j, c₀ t' = c t := by
    intro c hc t
    have hc' : outCount c = α := by simpa [hs] using hc
    have hpos : 0 < outCount c₀ (c t) := by
      rw [hc₀', ← hc', outCount]
      exact Finset.card_pos.mpr ⟨t, by simp⟩
    rw [outCount] at hpos
    obtain ⟨t', ht'⟩ := Finset.card_pos.mp hpos
    exact ⟨t', by simpa using ht'⟩
  let φ : (Fin j → Fin n) → Fin j → Fin j := fun c t =>
    if h : ∃ t' : Fin j, c₀ t' = c t then h.choose else t
  have hφ : ∀ c ∈ s, ∀ t, c₀ (φ c t) = c t := by
    intro c hc t
    have h := hex c hc t
    simp only [φ, dif_pos h]
    exact h.choose_spec
  have hinj : Set.InjOn φ s := by
    intro c hc c' hc' heq
    funext t
    rw [← hφ c hc t, ← hφ c' hc' t, heq]
  calc #s ≤ #(univ : Finset (Fin j → Fin j)) :=
        Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
    _ = j ^ j := by simp

theorem outCount_eq_high_add {j : ℕ} (c : Fin j → Fin n) (l : Fin n) :
    outCount c l = outHigh c l + if l ∈ outSingles c then 1 else 0 := by
  simp only [outHigh, outSingles, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h <;> omega

theorem card_outSingles_of_high {j : ℕ} {β : Fin n → ℕ} {c : Fin j → Fin n}
    (hc : outHigh c = β) : #(outSingles c) = j - ∑ l, β l := by
  classical
  have h := sum_outCount c
  simp_rw [outCount_eq_high_add c, hc] at h
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Nat.cast_id] at h
  omega

theorem sum_high_le {j : ℕ} {β : Fin n → ℕ} {c : Fin j → Fin n} (hc : outHigh c = β) :
    ∑ l, β l ≤ j := by
  classical
  have h := sum_outCount c
  simp_rw [outCount_eq_high_add c, hc] at h
  rw [Finset.sum_add_distrib] at h
  omega

/-- At most `n^k j^j` insertion sequences have high part `β`, `k = j - ∑ β`. -/
theorem card_outHigh_fiber_le {j : ℕ} (β : Fin n → ℕ) :
    #{c : Fin j → Fin n | outHigh c = β} ≤ n ^ (j - ∑ l, β l) * j ^ j := by
  classical
  set k := j - ∑ l, β l with hk
  set s := ({c : Fin j → Fin n | outHigh c = β} : Finset (Fin j → Fin n)) with hs
  have hmaps : Set.MapsTo outSingles (s : Set (Fin j → Fin n))
      ((powersetCard k (univ : Finset (Fin n)) : Finset (Finset (Fin n))) :
        Set (Finset (Fin n))) := by
    intro c hc
    have hc' : outHigh c = β := by simpa [hs] using hc
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact card_outSingles_of_high hc'
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ S ∈ powersetCard k univ, #{c ∈ s | outSingles c = S}
      ≤ ∑ _S ∈ powersetCard k (univ : Finset (Fin n)), j ^ j := by
        refine Finset.sum_le_sum fun S _ => ?_
        refine (Finset.card_le_card ?_).trans
          (card_outCount_fiber_le (j := j) fun l => β l + if l ∈ S then 1 else 0)
        intro c hc
        simp only [Finset.mem_filter, hs, Finset.mem_univ, true_and] at hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        funext l
        rw [outCount_eq_high_add, hc.1, hc.2]
    _ = n.choose k * j ^ j := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
    _ ≤ n ^ k * j ^ j := Nat.mul_le_mul_right _ (Nat.choose_le_pow n k)

/-- Pairs with high part `β` sharing their singles. -/
theorem card_outHigh_pairs_le {j : ℕ} (β : Fin n → ℕ) :
    #{p : (Fin j → Fin n) × (Fin j → Fin n) |
        outHigh p.1 = β ∧ outHigh p.2 = β ∧ outSingles p.1 = outSingles p.2} ≤
      n ^ (j - ∑ l, β l) * j ^ j * j ^ j := by
  classical
  set s := ({c : Fin j → Fin n | outHigh c = β} : Finset (Fin j → Fin n)) with hs
  set P := ({p : (Fin j → Fin n) × (Fin j → Fin n) |
        outHigh p.1 = β ∧ outHigh p.2 = β ∧ outSingles p.1 = outSingles p.2} :
      Finset ((Fin j → Fin n) × (Fin j → Fin n))) with hP
  have hmaps : Set.MapsTo Prod.fst (P : Set ((Fin j → Fin n) × (Fin j → Fin n)))
      (s : Set (Fin j → Fin n)) := by
    intro p hp
    simp only [hP, hs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    exact hp.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ c ∈ s, #{p ∈ P | p.1 = c}
      ≤ ∑ c ∈ s, #({c' : Fin j → Fin n | outCount c' = outCount c} :
          Finset (Fin j → Fin n)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        refine Finset.card_le_card_of_injOn Prod.snd (fun p hp => ?_) (fun p hp q hq hpq => ?_)
        · simp only [hP, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hp
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
          funext l
          rw [outCount_eq_high_add, outCount_eq_high_add c, hp.1.2.1, ← hp.2, hp.1.1, hp.1.2.2]
        · simp only [hP, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hp hq
          exact Prod.ext (hp.2.trans hq.2.symm) hpq
    _ ≤ ∑ _c ∈ s, j ^ j := Finset.sum_le_sum fun c _ => card_outCount_fiber_le _
    _ = #s * j ^ j := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n ^ (j - ∑ l, β l) * j ^ j * j ^ j :=
        Nat.mul_le_mul_right _ (card_outHigh_fiber_le β)

end PGM
