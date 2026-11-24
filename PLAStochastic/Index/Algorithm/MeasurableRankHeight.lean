import PLAStochastic.Index.Algorithm.RankHierarchy
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of the ALG-RE height

The height `reHeight eps p n` is a measurable function of the key sequence
`p : ℕ → ℝ` (product σ-algebra), for every `eps` and `n`.  The chain is:
the feasibility events of the shifted sequence are measurable
(`measurableSet_prefixAffineFeasible`), so `finSegLen` is measurable
(a `Nat.findGreatest` of measurable events), `finCut` by induction on the
segment index, `finSegCount` as a count of measurable events, and each layer
`reLayer eps p n ℓ = (Δ_ℓ, N_ℓ)` by induction on `ℓ`.  The only non-routine
point is that layer `ℓ + 1` evaluates `finSegCount` on the keys
`j ↦ p (j * Δ_ℓ)` with the random spacing `Δ_ℓ` and random length `N_ℓ`;
a measurable `ℕ`-valued index can be substituted into any family that is
measurable for each fixed index (`measurable_comp_nat`).  Finally `reHeight`
is the infimum of a set of `ℕ` whose membership events are measurable.
No probabilistic hypothesis is used; `eps ≥ 1` is not needed.
-/

namespace PGM

noncomputable section

open Classical MeasureTheory Set

/-! ## Generic tools for `ℕ`-valued maps -/

/-- Substituting a measurable `ℕ`-valued index into a family that is measurable
    for each fixed index. -/
theorem measurable_comp_nat {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {G : β → ℕ → γ} (hG : ∀ k, Measurable fun b => G b k)
    {q : α → β} {K : α → ℕ} (hq : Measurable q) (hK : Measurable K) :
    Measurable fun x => G (q x) (K x) :=
  (measurable_from_prod_countable_left (f := fun z : β × ℕ => G z.1 z.2) hG).comp
    (hq.prodMk hK)

/-- `Nat.count` of measurable events is measurable. -/
theorem measurable_count {α : Type*} [MeasurableSpace α] {P : α → ℕ → Prop}
    [∀ x, DecidablePred (P x)] (hP : ∀ j, MeasurableSet {x | P x j}) :
    ∀ n, Measurable fun x => Nat.count (P x) n
  | 0 => by simp only [Nat.count_zero]; exact measurable_const
  | n + 1 => by
    simp only [Nat.count_succ]
    exact (measurable_comp_nat (G := fun (m : ℕ) (e : ℕ) => m + e)
      (fun _ => measurable_of_countable _) (measurable_count hP n)
      (Measurable.ite (hP n) measurable_const measurable_const))

/-- The infimum of a random subset of `ℕ` with measurable membership events is measurable. -/
theorem measurable_sInf_nat {α : Type*} [MeasurableSpace α] {S : α → Set ℕ}
    (hS : ∀ ℓ, MeasurableSet {x | ℓ ∈ S x}) : Measurable fun x => sInf (S x) := by
  refine measurable_to_countable' fun v => ?_
  have hset : (fun x => sInf (S x)) ⁻¹' {v} =
      ({x | v ∈ S x} ∩ ⋂ ℓ ∈ Finset.range v, {x | ℓ ∈ S x}ᶜ) ∪
        ({_x | v = 0} ∩ ⋂ ℓ, {x | ℓ ∈ S x}ᶜ) := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
      mem_iInter, mem_compl_iff, Finset.mem_range]
    constructor
    · intro h
      rcases (S x).eq_empty_or_nonempty with he | hne
      · right
        rw [he, Nat.sInf_empty] at h
        exact ⟨h.symm, fun ℓ => by simp [he]⟩
      · left
        subst h
        exact ⟨Nat.sInf_mem hne, fun ℓ hℓ => Nat.notMem_of_lt_sInf hℓ⟩
    · rintro (⟨hv, hlt⟩ | ⟨hv, hall⟩)
      · refine le_antisymm (Nat.sInf_le hv) (not_lt.mp fun h => ?_)
        exact hlt _ h (Nat.sInf_mem ⟨v, hv⟩)
      · have he : S x = ∅ := Set.eq_empty_iff_forall_notMem.2 hall
        rw [he, Nat.sInf_empty, hv]
  rw [hset]
  exact ((hS v).inter (MeasurableSet.biInter (Finset.range v).countable_toSet
    fun ℓ _ => (hS ℓ).compl)).union
    ((MeasurableSet.const _).inter (MeasurableSet.iInter fun ℓ => (hS ℓ).compl))

/-! ## The finite ALG-OPT run -/

theorem measurable_shiftSeq (a : ℕ) : Measurable fun p : ℕ → ℝ => shiftSeq p a :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (a + i)

theorem measurable_finSegLen (eps : ℝ) (K a : ℕ) :
    Measurable fun p : ℕ → ℝ => finSegLen eps p K a :=
  measurable_findGreatest fun len _ =>
    measurable_shiftSeq a (measurableSet_prefixAffineFeasible eps len)

theorem measurable_finCut (eps : ℝ) (K : ℕ) :
    ∀ j, Measurable fun p : ℕ → ℝ => finCut eps p K j
  | 0 => measurable_const
  | j + 1 =>
    measurable_comp_nat (G := fun (p : ℕ → ℝ) a => a + finSegLen eps p K a)
      (fun a => (measurable_of_countable (fun m : ℕ => a + m)).comp
        (measurable_finSegLen eps K a))
      measurable_id (measurable_finCut eps K j)

theorem measurable_finSegCount (eps : ℝ) (K : ℕ) :
    Measurable fun p : ℕ → ℝ => finSegCount eps p K :=
  measurable_count (P := fun p j => finCut eps p K j < K)
    (fun j => measurable_finCut eps K j (MeasurableSet.of_discrete (s := {m : ℕ | m < K})))
    (K + 1)

/-- The segment count of measurable keys over a measurable list length is measurable. -/
theorem measurable_finSegCount_comp {α : Type*} [MeasurableSpace α] (eps : ℝ)
    {q : α → ℕ → ℝ} {K : α → ℕ} (hq : Measurable q) (hK : Measurable K) :
    Measurable fun x => finSegCount eps (q x) (K x) :=
  measurable_comp_nat (G := fun p k => finSegCount eps p k) (measurable_finSegCount eps) hq hK

/-! ## The ALG-RE run -/

theorem measurable_reLayer (eps : ℝ) (n : ℕ) :
    ∀ ℓ, Measurable fun p : ℕ → ℝ => reLayer eps p n ℓ
  | 0 => measurable_const
  | ℓ + 1 => by
    have ih := measurable_reLayer eps n ℓ
    have hΔ : Measurable fun p : ℕ → ℝ => (reLayer eps p n ℓ).1 := measurable_fst.comp ih
    have hN : Measurable fun p : ℕ → ℝ => (reLayer eps p n ℓ).2 := measurable_snd.comp ih
    have hkeys : Measurable fun (p : ℕ → ℝ) (j : ℕ) => p (j * (reLayer eps p n ℓ).1) :=
      measurable_pi_lambda _ fun j =>
        measurable_comp_nat (G := fun (p : ℕ → ℝ) d => p (j * d))
          (fun d => measurable_pi_apply (j * d)) measurable_id hΔ
    have hM := measurable_finSegCount_comp eps hkeys hN
    have hF := (measurable_of_countable
      (fun t : ℕ × ℕ × ℕ => (t.2.1 / t.2.2 * t.1, t.2.1 ⌈/⌉ (t.2.1 / t.2.2)))).comp
      (hΔ.prodMk (hN.prodMk hM))
    exact hF

theorem measurable_reHeight (eps : ℝ) (n : ℕ) :
    Measurable fun p : ℕ → ℝ => reHeight eps p n :=
  measurable_sInf_nat fun ℓ =>
    (MeasurableSet.const (1 ≤ ℓ)).inter
      ((measurable_snd.comp (measurable_reLayer eps n ℓ)) (measurableSet_singleton 1))

/-! ## Random keys -/

theorem measurable_reHeight_comp {Ω : Type*} [MeasurableSpace Ω] (eps : ℝ) (n : ℕ)
    {keys : Ω → ℕ → ℝ} (hkeys : Measurable keys) :
    Measurable fun ω => reHeight eps (keys ω) n :=
  (measurable_reHeight eps n).comp hkeys

/-- The partial-sum keys `t ↦ x0 + ∑_{s < t} g s` of measurable gaps are measurable. -/
theorem measurable_partialSumKeys {Ω : Type*} [MeasurableSpace Ω] {x0 : Ω → ℝ}
    {g : ℕ → Ω → ℝ} (hx0 : Measurable x0) (hg : ∀ s, Measurable (g s)) :
    Measurable fun ω (t : ℕ) => x0 ω + ∑ s ∈ Finset.range t, g s ω :=
  measurable_pi_lambda _ fun _ => hx0.add (Finset.measurable_sum _ fun s _ => hg s)

theorem measurable_reHeight_partialSum {Ω : Type*} [MeasurableSpace Ω] (eps : ℝ) (n : ℕ)
    {x0 : Ω → ℝ} {g : ℕ → Ω → ℝ} (hx0 : Measurable x0) (hg : ∀ s, Measurable (g s)) :
    Measurable fun ω => reHeight eps (fun t => x0 ω + ∑ s ∈ Finset.range t, g s ω) n :=
  measurable_reHeight_comp eps n (measurable_partialSumKeys hx0 hg)

end

end PGM
