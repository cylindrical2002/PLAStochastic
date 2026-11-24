import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Regeneration of an iid sequence at an almost surely finite stopping rule

Let `Z : ℕ → Ω → E` be iid with values in a measurable space `E`, and write
`seq Z ω = (Z 0 ω, Z 1 ω, …)` for its path in sequence space `ℕ → E`.

A *stopping rule* is a map `τ : (ℕ → E) → ℕ∞` on sequence space such that, for every
`t : ℕ`, the event `{z | t < τ z}` is measurable with respect to the first `t`
coordinates `z 0, …, z (t - 1)`, i.e. with respect to the σ-algebra pulled back by
`seqPrefix t : (ℕ → E) → (Fin t → E)`.  Thus whether coordinate `t` belongs to the
stopped block is decided by the strictly earlier coordinates.  The stopped block is
`z 0, …, z (τ z - 1)`, and `shiftBy τ z = (z (τ z), z (τ z + 1), …)` is the restarted
sequence (with the junk shift by `0` when `τ z = ⊤`).

Main results, for an almost surely finite stopping rule:
* `measurable_shiftBy`: the restart map is measurable;
* `identDistrib_shiftBy`: the restarted sequence has the law of the original sequence;
* `indepFun_block_shiftBy`: any measurable functional `D` of the stopped block
  (`τ z` together with `z 0, …, z (τ z - 1)`) is independent of the restarted sequence;
* `iIndepFun_rewards`, `identDistrib_rewards`: with `R := shiftBy τ`, the rewards
  `D (R^[j] (seq Z ·))` are iid;
* `ae_iterate_ne_top`: every iterated stopping rule is almost surely finite.

The proofs decompose events by the value of the stopping rule, use independence of
the fixed prefix and the fixed future at each deterministic time, and sum.

This file adapts the real-valued, natural-filtration proofs of the Swing project
(`SwingRepair/StoppedIID.lean`, `SwingRepair/StoppedIIDAe.lean`,
`SwingRepair/StoppedIIDProcess.lean`, `SwingRepair/RegenerativeMap.lean` in
`swing-filter/theory/lean`) to a general state space and to stopping rules stated
on sequence space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PGM

variable {E : Type*} [MeasurableSpace E]

/-! ## Sequence space, prefixes and stopping rules -/

/-- The first `t` coordinates `z 0, …, z (t - 1)` of a sequence. -/
def seqPrefix (t : ℕ) (z : ℕ → E) : Fin t → E := fun i => z i

/-- A stopping rule on sequence space: for every `t`, the event `{t < τ}` is measurable
with respect to the first `t` coordinates. -/
def IsStoppingRule (τ : (ℕ → E) → ℕ∞) : Prop :=
  ∀ t : ℕ, MeasurableSet[MeasurableSpace.comap (seqPrefix t) inferInstance]
    {z | (t : ℕ∞) < τ z}

/-- The path of a process, as a point of sequence space. -/
def seq {Ω : Type*} (Z : ℕ → Ω → E) (ω : Ω) : ℕ → E := fun t => Z t ω

/-- The sequence restarted at the stopping rule (shift by `0` when `τ z = ⊤`). -/
def shiftBy (τ : (ℕ → E) → ℕ∞) (z : ℕ → E) : ℕ → E := fun t => z ((τ z).toNat + t)

theorem measurable_seqPrefix (t : ℕ) : Measurable (seqPrefix (E := E) t) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)

/-- Membership in a prefix-measurable set depends only on the prefix. -/
theorem mem_iff_of_measurableSet_comap_seqPrefix {t : ℕ} {s : Set (ℕ → E)}
    (hs : MeasurableSet[MeasurableSpace.comap (seqPrefix t) inferInstance] s)
    {z z' : ℕ → E} (h : ∀ i < t, z i = z' i) : z ∈ s ↔ z' ∈ s := by
  obtain ⟨S, -, rfl⟩ := hs
  have hzz : seqPrefix t z = seqPrefix t z' := funext fun i => h i i.isLt
  simp only [Set.mem_preimage, hzz]

/-- A measurable set whose membership depends only on the first `t` coordinates is
measurable with respect to those coordinates. -/
theorem measurableSet_comap_seqPrefix_of_agree {t : ℕ} {s : Set (ℕ → E)}
    (hs : MeasurableSet s) (h : ∀ z z', (∀ i < t, z i = z' i) → z ∈ s → z' ∈ s) :
    MeasurableSet[MeasurableSpace.comap (seqPrefix t) inferInstance] s := by
  rcases isEmpty_or_nonempty E with hE | ⟨⟨e⟩⟩
  · have hs0 : s = ∅ := by
      ext z
      exact isEmptyElim (z 0)
    rw [hs0]
    exact MeasurableSpace.measurableSet_empty _
  · let ext : (Fin t → E) → ℕ → E := fun v k => if hk : k < t then v ⟨k, hk⟩ else e
    have hext : Measurable ext := by
      refine measurable_pi_lambda _ fun k => ?_
      by_cases hk : k < t
      · simp only [ext, hk, dif_pos]
        exact measurable_pi_apply _
      · simp only [ext, hk, dif_neg, not_false_eq_true]
        exact measurable_const
    refine ⟨ext ⁻¹' s, hext hs, ?_⟩
    ext z
    simp only [Set.mem_preimage]
    have hagree : ∀ i < t, ext (seqPrefix t z) i = z i := by
      intro i hi
      simp [ext, hi, seqPrefix]
    exact ⟨fun hz => h _ _ hagree hz, fun hz => h _ _ (fun i hi => (hagree i hi).symm) hz⟩

omit [MeasurableSpace E] in
/-- A finite value of `ℕ∞` is characterized by the order events `{s < x}`, `s ≤ t`. -/
theorem enat_eq_coe_iff (x : ℕ∞) (t : ℕ) :
    x = t ↔ (∀ s : ℕ, s < t → (s : ℕ∞) < x) ∧ ¬ (t : ℕ∞) < x := by
  induction x with
  | top => simp
  | coe m =>
    simp only [Nat.cast_inj, Nat.cast_lt, not_lt]
    constructor
    · rintro rfl
      exact ⟨fun s hs => hs, le_rfl⟩
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge m t with hlt | hge
      · exact absurd (h1 m hlt) (lt_irrefl m)
      · omega

variable {τ : (ℕ → E) → ℕ∞}

theorem IsStoppingRule.measurableSet_lt (hτ : IsStoppingRule τ) (t : ℕ) :
    MeasurableSet {z | (t : ℕ∞) < τ z} :=
  (measurable_seqPrefix t).comap_le _ (hτ t)

/-- A stopping rule is measurable. -/
theorem IsStoppingRule.measurable (hτ : IsStoppingRule τ) : Measurable τ := by
  refine measurable_to_countable' fun x => ?_
  induction x with
  | top =>
    have heq : τ ⁻¹' {⊤} = ⋂ t : ℕ, {z | (t : ℕ∞) < τ z} := by
      ext z
      simp [ENat.eq_top_iff_forall_gt]
    rw [heq]
    exact MeasurableSet.iInter fun t => hτ.measurableSet_lt t
  | coe t =>
    have heq : τ ⁻¹' {(t : ℕ∞)} =
        (⋂ s ∈ Finset.range t, {z | (s : ℕ∞) < τ z}) ∩ {z | (t : ℕ∞) < τ z}ᶜ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, enat_eq_coe_iff, Set.mem_inter_iff,
        Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq, Set.mem_compl_iff]
    rw [heq]
    exact (MeasurableSet.biInter (Finset.range t).countable_toSet
      fun s _ => hτ.measurableSet_lt s).inter (hτ.measurableSet_lt t).compl

/-- The event `{τ = t}` is measurable with respect to the first `t` coordinates. -/
theorem IsStoppingRule.measurableSet_eq (hτ : IsStoppingRule τ) (t : ℕ) :
    MeasurableSet[MeasurableSpace.comap (seqPrefix t) inferInstance] {z | τ z = t} := by
  refine measurableSet_comap_seqPrefix_of_agree
    (hτ.measurable (measurableSet_singleton (t : ℕ∞))) fun z z' h hz => ?_
  simp only [Set.mem_ofPred_eq, enat_eq_coe_iff] at hz ⊢
  refine ⟨fun s hs => ?_, ?_⟩
  · exact (mem_iff_of_measurableSet_comap_seqPrefix (hτ s)
      fun i hi => h i (hi.trans hs)).mp (hz.1 s hs)
  · exact fun h' => hz.2 ((mem_iff_of_measurableSet_comap_seqPrefix (hτ t) h).mpr h')

/-- The restart map is measurable. -/
theorem measurable_shiftBy (hτ : IsStoppingRule τ) : Measurable (shiftBy τ) := by
  refine measurable_pi_lambda _ fun j => ?_
  have hm : Measurable (fun p : (ℕ → E) × ℕ => p.1 (p.2 + j)) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply (n + j)
  exact hm.comp
    (measurable_id.prodMk ((Measurable.of_discrete (f := ENat.toNat)).comp hτ.measurable))

/-! ## The iid process at a deterministic time -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → E}

theorem measurable_seq (hZ : ∀ n, Measurable (Z n)) : Measurable (seq Z) :=
  measurable_pi_lambda _ hZ

/-- The fixed future from time `t` is independent of the first `t` coordinates. -/
theorem indep_future_prefix (hZ : ∀ n, Measurable (Z n)) (hi : iIndepFun Z P) (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω (j : ℕ) => Z (t + j) ω) inferInstance)
      (MeasurableSpace.comap (fun ω => seqPrefix t (seq Z ω)) inferInstance) P := by
  have hd : Disjoint (Set.Ici t) (Set.Iio t) := by
    apply Set.disjoint_left.mpr
    intro i h1 h2
    simp only [Set.mem_Ici, Set.mem_Iio] at h1 h2
    omega
  have h := indep_iSup_of_disjoint (fun k => (hZ k).comap_le) hi.iIndep hd
  have h1 : MeasurableSpace.comap (fun ω (j : ℕ) => Z (t + j) ω) inferInstance ≤
      ⨆ i ∈ Set.Ici t, MeasurableSpace.comap (Z i) inferInstance := by
    rw [MeasurableSpace.comap_process_pi]
    refine iSup_le fun j => ?_
    exact le_iSup_of_le (t + j) (le_iSup_of_le (by simp) le_rfl)
  have h2 : MeasurableSpace.comap (fun ω => seqPrefix t (seq Z ω)) inferInstance ≤
      ⨆ i ∈ Set.Iio t, MeasurableSpace.comap (Z i) inferInstance := by
    change MeasurableSpace.comap (fun ω (i : Fin t) => Z i ω) inferInstance ≤ _
    rw [MeasurableSpace.comap_process_pi]
    refine iSup_le fun i => ?_
    exact le_iSup_of_le (i : ℕ) (le_iSup_of_le (by simp) le_rfl)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h h1) h2

/-- The fixed future from time `t` has the law of the whole sequence. -/
theorem identDistrib_future (hZ : ∀ n, Measurable (Z n)) (hi : iIndepFun Z P)
    (hid : ∀ n, IdentDistrib (Z n) (Z 0) P P) (t : ℕ) :
    IdentDistrib (fun ω (j : ℕ) => Z (t + j) ω) (seq Z) P P := by
  have hshift : iIndepFun (fun j : ℕ => Z (t + j)) P :=
    hi.precomp (g := fun j : ℕ => t + j) (by intro i j hij; dsimp at hij; omega)
  refine ⟨(measurable_pi_lambda _ fun j => hZ (t + j)).aemeasurable,
    (measurable_seq hZ).aemeasurable, ?_⟩
  rw [hshift.map_fun_eq_infinitePi_map (fun j => hZ (t + j))]
  change _ = P.map (fun ω i => Z i ω)
  rw [hi.map_fun_eq_infinitePi_map hZ]
  congr 1
  funext j
  exact (hid (t + j)).map_eq.trans (hid j).map_eq.symm

omit [MeasurableSpace E] in
/-- Countable additivity over the finite values of an almost surely finite `ℕ∞`-valued map. -/
theorem measure_eq_tsum_eq_coe {T : Ω → ℕ∞} (hT : Measurable T)
    (hfin : ∀ᵐ ω ∂P, T ω ≠ ⊤) {S : Set Ω} (hS : MeasurableSet S) :
    P S = ∑' t : ℕ, P (S ∩ {ω | T ω = t}) := by
  have hu : S =ᵐ[P] ⋃ t : ℕ, S ∩ {ω | T ω = t} := by
    filter_upwards [hfin] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    apply propext
    change ω ∈ S ↔ ω ∈ ⋃ t : ℕ, S ∩ {ω | T ω = t}
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun hs => ⟨n, hs, hn.symm⟩, fun ⟨_, hs, _⟩ => hs⟩
  calc
    P S = P (⋃ t : ℕ, S ∩ {ω | T ω = t}) := measure_congr hu
    _ = ∑' t : ℕ, P (S ∩ {ω | T ω = t}) := by
      apply measure_iUnion
      · intro i j hij
        apply Set.disjoint_left.mpr
        rintro ω ⟨_, hi⟩ ⟨_, hj⟩
        apply hij
        exact_mod_cast hi.symm.trans hj
      · intro n
        exact hS.inter (hT (measurableSet_singleton _))

/-! ## Restart at the stopping rule -/

/-- The restart factorization on every stopped event: if `A` is measurable and each slice
`A ∩ {τ = t}` is measurable with respect to the first `t` coordinates, then
`P(seq Z ∈ A, shiftBy τ (seq Z) ∈ B) = P(seq Z ∈ A) P(seq Z ∈ B)`. -/
theorem measure_inter_shiftBy (hZ : ∀ n, Measurable (Z n)) (hi : iIndepFun Z P)
    (hid : ∀ n, IdentDistrib (Z n) (Z 0) P P) (hτ : IsStoppingRule τ)
    (hfin : ∀ᵐ ω ∂P, τ (seq Z ω) ≠ ⊤)
    {A : Set (ℕ → E)} (hA : MeasurableSet A)
    (hAt : ∀ t : ℕ, MeasurableSet[MeasurableSpace.comap (seqPrefix t) inferInstance]
      (A ∩ {z | τ z = t}))
    {B : Set (ℕ → E)} (hB : MeasurableSet B) :
    P (seq Z ⁻¹' A ∩ (fun ω => shiftBy τ (seq Z ω)) ⁻¹' B) =
      P (seq Z ⁻¹' A) * P (seq Z ⁻¹' B) := by
  have hW := measurable_seq hZ
  have hT : Measurable (fun ω => τ (seq Z ω)) := hτ.measurable.comp hW
  have hS : Measurable (fun ω => shiftBy τ (seq Z ω)) := (measurable_shiftBy hτ).comp hW
  rw [measure_eq_tsum_eq_coe hT hfin ((hW hA).inter (hS hB))]
  calc
    (∑' t : ℕ, P ((seq Z ⁻¹' A ∩ (fun ω => shiftBy τ (seq Z ω)) ⁻¹' B) ∩
      {ω | τ (seq Z ω) = t})) =
        ∑' t : ℕ, P (seq Z ⁻¹' A ∩ {ω | τ (seq Z ω) = t}) * P (seq Z ⁻¹' B) := by
      refine tsum_congr fun t => ?_
      have heq : (seq Z ⁻¹' A ∩ (fun ω => shiftBy τ (seq Z ω)) ⁻¹' B) ∩
          {ω | τ (seq Z ω) = t} =
          (fun ω (j : ℕ) => Z (t + j) ω) ⁻¹' B ∩ seq Z ⁻¹' (A ∩ {z | τ z = t}) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
        have hsh (ht : τ (seq Z ω) = t) : shiftBy τ (seq Z ω) = fun j => Z (t + j) ω := by
          funext j
          simp only [shiftBy, ht, ENat.toNat_natCast, seq]
        constructor
        · rintro ⟨⟨ha, hb⟩, ht⟩
          exact ⟨hsh ht ▸ hb, ha, ht⟩
        · rintro ⟨hb, ha, ht⟩
          exact ⟨⟨ha, (hsh ht).symm ▸ hb⟩, ht⟩
      rw [heq]
      have hmB : MeasurableSet[MeasurableSpace.comap (fun ω (j : ℕ) => Z (t + j) ω)
          inferInstance] ((fun ω (j : ℕ) => Z (t + j) ω) ⁻¹' B) := ⟨B, hB, rfl⟩
      have hmA : MeasurableSet[MeasurableSpace.comap (fun ω => seqPrefix t (seq Z ω))
          inferInstance] (seq Z ⁻¹' (A ∩ {z | τ z = t})) := by
        obtain ⟨S, hS, hSeq⟩ := hAt t
        exact ⟨S, hS, by rw [← hSeq]; rfl⟩
      rw [(Indep_iff _ _ P).mp (indep_future_prefix hZ hi t) _ _ hmB hmA,
        (identDistrib_future hZ hi hid t).measure_mem_eq hB, mul_comm]
      rfl
    _ = P (seq Z ⁻¹' A) * P (seq Z ⁻¹' B) := by
      rw [ENNReal.tsum_mul_right, ← measure_eq_tsum_eq_coe hT hfin (hW hA)]

/-- The restarted sequence has the law of the original sequence. -/
theorem identDistrib_shiftBy [IsProbabilityMeasure P] (hZ : ∀ n, Measurable (Z n))
    (hi : iIndepFun Z P) (hid : ∀ n, IdentDistrib (Z n) (Z 0) P P)
    (hτ : IsStoppingRule τ) (hfin : ∀ᵐ ω ∂P, τ (seq Z ω) ≠ ⊤) :
    IdentDistrib (fun ω => shiftBy τ (seq Z ω)) (seq Z) P P := by
  have hW := measurable_seq hZ
  have hS : Measurable (fun ω => shiftBy τ (seq Z ω)) := (measurable_shiftBy hτ).comp hW
  refine ⟨hS.aemeasurable, hW.aemeasurable, ?_⟩
  ext B hB
  rw [Measure.map_apply hS hB, Measure.map_apply hW hB]
  have h := measure_inter_shiftBy hZ hi hid hτ hfin MeasurableSet.univ
    (fun t => by simpa only [Set.univ_inter] using hτ.measurableSet_eq t) hB
  simpa using h

/-- Any measurable functional of the stopped block (the value `τ z` together with the
coordinates `z t`, `t < τ z`) is independent of the restarted sequence. -/
theorem indepFun_block_shiftBy [IsProbabilityMeasure P] (hZ : ∀ n, Measurable (Z n))
    (hi : iIndepFun Z P) (hid : ∀ n, IdentDistrib (Z n) (Z 0) P P)
    (hτ : IsStoppingRule τ) (hfin : ∀ᵐ ω ∂P, τ (seq Z ω) ≠ ⊤)
    {T : Type*} [MeasurableSpace T] {D : (ℕ → E) → T} (hDm : Measurable D)
    (hD : ∀ z z', τ z = τ z' → (∀ t : ℕ, (t : ℕ∞) < τ z → z t = z' t) → D z = D z') :
    IndepFun (fun ω => D (seq Z ω)) (fun ω => shiftBy τ (seq Z ω)) P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro C B hC hB
  have hAt : ∀ t : ℕ, MeasurableSet[MeasurableSpace.comap (seqPrefix t) inferInstance]
      (D ⁻¹' C ∩ {z | τ z = t}) := by
    intro t
    refine measurableSet_comap_seqPrefix_of_agree
      ((hDm hC).inter (hτ.measurable (measurableSet_singleton _))) fun z z' h hz => ?_
    obtain ⟨hzC, hzt⟩ := hz
    have hz't : τ z' = t :=
      (mem_iff_of_measurableSet_comap_seqPrefix (hτ.measurableSet_eq t) h).mp hzt
    refine ⟨?_, hz't⟩
    have hDz : D z = D z' := hD z z' (hzt.trans hz't.symm) fun s hs => by
      rw [Set.mem_ofPred_eq] at hzt
      rw [hzt, Nat.cast_lt] at hs
      exact h s hs
    simpa [Set.mem_preimage, hDz] using hzC
  have h := measure_inter_shiftBy hZ hi hid hτ hfin (hDm hC) hAt hB
  rw [(identDistrib_shiftBy hZ hi hid hτ hfin).measure_mem_eq hB]
  exact h

/-! ## Iterating a regenerative split

The generic part: a measurable state `W : Ω → S`, a measurable reward `D : S → T` and a
measurable remainder `R : S → S` with `R ∘ W ∼ W` and `D ∘ W ⟂ R ∘ W`. -/

section Regenerative

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T] {μ : Measure Ω}
  {D : S → T} {R : S → S} {W : Ω → S}

/-- Each iterated remainder state has the original state law. -/
theorem regen_identDistrib_iterate (hR : Measurable R) (hW : Measurable W)
    (hLaw : IdentDistrib (fun ω => R (W ω)) W μ μ) (n : ℕ) :
    IdentDistrib (fun ω => R^[n] (W ω)) W μ μ := by
  induction n with
  | zero => exact IdentDistrib.refl hW.aemeasurable
  | succ n ih =>
    have heq : (fun ω => R^[n + 1] (W ω)) = fun ω => R (R^[n] (W ω)) :=
      funext fun ω => Function.iterate_succ_apply' R n (W ω)
    rw [heq]
    exact (ih.comp hR).trans hLaw

/-- The same independent reward/remainder split holds at every iterated state. -/
theorem regen_indepFun_iterate [IsProbabilityMeasure μ] (hD : Measurable D)
    (hR : Measurable R) (hW : Measurable W) (hLaw : IdentDistrib (fun ω => R (W ω)) W μ μ)
    (hSplit : IndepFun (fun ω => D (W ω)) (fun ω => R (W ω)) μ) (n : ℕ) :
    IndepFun (fun ω => D (R^[n] (W ω))) (fun ω => R (R^[n] (W ω))) μ :=
  indepFun_of_identDistrib_pair hSplit
    ((regen_identDistrib_iterate hR hW hLaw n).symm.comp (hD.prodMk hR))

/-- A reward is independent of every finite tuple of strictly later rewards. -/
theorem regen_indepFun_later [IsProbabilityMeasure μ] (hD : Measurable D)
    (hR : Measurable R) (hW : Measurable W) (hLaw : IdentDistrib (fun ω => R (W ω)) W μ μ)
    (hSplit : IndepFun (fun ω => D (W ω)) (fun ω => R (W ω)) μ)
    (a : ℕ) (s : Finset ℕ) (hord : ∀ i ∈ s, a < i) :
    IndepFun (fun ω => D (R^[a] (W ω))) (fun ω (i : s) => D (R^[i.val] (W ω))) μ := by
  let G : S → (s → T) := fun x i => D (R^[i.val - (a + 1)] x)
  have hG : Measurable G := measurable_pi_lambda _ fun i =>
    hD.comp (hR.iterate (i.val - (a + 1)))
  have heq : (fun ω (i : s) => D (R^[i.val] (W ω))) =
      G ∘ (fun ω => R (R^[a] (W ω))) := by
    funext ω i
    dsimp [G]
    rw [← Function.iterate_succ_apply' R a,
      ← Function.iterate_add_apply R (i.val - (a + 1)) (a + 1)]
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (hord i.val i.property))]
  rw [heq]
  exact (regen_indepFun_iterate hD hR hW hLaw hSplit a).comp measurable_id hG

/-- The iterated rewards are mutually independent. -/
theorem regen_iIndepFun [IsProbabilityMeasure μ] (hD : Measurable D)
    (hR : Measurable R) (hW : Measurable W) (hLaw : IdentDistrib (fun ω => R (W ω)) W μ μ)
    (hSplit : IndepFun (fun ω => D (W ω)) (fun ω => R (W ω)) μ) :
    iIndepFun (fun n ω => D (R^[n] (W ω))) μ := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s
  induction s using Finset.induction_on_min with
  | empty => intro sets hsets; simp
  | insert a s hord ih =>
    intro sets hsets
    have ha : a ∉ s := fun ha => (lt_irrefl a) (hord a ha)
    have hs (i : ℕ) (hi : i ∈ s) : MeasurableSet (sets i) :=
      hsets i (Finset.mem_insert_of_mem hi)
    let B : Set (s → T) := {v | ∀ i : s, v i ∈ sets i.val}
    have hB : MeasurableSet B := by
      have heqB : B = ⋂ i : s, (fun v : s → T => v i) ⁻¹' sets i.val := by ext v; simp [B]
      rw [heqB]
      exact MeasurableSet.iInter fun i => (measurable_pi_apply i) (hs i.val i.property)
    have hpre : (fun ω (i : s) => D (R^[i.val] (W ω))) ⁻¹' B =
        ⋂ i ∈ s, (fun ω => D (R^[i] (W ω))) ⁻¹' sets i := by
      ext ω
      simp [B]
    have hpair := (regen_indepFun_later hD hR hW hLaw hSplit a s hord).measure_inter_preimage_eq_mul
      _ _ (hsets a (Finset.mem_insert_self _ _)) hB
    rw [hpre] at hpair
    have heq : (⋂ i ∈ insert a s, (fun ω => D (R^[i] (W ω))) ⁻¹' sets i) =
        (fun ω => D (R^[a] (W ω))) ⁻¹' sets a ∩
          ⋂ i ∈ s, (fun ω => D (R^[i] (W ω))) ⁻¹' sets i := by ext ω; simp
    rw [heq, hpair, ih hs, Finset.prod_insert ha]

end Regenerative

/-! ## Iterated restarts of an iid sequence -/

/-- Every iterated restart has the law of the original sequence. -/
theorem identDistrib_iterate_shiftBy [IsProbabilityMeasure P] (hZ : ∀ n, Measurable (Z n))
    (hi : iIndepFun Z P) (hid : ∀ n, IdentDistrib (Z n) (Z 0) P P)
    (hτ : IsStoppingRule τ) (hfin : ∀ᵐ ω ∂P, τ (seq Z ω) ≠ ⊤) (j : ℕ) :
    IdentDistrib (fun ω => (shiftBy τ)^[j] (seq Z ω)) (seq Z) P P :=
  regen_identDistrib_iterate (measurable_shiftBy hτ) (measurable_seq hZ)
    (identDistrib_shiftBy hZ hi hid hτ hfin) j

/-- The stopping rule is almost surely finite along every iterated restart. -/
theorem ae_iterate_ne_top [IsProbabilityMeasure P] (hZ : ∀ n, Measurable (Z n))
    (hi : iIndepFun Z P) (hid : ∀ n, IdentDistrib (Z n) (Z 0) P P)
    (hτ : IsStoppingRule τ) (hfin : ∀ᵐ ω ∂P, τ (seq Z ω) ≠ ⊤) (j : ℕ) :
    ∀ᵐ ω ∂P, τ ((shiftBy τ)^[j] (seq Z ω)) ≠ ⊤ :=
  (identDistrib_iterate_shiftBy hZ hi hid hτ hfin j).symm.ae_snd
    (p := fun z => τ z ≠ ⊤) (hτ.measurable (measurableSet_singleton ⊤)).compl hfin

/-- The iterated block rewards are identically distributed. -/
theorem identDistrib_rewards [IsProbabilityMeasure P] (hZ : ∀ n, Measurable (Z n))
    (hi : iIndepFun Z P) (hid : ∀ n, IdentDistrib (Z n) (Z 0) P P)
    (hτ : IsStoppingRule τ) (hfin : ∀ᵐ ω ∂P, τ (seq Z ω) ≠ ⊤)
    {T : Type*} [MeasurableSpace T] {D : (ℕ → E) → T} (hDm : Measurable D) (j : ℕ) :
    IdentDistrib (fun ω => D ((shiftBy τ)^[j] (seq Z ω))) (fun ω => D (seq Z ω)) P P :=
  (identDistrib_iterate_shiftBy hZ hi hid hτ hfin j).comp hDm

/-- The iterated block rewards are mutually independent. -/
theorem iIndepFun_rewards [IsProbabilityMeasure P] (hZ : ∀ n, Measurable (Z n))
    (hi : iIndepFun Z P) (hid : ∀ n, IdentDistrib (Z n) (Z 0) P P)
    (hτ : IsStoppingRule τ) (hfin : ∀ᵐ ω ∂P, τ (seq Z ω) ≠ ⊤)
    {T : Type*} [MeasurableSpace T] {D : (ℕ → E) → T} (hDm : Measurable D)
    (hD : ∀ z z', τ z = τ z' → (∀ t : ℕ, (t : ℕ∞) < τ z → z t = z' t) → D z = D z') :
    iIndepFun (fun j ω => D ((shiftBy τ)^[j] (seq Z ω))) P :=
  regen_iIndepFun hDm (measurable_shiftBy hτ) (measurable_seq hZ)
    (identDistrib_shiftBy hZ hi hid hτ hfin)
    (indepFun_block_shiftBy hZ hi hid hτ hfin hDm hD)

end PGM
