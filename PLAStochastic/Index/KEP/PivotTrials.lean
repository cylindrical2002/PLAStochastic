import PLAStochastic.Index.KEP.SampleToAnchored
import PLAStochastic.Index.KEP.GoodAnchor
import PLAStochastic.Index.KEP.PivotRestart
import PLAStochastic.Index.KEP.PivotStopping
import PLAStochastic.Index.KEP.OrderStatisticReset
import PLAStochastic.Index.Algorithm.EndpointTop

/-!
# Trials at the layer-`L` pivots of a Model K sample

Source: `proofs/proofK_endpoint_scale.tex`, proof of `ksc:thm:endpoint-scale`, part
"Upper bound before a deterministic horizon", and `ksc:lem:adapted-trials`.

For `v : Fin N → ℝ` let `ρ i = layerPivot eps (samplePairs Q v) L i` (`samplePivot`) be the
layer-`L` pivots of the sample keys `Q ∘ v`.  Fix a horizon `𝔥 ≤ N` and a target gap `gap₀ ≥ 1`.
Trial `i` is *active* if `ρ i < 𝔥` and the anchor `v (ρ i)` lies in the window of
`goodAnchors` (`AnchorGood`); it *succeeds* if moreover the next gap is at least
`min gap₀ (𝔥 - ρ i)` (`trialActive`, `trialSuccess`).

* **Shift identity** (`samplePairs_shift_eq_anchPairsW`, `layerPivot_samplePairs_succ_sub`).
  Restarted at rank `r` with `v r ≠ 1`, the sample pairs are `anchPairsW Q (v r) (resc r v)`,
  so the next gap after a pivot at `r` is the leading pivot of these anchored pairs.
* **Reset at the `i`-th pivot** (`ofReal_mul_orderLaw_trialActive_le`).  If the anchored success
  event has probability at least `p` for every nonnegative good anchor value at every rank
  `r < 𝔥`, then `p · P(trial i active) ≤ P(trial i succeeds)`.  On `{ρ i = r}` the active event
  is a `pre r`-preimage and the success event depends on `(v r, resc r v)`
  (`Renyi.map_pre_resc_orderLaw`, `mul_orderLaw_pre_le`).  The window of `goodAnchors` contains
  negative values when `r < N / 2`, but the sorted uniforms are almost surely positive
  (`ae_orderLaw_mem_simplex`), so the success bound is needed only at `0 ≤ v r`.  No filtration
  is needed: only the one-trial inequality enters the sum over trials.
* **Counting** (`card_trial_success_le`, `sum_indicator_trialSuccess_le`).  Deterministically at
  most `𝔥 / gap₀ + 1` trials succeed.
* **Layer size** (`epLayer_snd_eq_card_samplePivot`, `epLayer_snd_le_sum_trialActive`).  The
  layer-`L` size is the number of pivots below `N`, at most the number of active trials plus
  `N / q^L + 1` off `goodAnchors N D` plus `(N - 𝔥) / q^L + 1` pivots in `[𝔥, N)`.
* **Main bound** (`integral_epLayer_snd_le`).  Under `orderLaw N`,
  `E[layer-L size] ≤ (𝔥 / gap₀ + 2) / p + (N / q^L + 1) · P(goodAnchorsᶜ) + (N - 𝔥) / q^L + 1`,
  `q = ⌊2 eps⌋₊ + 1`.
-/

namespace PGM

noncomputable section

open MeasureTheory Finset

/-! ## Counting successful trials (deterministic) -/

/-- **Trial count.**  Along a strictly increasing pivot sequence `ρ`, the pivots `ρ i < 𝔥`
    followed by a gap of at least `min gap₀ (𝔥 - ρ i)` number at most `𝔥 / gap₀ + 1`. -/
theorem card_trial_success_le {ρ : ℕ → ℕ} (hρ : StrictMono ρ) {𝔥 gap₀ : ℕ} (hgap : 1 ≤ gap₀)
    (S : Finset ℕ) :
    #{i ∈ S | ρ i < 𝔥 ∧ min gap₀ (𝔥 - ρ i) ≤ ρ (i + 1) - ρ i} ≤ 𝔥 / gap₀ + 1 := by
  set T := {i ∈ S | ρ i < 𝔥 ∧ min gap₀ (𝔥 - ρ i) ≤ ρ (i + 1) - ρ i} with hT
  have hsplit := card_filter_add_card_filter_not (s := T) (fun i => ρ i + gap₀ ≤ 𝔥)
  have hmono := hρ.monotone
  have h1 : #{i ∈ T | ρ i + gap₀ ≤ 𝔥} ≤ 𝔥 / gap₀ := by
    have hmaps : Set.MapsTo (fun i => ρ i / gap₀) ({i ∈ T | ρ i + gap₀ ≤ 𝔥} : Finset ℕ)
        (range (𝔥 / gap₀)) := by
      intro i hi
      simp only [coe_filter, hT, mem_filter, Set.mem_ofPred_eq] at hi
      simp only [coe_range, Set.mem_Iio]
      have h := Nat.div_le_div_right (c := gap₀) hi.2
      rw [Nat.add_div_right _ (by omega)] at h
      omega
    have hinj : Set.InjOn (fun i => ρ i / gap₀) ({i ∈ T | ρ i + gap₀ ≤ 𝔥} : Finset ℕ) := by
      have key : ∀ i j, i ∈ ({i ∈ T | ρ i + gap₀ ≤ 𝔥} : Finset ℕ) → i < j →
          ρ i / gap₀ < ρ j / gap₀ := by
        intro i j hi hij
        simp only [hT, mem_filter] at hi
        obtain ⟨⟨-, hi1, hi2⟩, hi3⟩ := hi
        have hg : ρ i + gap₀ ≤ ρ (i + 1) := by
          have : min gap₀ (𝔥 - ρ i) = gap₀ := min_eq_left (by omega)
          have := hρ (Nat.lt_succ_self i)
          omega
        have h := Nat.div_le_div_right (c := gap₀) (hg.trans (hmono (Nat.succ_le_of_lt hij)))
        rw [Nat.add_div_right _ (by omega)] at h
        omega
      intro i hi j hj hij
      simp only at hij
      rcases lt_trichotomy i j with h | h | h
      · exact absurd hij (key i j hi h).ne
      · exact h
      · exact absurd hij (key j i hj h).ne'
    simpa using card_le_card_of_injOn _ hmaps hinj
  have h2 : #{i ∈ T | ¬ ρ i + gap₀ ≤ 𝔥} ≤ 1 := by
    have key : ∀ i ∈ ({i ∈ T | ¬ ρ i + gap₀ ≤ 𝔥} : Finset ℕ), ρ i < 𝔥 ∧ 𝔥 ≤ ρ (i + 1) := by
      intro i hi
      simp only [hT, mem_filter] at hi
      obtain ⟨⟨-, hi1, hi2⟩, hi3⟩ := hi
      have : min gap₀ (𝔥 - ρ i) = 𝔥 - ρ i := min_eq_right (by omega)
      have := hρ (Nat.lt_succ_self i)
      omega
    refine card_le_one.2 fun i hi j hj => ?_
    obtain ⟨hi1, hi2⟩ := key i hi
    obtain ⟨hj1, hj2⟩ := key j hj
    rcases lt_trichotomy i j with h | h | h
    · have := hmono (show i + 1 ≤ j by omega); omega
    · exact h
    · have := hmono (show j + 1 ≤ i by omega); omega
  omega

/-! ## The sample pairs restarted at a rank -/

section Shift

open Renyi

variable {r m : ℕ}

/-- For `pivot r v ≠ 1`, the anchored positions after `v r` recover the future of `v`. -/
theorem pivot_add_mul_anchPos_resc {v : Fin (r + 1 + m) → ℝ} (hv : pivot r v ≠ 1) {s : ℕ}
    (hs : s ≤ m) :
    pivot r v + (1 - pivot r v) * anchPos (resc r v) s = v ⟨r + s, by omega⟩ := by
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · simp only [anchPos, Nat.le_zero, Nat.one_ne_zero, false_and, dif_neg, not_false_eq_true,
      mul_zero, add_zero]
    rfl
  · rw [anchPos, dif_pos ⟨hs1, hs⟩, ← future_eq_pivot_add hv ⟨s - 1, by omega⟩]
    congr 1
    ext
    simp only [Fin.val_natAdd]
    omega

/-- **Shift identity.**  Restarted at rank `r`, the sample pairs are the anchored pairs with
    anchor value `v r` and positions `resc r v`. -/
theorem samplePairs_shift_eq_anchPairsW (Q : ℝ → ℝ) {v : Fin (r + 1 + m) → ℝ}
    (hv : pivot r v ≠ 1) :
    (fun t => samplePairs Q v (r + t)) = anchPairsW Q (pivot r v) (resc r v) := by
  funext t
  refine Prod.ext ?_ rfl
  by_cases ht : t < m
  · simp only [samplePairs, anchPairsW, dif_pos (show r + t + 1 < r + 1 + m by omega), if_pos ht]
    rw [pivot_add_mul_anchPos_resc hv (s := t + 1) (by omega),
      pivot_add_mul_anchPos_resc hv (s := t) (by omega)]
    rfl
  · simp only [samplePairs, anchPairsW, dif_neg (show ¬ r + t + 1 < r + 1 + m by omega),
      if_neg ht]

/-- **Next gap after a pivot.**  If the layer-`L` pivot `i` of the sample pairs sits at rank
    `r` with `v r ≠ 1`, the next layer-`L` gap is the leading layer-`L` pivot of the
    anchored pairs at `(v r, resc r v)`. -/
theorem layerPivot_samplePairs_succ_sub (eps : ℝ) (Q : ℝ → ℝ) {v : Fin (r + 1 + m) → ℝ}
    (hv : pivot r v ≠ 1) {L i : ℕ} (hr : layerPivot eps (samplePairs Q v) L i = r) :
    layerPivot eps (samplePairs Q v) L (i + 1) - layerPivot eps (samplePairs Q v) L i =
      layerPivot eps (anchPairsW Q (pivot r v) (resc r v)) L 1 := by
  rw [layerPivot_succ_sub (samplePairs_snd Q v) L i, hr, samplePairs_shift_eq_anchPairsW Q hv]

end Shift

/-! ## Reset at a deterministic rank -/

section Reset

open Renyi

variable {r m : ℕ}

/-- **Reset, lower bound.**  If an event `F` of the anchor value and the rescaled future has
    conditional probability at least `c` for every past `x ∈ C` with nonnegative pivot value,
    then `c · P(pre ∈ C) ≤ P(pre ∈ C, (pivot, resc) ∈ F)`.  The sorted uniforms are almost
    surely positive, so pasts with a negative pivot value are negligible. -/
theorem mul_orderLaw_pre_le {C : Set (Fin (r + 1) → ℝ)} (hC : MeasurableSet C)
    {F : Set (ℝ × (Fin m → ℝ))} (hF : MeasurableSet F) {c : ENNReal}
    (h : ∀ x ∈ C, 0 ≤ x (Fin.last r) → c ≤ orderLaw m {w | (x (Fin.last r), w) ∈ F}) :
    c * orderLaw (r + 1 + m) (pre r ⁻¹' C) ≤
      orderLaw (r + 1 + m) (pre r ⁻¹' C ∩ {v | (pivot r v, resc r v) ∈ F}) := by
  set C' : Set (Fin (r + 1) → ℝ) := C ∩ {x | 0 ≤ x (Fin.last r)} with hC'def
  have hC' : MeasurableSet C' :=
    hC.inter (measurableSet_le measurable_const (measurable_pi_apply _))
  have heq : orderLaw (r + 1 + m) (pre r ⁻¹' C) = orderLaw (r + 1 + m) (pre r ⁻¹' C') := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [ae_orderLaw_mem_simplex (r + 1 + m)] with v hv
    have h0 : 0 ≤ pre r v (Fin.last r) := (hv.2.1 _).le
    simp only [hC'def, Set.preimage_inter, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_ofPred_eq, h0, and_true]
  rw [heq]
  refine le_trans ?_ (measure_mono (Set.inter_subset_inter_left _
    (Set.preimage_mono (Set.inter_subset_left : C' ⊆ C))))
  set S : Set ((Fin (r + 1) → ℝ) × (Fin m → ℝ)) := {q | q.1 ∈ C' ∧ (q.1 (Fin.last r), q.2) ∈ F}
    with hSdef
  have hSm : MeasurableSet S :=
    (measurable_fst hC').inter
      ((((measurable_pi_apply (Fin.last r)).comp measurable_fst).prodMk measurable_snd) hF)
  have hset : pre r ⁻¹' C' ∩ {v | (pivot r v, resc r v) ∈ F} =
      (fun v => (pre r v, resc r v)) ⁻¹' S := rfl
  rw [hset, ← Measure.map_apply measurable_pre_resc hSm, map_pre_resc_orderLaw,
    Measure.prod_apply hSm, ← preLaw_apply hC', ← lintegral_indicator_const hC']
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ C'
  · rw [Set.indicator_of_mem hx]
    refine (h x hx.1 hx.2).trans_eq ?_
    congr 1
    ext w
    simp [hSdef, hx]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

end Reset

/-! ## Trials at the sample pivots -/

section Trials

/-- The anchor window at rank `r` for sample size `N`:
    `(N - r)/(2N) ≤ 1 - u ≤ 2 (N - r)/N` (the condition of `goodAnchors`). -/
def AnchorGood (N r : ℕ) (u : ℝ) : Prop :=
  ((N - r : ℕ) : ℝ) / (2 * N) ≤ 1 - u ∧ 1 - u ≤ 2 * ((N - r : ℕ) : ℝ) / N

theorem measurableSet_anchorGood (N r : ℕ) : MeasurableSet {u : ℝ | AnchorGood N r u} :=
  (measurableSet_le measurable_const (measurable_const.sub measurable_id)).inter
    (measurableSet_le (measurable_const.sub measurable_id) measurable_const)

theorem AnchorGood.lt_one {N r : ℕ} {u : ℝ} (hr : r < N) (h : AnchorGood N r u) : u < 1 := by
  have h1 : (0 : ℝ) < ((N - r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - r)
  have h2 : (0 : ℝ) < 2 * N := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    linarith
  have := div_pos h1 h2
  linarith [h.1]

/-- The layer-`L` pivots of the sample pairs. -/
abbrev samplePivot (eps : ℝ) (Q : ℝ → ℝ) (L : ℕ) {N : ℕ} (v : Fin N → ℝ) (i : ℕ) : ℕ :=
  layerPivot eps (samplePairs Q v) L i

/-- Trial `i` is active: the pivot `i` lies before the horizon and its anchor is good. -/
def trialActive (eps : ℝ) (Q : ℝ → ℝ) (L 𝔥 N i : ℕ) : Set (Fin N → ℝ) :=
  {v | samplePivot eps Q L v i < 𝔥 ∧
    AnchorGood N (samplePivot eps Q L v i) (extendKeys v (samplePivot eps Q L v i))}

/-- Trial `i` succeeds: it is active and the next gap is at least `min gap₀ (𝔥 - ρ i)`. -/
def trialSuccess (eps : ℝ) (Q : ℝ → ℝ) (L 𝔥 gap₀ N i : ℕ) : Set (Fin N → ℝ) :=
  trialActive eps Q L 𝔥 N i ∩
    {v | min gap₀ (𝔥 - samplePivot eps Q L v i) ≤
      samplePivot eps Q L v (i + 1) - samplePivot eps Q L v i}

variable {N : ℕ} {Q : ℝ → ℝ} {eps : ℝ}

theorem measurable_samplePairs (hQ : Measurable Q) :
    Measurable (samplePairs Q (N := N)) :=
  measurable_pi_lambda _ fun i =>
    ((measurable_samplePairs_fst hQ i).mono (Renyi.coordSigma_le N (i + 1)) le_rfl).prodMk
      measurable_const

theorem measurable_samplePivot (hQ : Measurable Q) (eps : ℝ) (L i : ℕ) :
    Measurable fun v : Fin N → ℝ => samplePivot eps Q L v i :=
  (measurable_layerPivot eps L i).comp (measurable_samplePairs hQ)

theorem measurableSet_trialActive (hQ : Measurable Q) (eps : ℝ) (L 𝔥 i : ℕ) :
    MeasurableSet (trialActive eps Q L 𝔥 N i) := by
  have hset : trialActive eps Q L 𝔥 N i = ⋃ r ∈ range 𝔥,
      {v | samplePivot eps Q L v i = r} ∩ {v | AnchorGood N r (extendKeys v r)} := by
    ext v
    simp only [trialActive, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, mem_range,
      exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, rfl, h2⟩
    · rintro ⟨r, hr, rfl, h2⟩
      exact ⟨hr, h2⟩
  rw [hset]
  exact Finset.measurableSet_biUnion _ fun r _ =>
    (measurable_samplePivot hQ eps L i (measurableSet_singleton r)).inter
      ((measurableSet_anchorGood N r).preimage ((measurable_pi_apply r).comp measurable_extendKeys))

theorem measurableSet_trialSuccess (hQ : Measurable Q) (eps : ℝ) (L 𝔥 gap₀ i : ℕ) :
    MeasurableSet (trialSuccess eps Q L 𝔥 gap₀ N i) := by
  refine (measurableSet_trialActive hQ eps L 𝔥 i).inter ?_
  have hm : Measurable fun v : Fin N → ℝ =>
      (samplePivot eps Q L v i, samplePivot eps Q L v (i + 1)) :=
    (measurable_samplePivot hQ eps L i).prodMk (measurable_samplePivot hQ eps L (i + 1))
  exact hm (MeasurableSet.of_discrete (s := {q : ℕ × ℕ | min gap₀ (𝔥 - q.1) ≤ q.2 - q.1}))

end Trials

/-! ## Reset at the `i`-th pivot -/

section TrialReset

variable {N : ℕ} {Q : ℝ → ℝ} {eps : ℝ}

/-- Split an event on which a measurable `ℕ`-valued time is `< 𝔥` over its values. -/
theorem measure_eq_sum_inter_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) {E : Set α}
    (hE : MeasurableSet E) {f : α → ℕ} (hf : Measurable f) {𝔥 : ℕ} (hsub : ∀ v ∈ E, f v < 𝔥) :
    μ E = ∑ r ∈ range 𝔥, μ (E ∩ {v | f v = r}) := by
  have hset : E = ⋃ r ∈ range 𝔥, E ∩ {v | f v = r} := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_range, exists_prop]
    constructor
    · intro hv
      exact ⟨f v, hsub v hv, hv, rfl⟩
    · rintro ⟨r, -, hv, -⟩
      exact hv
  conv_lhs => rw [hset]
  refine measure_biUnion_finset ?_ fun r _ => hE.inter (hf (measurableSet_singleton r))
  intro r _ s _ hrs
  exact Set.disjoint_left.2 fun v h1 h2 => hrs (h1.2.symm.trans h2.2)

/-- **Reset at the pivot `i`, one rank.**  On `{ρ i = r}` the active event is a past event
    and the success event is the anchored success event at `(v r, resc r v)`. -/
theorem ofReal_mul_orderLaw_trialActive_inter_le (hQ : Measurable Q) {L 𝔥 gap₀ : ℕ}
    (h𝔥 : 𝔥 ≤ N) {p : ℝ}
    (hS : ∀ r < 𝔥, ∀ m, r + 1 + m = N → ∀ u : ℝ, AnchorGood N r u → 0 ≤ u →
      ENNReal.ofReal p ≤
        Renyi.orderLaw m {w | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q u w) L 1})
    (i : ℕ) {r : ℕ} (hr : r < 𝔥) :
    ENNReal.ofReal p *
        Renyi.orderLaw N (trialActive eps Q L 𝔥 N i ∩ {v | samplePivot eps Q L v i = r}) ≤
      Renyi.orderLaw N (trialSuccess eps Q L 𝔥 gap₀ N i ∩ {v | samplePivot eps Q L v i = r}) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = r + 1 + m := ⟨N - (r + 1), by omega⟩
  obtain ⟨C₀, hC₀, hC₀eq⟩ := Renyi.exists_preimage_pre_of_measurableSet_coordSigma
    (measurableSet_layerPivot_samplePairs_eq (eps := eps) hQ L i r)
  set C : Set (Fin (r + 1) → ℝ) :=
    C₀ ∩ {x | AnchorGood (r + 1 + m) r (x (Fin.last r))} with hCdef
  have hC : MeasurableSet C :=
    hC₀.inter ((measurableSet_anchorGood _ r).preimage (measurable_pi_apply (Fin.last r)))
  set F : Set (ℝ × (Fin m → ℝ)) :=
    {q | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q q.1 q.2) L 1} with hFdef
  have hF : MeasurableSet F :=
    measurable_anchPairsW_uncurry hQ (measurableSet_le_layerPivot eps _ L 1)
  have hext : ∀ v : Fin (r + 1 + m) → ℝ, extendKeys v r = Renyi.pivot r v := fun v =>
    extendKeys_of_lt v (by omega)
  have hmemC : ∀ v : Fin (r + 1 + m) → ℝ, v ∈ Renyi.pre r ⁻¹' C ↔
      samplePivot eps Q L v i = r ∧ AnchorGood (r + 1 + m) r (Renyi.pivot r v) := by
    intro v
    have h1 : v ∈ Renyi.pre r ⁻¹' C₀ ↔ samplePivot eps Q L v i = r := by
      rw [hC₀eq]
      rfl
    simp only [hCdef, Set.preimage_inter, Set.mem_inter_iff, h1]
    rfl
  have hA : trialActive eps Q L 𝔥 (r + 1 + m) i ∩ {v | samplePivot eps Q L v i = r} =
      Renyi.pre r ⁻¹' C := by
    ext v
    rw [hmemC]
    simp only [trialActive, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨-, hg⟩, hv⟩
      rw [hv, hext] at hg
      exact ⟨hv, hg⟩
    · rintro ⟨hv, hg⟩
      rw [hv, hext]
      exact ⟨⟨hr, hg⟩, rfl⟩
  have hY : trialSuccess eps Q L 𝔥 gap₀ (r + 1 + m) i ∩ {v | samplePivot eps Q L v i = r} =
      Renyi.pre r ⁻¹' C ∩ {v | (Renyi.pivot r v, Renyi.resc r v) ∈ F} := by
    ext v
    have hA' := congrArg (v ∈ ·) hA
    simp only [eq_iff_iff] at hA'
    simp only [trialSuccess, Set.mem_inter_iff, Set.mem_ofPred_eq, hFdef]
    constructor
    · rintro ⟨⟨hact, hgap⟩, hv⟩
      have hvC := hA'.1 ⟨hact, hv⟩
      obtain ⟨-, hg⟩ := (hmemC v).1 hvC
      refine ⟨hvC, ?_⟩
      have e := layerPivot_samplePairs_succ_sub eps Q (hg.lt_one (by omega)).ne hv
      have hv' : layerPivot eps (samplePairs Q v) L i = r := hv
      simp only [samplePivot] at hgap
      rw [← e]
      rw [hv'] at hgap ⊢
      exact hgap
    · rintro ⟨hvC, hgap⟩
      obtain ⟨hv, hg⟩ := (hmemC v).1 hvC
      obtain ⟨hact, -⟩ := hA'.2 hvC
      refine ⟨⟨hact, ?_⟩, hv⟩
      have e := layerPivot_samplePairs_succ_sub eps Q (hg.lt_one (by omega)).ne hv
      have hv' : layerPivot eps (samplePairs Q v) L i = r := hv
      simp only [samplePivot]
      rw [e, hv']
      exact hgap
  rw [hA, hY]
  exact mul_orderLaw_pre_le hC hF fun x hx h0 => hS r hr m rfl _ hx.2 h0

/-- **Reset at the pivot `i`.**  `p · P(trial i active) ≤ P(trial i succeeds)`. -/
theorem ofReal_mul_orderLaw_trialActive_le (hQ : Measurable Q) {L 𝔥 gap₀ : ℕ}
    (h𝔥 : 𝔥 ≤ N) {p : ℝ}
    (hS : ∀ r < 𝔥, ∀ m, r + 1 + m = N → ∀ u : ℝ, AnchorGood N r u → 0 ≤ u →
      ENNReal.ofReal p ≤
        Renyi.orderLaw m {w | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q u w) L 1})
    (i : ℕ) :
    ENNReal.ofReal p * Renyi.orderLaw N (trialActive eps Q L 𝔥 N i) ≤
      Renyi.orderLaw N (trialSuccess eps Q L 𝔥 gap₀ N i) := by
  have hf := measurable_samplePivot (N := N) hQ eps L i
  rw [measure_eq_sum_inter_eq _ (measurableSet_trialActive hQ eps L 𝔥 i) hf
      (𝔥 := 𝔥) fun v hv => hv.1,
    measure_eq_sum_inter_eq _ (measurableSet_trialSuccess hQ eps L 𝔥 gap₀ i) hf
      (𝔥 := 𝔥) fun v hv => hv.1.1, mul_sum]
  exact sum_le_sum fun r hr =>
    ofReal_mul_orderLaw_trialActive_inter_le hQ h𝔥 hS i (mem_range.1 hr)

end TrialReset

/-! ## Layer size -/

section Layer

open Classical

variable {N : ℕ} {Q : ℝ → ℝ} {eps : ℝ}

/-- **Layer size.**  Layer `L` of ALG-PGM on the keys `Q ∘ v` has as many keys as there are
    layer-`L` sample pivots below `N`. -/
theorem epLayer_snd_eq_card_samplePivot (heps : 0 ≤ eps) (Q : ℝ → ℝ) (v : Fin N → ℝ)
    (L : ℕ) :
    (epLayer eps (extendKeys (Q ∘ v)) N L).2 = #{j ∈ range N | samplePivot eps Q L v j < N} := by
  have hkeys : ∀ t < N, extendKeys (Q ∘ v) t =
      extendKeys (Q ∘ v) 0 + pairKeys (samplePairs Q v) t := by
    intro t ht
    rw [pairKeys_samplePairs Q v t ht, extendKeys_of_lt _ ht,
      extendKeys_of_lt _ (by omega : 0 < N)]
    simp
  rw [(epLayer_congr hkeys L).1]
  exact epLayer_snd_eq_card_layerPivot heps (samplePairs_snd Q v)
    (allLayersFinite_samplePairs eps Q v) _ N L

/-- **Layer size, pointwise bound.**  The layer-`L` size is at most the number of active
    trials, plus `N / q^L + 1` off the good-anchor event, plus the pivots in `[𝔥, N)`. -/
theorem epLayer_snd_le_sum_trialActive (heps : 0 ≤ eps) (Q : ℝ → ℝ) {L 𝔥 D : ℕ}
    (h𝔥 : 𝔥 ≤ N) (hD : D ≤ N - 𝔥) (v : Fin N → ℝ) :
    ((epLayer eps (extendKeys (Q ∘ v)) N L).2 : ℝ) ≤
      ∑ i ∈ range N, (trialActive eps Q L 𝔥 N i).indicator 1 v +
        ((N : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1) * (goodAnchors N D)ᶜ.indicator 1 v +
        (((N : ℝ) - 𝔥) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1) := by
  have hz := samplePairs_snd Q v
  have hfin := allLayersFinite_samplePairs eps Q v
  have hq : (0 : ℝ) < (⌊2 * eps⌋₊ + 1 : ℝ) ^ L := by positivity
  have hcast : ∀ a : ℕ, ((a / (⌊2 * eps⌋₊ + 1) ^ L : ℕ) : ℝ) ≤
      (a : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L := by
    intro a
    have := Nat.cast_div_le (α := ℝ) (m := a) (n := (⌊2 * eps⌋₊ + 1) ^ L)
    push_cast at this
    exact this
  rw [epLayer_snd_eq_card_samplePivot heps Q v L]
  -- split the pivots below `N` at the horizon
  have hsplit : #{j ∈ range N | samplePivot eps Q L v j < N} ≤
      #{j ∈ range N | samplePivot eps Q L v j < 𝔥} +
        #{j ∈ range N | 𝔥 ≤ samplePivot eps Q L v j ∧ samplePivot eps Q L v j < N} := by
    refine (card_le_card fun j hj => ?_).trans (card_union_le _ _)
    simp only [mem_filter, mem_union] at hj ⊢
    by_cases h : samplePivot eps Q L v j < 𝔥
    · exact Or.inl ⟨hj.1, h⟩
    · exact Or.inr ⟨hj.1, not_lt.1 h, hj.2⟩
  have htail := card_layerPivot_le heps hz hfin L 𝔥 N (range N)
  have htail' : ((#{j ∈ range N | 𝔥 ≤ samplePivot eps Q L v j ∧
      samplePivot eps Q L v j < N} : ℕ) : ℝ) ≤ ((N : ℝ) - 𝔥) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1 := by
    have h1 : ((#{j ∈ range N | 𝔥 ≤ samplePivot eps Q L v j ∧
        samplePivot eps Q L v j < N} : ℕ) : ℝ) ≤
        (((N - 𝔥) / (⌊2 * eps⌋₊ + 1) ^ L + 1 : ℕ) : ℝ) := by exact_mod_cast htail
    have h2 := hcast (N - 𝔥)
    rw [Nat.cast_sub h𝔥] at h2
    push_cast at h1
    linarith
  have hsum : ∑ i ∈ range N, (trialActive eps Q L 𝔥 N i).indicator 1 v =
      ((#{i ∈ range N | v ∈ trialActive eps Q L 𝔥 N i} : ℕ) : ℝ) := by
    rw [← sum_boole]
    refine sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, Pi.one_apply]
  rw [hsum]
  have hsplit' : ((#{j ∈ range N | samplePivot eps Q L v j < N} : ℕ) : ℝ) ≤
      ((#{j ∈ range N | samplePivot eps Q L v j < 𝔥} : ℕ) : ℝ) +
        ((#{j ∈ range N | 𝔥 ≤ samplePivot eps Q L v j ∧ samplePivot eps Q L v j < N} : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  by_cases hv : v ∈ goodAnchors N D
  · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hv), mul_zero, add_zero]
    have hsub : #{j ∈ range N | samplePivot eps Q L v j < 𝔥} ≤
        #{i ∈ range N | v ∈ trialActive eps Q L 𝔥 N i} := by
      refine card_le_card fun j hj => ?_
      simp only [mem_filter] at hj ⊢
      refine ⟨hj.1, hj.2, ?_⟩
      have hjN : samplePivot eps Q L v j < N := by omega
      rw [extendKeys_of_lt v hjN]
      exact hv ⟨_, hjN⟩ (by simp only; omega)
    have hsub' : ((#{j ∈ range N | samplePivot eps Q L v j < 𝔥} : ℕ) : ℝ) ≤
        ((#{i ∈ range N | v ∈ trialActive eps Q L 𝔥 N i} : ℕ) : ℝ) := by exact_mod_cast hsub
    linarith
  · rw [Set.indicator_of_mem (Set.mem_compl hv), Pi.one_apply, mul_one]
    have hhead := card_layerPivot_le heps hz hfin L 0 𝔥 (range N)
    have hhead' : ((#{j ∈ range N | samplePivot eps Q L v j < 𝔥} : ℕ) : ℝ) ≤
        (N : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1 := by
      have hset : ({j ∈ range N | samplePivot eps Q L v j < 𝔥} : Finset ℕ) =
          {j ∈ range N | 0 ≤ layerPivot eps (samplePairs Q v) L j ∧
            layerPivot eps (samplePairs Q v) L j < 𝔥} := by
        ext j
        simp
      have h1 : ((#{j ∈ range N | samplePivot eps Q L v j < 𝔥} : ℕ) : ℝ) ≤
          (((𝔥 - 0) / (⌊2 * eps⌋₊ + 1) ^ L + 1 : ℕ) : ℝ) := by
        rw [hset]
        exact_mod_cast hhead
      have h2 := hcast 𝔥
      have h3 : (𝔥 : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L ≤ (N : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L :=
        div_le_div_of_nonneg_right (by exact_mod_cast h𝔥) hq.le
      rw [Nat.sub_zero] at h1
      push_cast at h1
      linarith
    have h0 : (0 : ℝ) ≤ ((#{i ∈ range N | v ∈ trialActive eps Q L 𝔥 N i} : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith

end Layer

/-! ## The expected layer size before the horizon -/

section Main

open Classical

theorem measurableSet_goodAnchors (N D : ℕ) : MeasurableSet (goodAnchors N D) := by
  have hset : goodAnchors N D =
      ⋂ r : Fin N, {v : Fin N → ℝ | D ≤ N - (r : ℕ) → AnchorGood N r (v r)} := by
    ext v
    simp only [goodAnchors, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [hset]
  refine MeasurableSet.iInter fun r => ?_
  by_cases h : D ≤ N - (r : ℕ)
  · simp only [h, true_implies]
    exact (measurableSet_anchorGood N r).preimage (measurable_pi_apply r)
  · simp only [h, false_implies, Set.ofPred_true, MeasurableSet.univ]

variable {N : ℕ} {Q : ℝ → ℝ} {eps : ℝ}

/-- **Counting successes.**  At most `𝔥 / gap₀ + 2` of the trials `i < N` succeed. -/
theorem sum_indicator_trialSuccess_le (heps : 0 ≤ eps) (Q : ℝ → ℝ) {L 𝔥 gap₀ : ℕ}
    (hgap : 1 ≤ gap₀) (v : Fin N → ℝ) :
    ∑ i ∈ range N, (trialSuccess eps Q L 𝔥 gap₀ N i).indicator 1 v ≤ (𝔥 : ℝ) / gap₀ + 2 := by
  have hsum : ∑ i ∈ range N, (trialSuccess eps Q L 𝔥 gap₀ N i).indicator 1 v =
      ((#{i ∈ range N | v ∈ trialSuccess eps Q L 𝔥 gap₀ N i} : ℕ) : ℝ) := by
    rw [← sum_boole]
    refine sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, Pi.one_apply]
  rw [hsum]
  have hmono := layerPivot_strictMono heps (samplePairs_snd Q v)
    (allLayersFinite_samplePairs eps Q v) L
  have h1 : #{i ∈ range N | v ∈ trialSuccess eps Q L 𝔥 gap₀ N i} ≤ 𝔥 / gap₀ + 1 := by
    refine (card_le_card fun i hi => ?_).trans (card_trial_success_le hmono hgap (range N))
    simp only [mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1.1, hi.2.2⟩
  have h2 : ((#{i ∈ range N | v ∈ trialSuccess eps Q L 𝔥 gap₀ N i} : ℕ) : ℝ) ≤
      ((𝔥 / gap₀ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : ((𝔥 / gap₀ : ℕ) : ℝ) ≤ (𝔥 : ℝ) / gap₀ := Nat.cast_div_le
  push_cast at h2
  linarith

/-- **Expected layer-`L` size before a deterministic horizon.**  Let the layer-`L` pivots of
    the sample keys `Q ∘ v`, `v ∼ orderLaw N`, be `ρ i`.  Suppose that at every rank `r < 𝔥`
    and every nonnegative anchor value `u` in the window of `goodAnchors`, the anchored pairs
    with `N - 1 - r` fresh sorted uniforms have leading layer-`L` pivot at least
    `min gap₀ (𝔥 - r)` with probability at least `p`.  Then the expected size of layer `L`
    is at most `(𝔥 / gap₀ + 2) / p + (N / q^L + 1) · P(goodAnchorsᶜ) + (N - 𝔥) / q^L + 1`,
    `q = ⌊2 eps⌋₊ + 1`. -/
theorem integral_epLayer_snd_le (hQ : Measurable Q) (heps : 0 ≤ eps) {L 𝔥 gap₀ D : ℕ}
    (h𝔥 : 𝔥 ≤ N) (hgap : 1 ≤ gap₀) (hD : D ≤ N - 𝔥) {p : ℝ} (hp : 0 < p)
    (hS : ∀ r < 𝔥, ∀ m, r + 1 + m = N → ∀ u : ℝ,
      ((N - r : ℕ) : ℝ) / (2 * N) ≤ 1 - u → 1 - u ≤ 2 * ((N - r : ℕ) : ℝ) / N →
      0 ≤ u → ENNReal.ofReal p ≤
        Renyi.orderLaw m {w | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q u w) L 1}) :
    ∫ v, ((epLayer eps (extendKeys (Q ∘ v)) N L).2 : ℝ) ∂(Renyi.orderLaw N) ≤
      ((𝔥 : ℝ) / gap₀ + 2) / p +
        ((N : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1) * (Renyi.orderLaw N (goodAnchors N D)ᶜ).toReal +
        ((N : ℝ) - 𝔥) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1 := by
  set μ := Renyi.orderLaw N
  have hS' : ∀ r < 𝔥, ∀ m, r + 1 + m = N → ∀ u : ℝ, AnchorGood N r u → 0 ≤ u →
      ENNReal.ofReal p ≤
        Renyi.orderLaw m {w | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q u w) L 1} :=
    fun r hr m hm u hu => hS r hr m hm u hu.1 hu.2
  have hA := measurableSet_trialActive (N := N) hQ eps L 𝔥
  have hY := measurableSet_trialSuccess (N := N) hQ eps L 𝔥 gap₀
  have hB : MeasurableSet (goodAnchors N D)ᶜ := (measurableSet_goodAnchors N D).compl
  -- reset at each pivot
  have hstep : ∀ i, p * μ.real (trialActive eps Q L 𝔥 N i) ≤
      μ.real (trialSuccess eps Q L 𝔥 gap₀ N i) := by
    intro i
    have h := ENNReal.toReal_mono (measure_ne_top _ _)
      (ofReal_mul_orderLaw_trialActive_le hQ h𝔥 hS' i)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le] at h
  -- the expected number of successes
  have hsumY : ∑ i ∈ range N, μ.real (trialSuccess eps Q L 𝔥 gap₀ N i) ≤ (𝔥 : ℝ) / gap₀ + 2 := by
    have hint : ∀ i ∈ range N,
        Integrable (fun v => (trialSuccess eps Q L 𝔥 gap₀ N i).indicator 1 v) μ :=
      fun i _ => (integrable_const (1 : ℝ)).indicator (hY i)
    calc ∑ i ∈ range N, μ.real (trialSuccess eps Q L 𝔥 gap₀ N i)
        = ∫ v, ∑ i ∈ range N, (trialSuccess eps Q L 𝔥 gap₀ N i).indicator 1 v ∂μ := by
          rw [integral_finsetSum _ hint]
          exact sum_congr rfl fun i _ => (integral_indicator_one (hY i)).symm
      _ ≤ ∫ _v, ((𝔥 : ℝ) / gap₀ + 2) ∂μ :=
          integral_mono (integrable_finsetSum _ hint) (integrable_const _)
            fun v => sum_indicator_trialSuccess_le heps Q hgap v
      _ = (𝔥 : ℝ) / gap₀ + 2 := by simp
  have hsumA : ∑ i ∈ range N, μ.real (trialActive eps Q L 𝔥 N i) ≤ ((𝔥 : ℝ) / gap₀ + 2) / p := by
    rw [le_div_iff₀ hp, sum_mul]
    refine le_trans (sum_le_sum fun i _ => ?_) hsumY
    rw [mul_comm]
    exact hstep i
  -- integrate the pointwise layer bound
  set c₁ : ℝ := (N : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1
  set c₂ : ℝ := ((N : ℝ) - 𝔥) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1
  have hintA : ∀ i ∈ range N,
      Integrable (fun v => (trialActive eps Q L 𝔥 N i).indicator 1 v) μ :=
    fun i _ => (integrable_const (1 : ℝ)).indicator (hA i)
  have hintB : Integrable (fun v => c₁ * (goodAnchors N D)ᶜ.indicator 1 v) μ :=
    ((integrable_const (1 : ℝ)).indicator hB).const_mul c₁
  have hsA : Integrable (fun v => ∑ i ∈ range N, (trialActive eps Q L 𝔥 N i).indicator 1 v) μ :=
    integrable_finsetSum _ hintA
  have hAB : Integrable (fun v => ∑ i ∈ range N, (trialActive eps Q L 𝔥 N i).indicator 1 v +
      c₁ * (goodAnchors N D)ᶜ.indicator 1 v) μ := hsA.add hintB
  have hg : Integrable (fun v => ∑ i ∈ range N, (trialActive eps Q L 𝔥 N i).indicator 1 v +
      c₁ * (goodAnchors N D)ᶜ.indicator 1 v + c₂) μ := hAB.add (integrable_const _)
  have hle := integral_mono_of_nonneg (ae_of_all _ fun v => Nat.cast_nonneg _) hg
    (ae_of_all _ fun v => epLayer_snd_le_sum_trialActive heps Q (L := L) h𝔥 hD v)
  have hval : ∫ v, (∑ i ∈ range N, (trialActive eps Q L 𝔥 N i).indicator 1 v +
      c₁ * (goodAnchors N D)ᶜ.indicator 1 v + c₂) ∂μ =
      ∑ i ∈ range N, μ.real (trialActive eps Q L 𝔥 N i) + c₁ * μ.real (goodAnchors N D)ᶜ + c₂ := by
    rw [integral_add hAB (integrable_const _), integral_add hsA hintB, integral_finsetSum _ hintA,
      integral_const_mul, integral_indicator_one hB, integral_const]
    simp only [probReal_univ, one_smul]
    congr 2
    exact sum_congr rfl fun i _ => integral_indicator_one (hA i)
  rw [hval] at hle
  have hreal : μ.real (goodAnchors N D)ᶜ = (Renyi.orderLaw N (goodAnchors N D)ᶜ).toReal := rfl
  rw [← hreal]
  linarith

end Main

end

end PGM
