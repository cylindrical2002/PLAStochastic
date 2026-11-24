import PLAStochastic.Index.GEP.OrbitClosure.Defs
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers
import PLAStochastic.Index.LocalCount.CyclicEarlyMark
import PLAStochastic.Index.OneLayer.ThresholdMargin

/-!
# WP2: cyclic reduction, deterministic inclusions and factorisation on iid gaps

Tools for the joint stopping bound of `PLAStochastic/Index/GEP/OrbitClosure/JointStop.lean`, on the canonical space
`iidLaw ρ` (coordinates iid by `iidSeq_gapCoord`).

* Sums: `map_sum_finset_eq_convPow` (the law of a sum over a finite index set of size `n`
  is `convPow ρ n`; induction with `IndepFun.map_add_eq_map_conv_map₀`),
  `map_gapKeys_eq_convPow`, `map_shift_iidLaw`, `measure_block_shift`.
* Cyclic reduction (`density-tail.md` (4.1), `research/2026-09-25-kep-proof/tex/main.tex`
  `prop:transfer`, "Cyclic reduction"): `stopMeas_le_cyclic`,
  `P(T = t, S_t ∈ A) ≤ (2/t) P(E ∩ {S_t ∈ A})` for every event `E` containing
  `{𝒦_t ≥ 1}` on positive paths.  Same proof as `marked_cyclic_identity` and
  `marked_cyclic_two` of `PLAStochastic/Index/LocalCount/CyclicTwo.lean`, with the rotation-invariant real mark
  `{S_t ∈ A}` in place of `{S_t^Q = k}`.
* `stopMeas_eq_zero`: `T > 2 eps` (`floor_two_eps_lt_pairSegLen`).
* Deterministic inclusions of `{𝒦_t ≥ 1}`:
  - `cyclicCount_pos_walk` (early stop): one half of the walk has
    `max |S_j - j| > eps/6` (`cyclicCount_eq_zero_of_walk_le`, `gapWalk_le_of_halves`);
  - `cyclicCount_pos_block` (long window, `density-tail.md` (4.3), the deterministic step of
    pla-local `thm:local(d)` L260–273): with `m = ⌊t/8⌋`, one of the `16` blocks
    `[jm, (j+1)m] ⊆ [0, t]` is feasible, i.e. `m < T(shift_{jm} g)`.  A stopping rotation
    `ρ_r` has its first `t` keys feasible (`stopsAt_rot_iff`); for `r > 0` its keys contain
    translates of the windows `[r, t]` and `[0, r-1]` (`vkeys_rot`, `pkeys_add_period`),
    for `r = 0` the window `[0, t-1]`; one of them has at least `⌈(t-1)/2⌉` gaps and
    contains the block `j = ⌈u/m⌉` (`prefixAffineFeasible_mono`,
    `prefixAffineFeasible_affine_iff`, `gapKeys_shift`).
* Measurability of prefix events: `exists_prefix_set_lt_gapSegLen` (`isStoppingRule_gapSegLen`),
  `exists_prefix_set_walk`.
* Factorisation (`prop:transfer`, "Two density bounds"; `density-tail.md` (4.4)–(4.5)):
  - `measure_block_inter_le`: an event of the block `[u, u+m)` meets `{S_t ∈ A}` with
    probability at most its own probability times `c |A|`, when the remaining `t - m` gaps
    have `LocBd c` (`measure_pair_le_lintegral`, `IIDSeq.indepFun_of_disjoint`);
  - `measure_gapKeys_le_spatial`: `P(S_{r+s} ∈ A) ≤ ∫_A (c_s p_r(x) + c_r p_s(x)) dx` with
    `p_n(x) = P(|x - (r+s)|/2 ≤ |S_n - n|)`, because every decomposition `x = y + z` has
    `|y - r| ≥ |x - (r+s)|/2` or `|z - s| ≥ |x - (r+s)|/2` (Tonelli on the product law).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

/-! ## Keys of finite vectors -/

theorem measurable_vkeys_apply (s j : ℕ) : Measurable fun v : Fin s → ℝ => vkeys v j := by
  simp only [vkeys, gapKeys]
  refine Finset.measurable_sum _ fun q _ => ?_
  by_cases hq : q < s
  · simp only [vext, hq, dif_pos]
    exact measurable_pi_apply _
  · simp only [vext, hq, dif_neg, not_false_eq_true]
    exact measurable_const

theorem measurable_vkeys (s : ℕ) : Measurable fun v : Fin s → ℝ => vkeys v :=
  measurable_pi_lambda _ fun j => measurable_vkeys_apply s j

theorem measurableSet_stopsAt (eps : ℝ) (t : ℕ) :
    MeasurableSet {v : Fin t → ℝ | stopsAt eps v} :=
  (measurable_vkeys t (measurableSet_prefixAffineFeasible eps t)).inter
    (measurable_vkeys t (measurableSet_prefixAffineFeasible eps (t + 1))).compl

/-! ## Laws of sums -/

/-- The law of a sum over a finite index set of iid `ρ` gaps is `convPow ρ S.card`. -/
theorem map_sum_finset_eq_convPow (ρ : ProbabilityMeasure ℝ) (S : Finset ℕ) :
    (iidLaw ρ).map (fun g => ∑ i ∈ S, g i) = convPow (ρ : Measure ℝ) S.card := by
  classical
  have hX := iidSeq_gapCoord ρ
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.card_empty, convPow_zero]
    rw [Measure.map_const, measure_univ, one_smul]
  | insert a S ha ih =>
    rw [Finset.card_insert_of_notMem ha, convPow_succ, ← ih]
    have hS : (∑ j ∈ S, gapCoord j) = fun g : ℕ → ℝ => ∑ i ∈ S, g i := by
      funext g
      simp only [Finset.sum_apply, gapCoord]
    have hind : IndepFun (fun g : ℕ → ℝ => ∑ i ∈ S, g i) (gapCoord a) (iidLaw ρ) := by
      rw [← hS]
      exact hX.indep.indepFun_finsetSum_of_notMem hX.measurable ha
    have hsum : (fun g : ℕ → ℝ => ∑ i ∈ insert a S, g i) =
        (fun g : ℕ → ℝ => ∑ i ∈ S, g i) + gapCoord a := by
      funext g
      simp only [Finset.sum_insert ha, Pi.add_apply, gapCoord]
      ring
    rw [hsum, hind.map_add_eq_map_conv_map₀ (Finset.measurable_sum _ fun j _ =>
      measurable_pi_apply j).aemeasurable (hX.measurable a).aemeasurable]
    congr 1
    exact Measure.infinitePi_map_eval _ a

theorem map_gapKeys_eq_convPow (ρ : ProbabilityMeasure ℝ) (n : ℕ) :
    (iidLaw ρ).map (fun g => gapKeys g n) = convPow (ρ : Measure ℝ) n := by
  have h := map_sum_finset_eq_convPow ρ (Finset.range n)
  rw [Finset.card_range] at h
  exact h

/-- Shifting the canonical iid sequence preserves its law. -/
theorem map_shift_iidLaw (ρ : ProbabilityMeasure ℝ) (u : ℕ) :
    (iidLaw ρ).map (fun g i => g (u + i)) = iidLaw ρ :=
  map_seq_eq_iidLaw ((iidSeq_gapCoord ρ).shift u) ρ
    (Measure.infinitePi_map_eval (fun _ : ℕ => (ρ : Measure ℝ)) (u + 0)).symm

/-- A block event has the probability of the same event on the first block. -/
theorem measure_block_shift (ρ : ProbabilityMeasure ℝ) (u m : ℕ) {E' : Set (Fin m → ℝ)}
    (hE' : MeasurableSet E') :
    iidLaw ρ {g | (fun i : Fin m => g (u + i)) ∈ E'} =
      iidLaw ρ {g | (fun i : Fin m => g i) ∈ E'} := by
  have hsh : Measurable fun (g : ℕ → ℝ) (i : ℕ) => g (u + i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hB : MeasurableSet {g : ℕ → ℝ | (fun i : Fin m => g i) ∈ E'} :=
    (measurable_pi_lambda _ fun i => measurable_pi_apply _) hE'
  calc iidLaw ρ {g | (fun i : Fin m => g (u + i)) ∈ E'} =
        iidLaw ρ ((fun (g : ℕ → ℝ) (i : ℕ) => g (u + i)) ⁻¹'
          {g : ℕ → ℝ | (fun i : Fin m => g i) ∈ E'}) := rfl
    _ = ((iidLaw ρ).map fun (g : ℕ → ℝ) (i : ℕ) => g (u + i))
          {g : ℕ → ℝ | (fun i : Fin m => g i) ∈ E'} := (Measure.map_apply hsh hB).symm
    _ = _ := by rw [map_shift_iidLaw]

/-! ## Prefix events -/

/-- `{m < T}` depends only on the first `m` gaps. -/
theorem exists_prefix_set_lt_gapSegLen (eps : ℝ) (m : ℕ) :
    ∃ E' : Set (Fin m → ℝ), MeasurableSet E' ∧
      ∀ g : ℕ → ℝ, ((m : ℕ∞) < gapSegLen eps g ↔ (fun i : Fin m => g i) ∈ E') := by
  obtain ⟨S, hS, hSeq⟩ := isStoppingRule_gapSegLen eps m
  refine ⟨S, hS, fun g => ?_⟩
  change g ∈ {z : ℕ → ℝ | (m : ℕ∞) < gapSegLen eps z} ↔ _
  rw [← hSeq]
  rfl

/-- `{max_{j ≤ s} |S_j - j| > x}` depends only on the first `s` gaps. -/
theorem exists_prefix_set_walk (x : ℝ) (s : ℕ) :
    ∃ E' : Set (Fin s → ℝ), MeasurableSet E' ∧
      ∀ g : ℕ → ℝ, ((∃ j ≤ s, x < |gapKeys g j - j|) ↔ (fun i : Fin s => g i) ∈ E') := by
  refine ⟨{v : Fin s → ℝ | ∃ j ≤ s, x < |vkeys v j - j|}, ?_, fun g => ?_⟩
  · have : {v : Fin s → ℝ | ∃ j ≤ s, x < |vkeys v j - j|} =
        ⋃ j : ℕ, ⋃ (_ : j ≤ s), {v : Fin s → ℝ | x < |vkeys v j - j|} := by
      ext v
      simp
    rw [this]
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const
        (continuous_abs.measurable.comp ((measurable_vkeys_apply s j).sub_const _))
  · simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by rwa [vkeys_eq_gapKeys g hj]⟩
    · rintro ⟨j, hj, hx⟩
      exact ⟨j, hj, by rwa [← vkeys_eq_gapKeys g hj]⟩

/-! ## Cyclic reduction -/

/-- The law of the first `t` gaps is invariant under every cyclic rotation. -/
theorem map_rot_iidLaw (ρ : ProbabilityMeasure ℝ) {t : ℕ} (r : Fin t) :
    (iidLaw ρ).map (fun g (i : Fin t) => g ((i + r : Fin t) : ℕ)) =
      (iidLaw ρ).map (fun g (i : Fin t) => g (i : ℕ)) := by
  have hX := iidSeq_gapCoord ρ
  have hmarg : ∀ n, (iidLaw ρ).map (gapCoord n) = (ρ : Measure ℝ) := fun n =>
    Measure.infinitePi_map_eval _ n
  have e1 := (hX.indep.precomp (g := fun i : Fin t => ((i + r : Fin t) : ℕ))
    (fun a b hab => add_right_cancel (Fin.val_injective hab))).map_fun_eq_pi_map
    (fun i => (hX.measurable _).aemeasurable)
  have e2 := (hX.indep.precomp (g := fun i : Fin t => (i : ℕ)) Fin.val_injective).map_fun_eq_pi_map
    (fun i => (hX.measurable _).aemeasurable)
  simp only [hmarg] at e1 e2
  exact e1.trans e2.symm

/-- A stop at `t ≤ 2 eps` is impossible. -/
theorem stopMeas_eq_zero {eps : ℝ} (heps : 0 ≤ eps) (ρ : ProbabilityMeasure ℝ) {t : ℕ}
    (ht : (t : ℝ) ≤ 2 * eps) : stopMeas eps ρ t = 0 := by
  have hempty : {g : ℕ → ℝ | gapSegLen eps g = (t : ℕ∞)} = ∅ := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hT
    set C := ConstantLineLengthCertificate.of_nonneg heps
    have h := constantLine_le_segLen C (gapKeys g)
    rw [← gapSegLen, hT] at h
    have hq : C.q ≤ t := by exact_mod_cast h
    have hq' : (C.q : ℝ) ≤ t := by exact_mod_cast hq
    linarith [C.lower]
  rw [stopMeas, hempty, Measure.restrict_empty, Measure.map_zero]

/-- **Cyclic reduction with a real mark**: `P(T = t, S_t ∈ A) ≤ (2/t) P(E ∩ {S_t ∈ A})` for
every measurable `E` containing `{𝒦_t ≥ 1}` on positive paths. -/
theorem stopMeas_le_cyclic {ρ : ProbabilityMeasure ℝ} (hpos : (ρ : Measure ℝ) (Iic 0) = 0)
    {eps : ℝ} (heps : 0 ≤ eps) {t : ℕ} (ht : 0 < t) {E : Set (ℕ → ℝ)} (hE : MeasurableSet E)
    (hsub : ∀ g : ℕ → ℝ, (∀ i, 0 < g i) → 1 ≤ cyclicCount eps (fun i : Fin t => g i) → g ∈ E)
    {A : Set ℝ} (hA : MeasurableSet A) :
    stopMeas eps ρ t A ≤ 2 / (t : ℝ≥0∞) * iidLaw ρ (E ∩ {g | gapKeys g t ∈ A}) := by
  classical
  have : NeZero t := ⟨ht.ne'⟩
  have hS : Measurable fun g : ℕ → ℝ => gapKeys g t :=
    (measurable_pi_apply t).comp measurable_gapKeys
  have hSA : MeasurableSet {g : ℕ → ℝ | gapKeys g t ∈ A} := hS hA
  have hstop : stopMeas eps ρ t A =
      iidLaw ρ {g | stopsAt eps (fun i : Fin t => g i) ∧ gapKeys g t ∈ A} := by
    rw [stopMeas, Measure.map_apply hS hA, Measure.restrict_apply (hS hA)]
    congr 1
    ext g
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, stopsAt_iff_segLen]
    rw [gapSegLen]
    tauto
  -- the rotated events
  set Ev : Set (Fin t → ℝ) := {v | stopsAt eps v ∧ ∑ i, v i ∈ A} with hEv
  have hEvm : MeasurableSet Ev :=
    (measurableSet_stopsAt eps t).inter ((Finset.measurable_sum _ fun i _ =>
      measurable_pi_apply i) hA)
  set R : Fin t → (ℕ → ℝ) → Fin t → ℝ := fun r g i => g ((i + r : Fin t) : ℕ) with hR
  have hRm : ∀ r, Measurable (R r) := fun r => measurable_pi_lambda _ fun i =>
    measurable_pi_apply _
  have hAm : ∀ r, MeasurableSet (R r ⁻¹' Ev) := fun r => hRm r hEvm
  have hsumrot : ∀ (g : ℕ → ℝ) (r : Fin t), ∑ i : Fin t, R r g i = gapKeys g t := by
    intro g r
    rw [gapKeys, ← Fin.sum_univ_eq_sum_range (fun i => g i) t]
    exact Equiv.sum_comp (Equiv.addRight r) (fun i : Fin t => g i)
  have hmem : ∀ (g : ℕ → ℝ) (r : Fin t), g ∈ R r ⁻¹' Ev ↔
      stopsAt eps (rot (fun i : Fin t => g i) r) ∧ gapKeys g t ∈ A := by
    intro g r
    simp only [Set.mem_preimage, hEv, Set.mem_ofPred_eq, hsumrot]
    rfl
  have hPA : ∀ r, iidLaw ρ (R r ⁻¹' Ev) = iidLaw ρ (R 0 ⁻¹' Ev) := by
    intro r
    rw [← Measure.map_apply (hRm r) hEvm, ← Measure.map_apply (hRm 0) hEvm,
      map_rot_iidLaw ρ r, map_rot_iidLaw ρ 0]
  have hA0 : R 0 ⁻¹' Ev = {g | stopsAt eps (fun i : Fin t => g i) ∧ gapKeys g t ∈ A} := by
    ext g
    rw [hmem]
    have hrot0 : rot (fun i : Fin t => g i) 0 = fun i : Fin t => g i :=
      funext fun i => by simp only [rot, add_zero]
    rw [hrot0]
    rfl
  -- the count is a sum of rotated indicators
  have hpt : ∀ g, {g : ℕ → ℝ | gapKeys g t ∈ A}.indicator
      (fun g => (cyclicCount eps (fun i : Fin t => g i) : ℝ≥0∞)) g =
        ∑ r : Fin t, (R r ⁻¹' Ev).indicator 1 g := by
    intro g
    by_cases hk : gapKeys g t ∈ A
    · rw [Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | gapKeys g t ∈ A} from hk)]
      simp only [cyclicCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hr : stopsAt eps (rot (fun i : Fin t => g i) r)
      · rw [if_pos hr, Set.indicator_of_mem ((hmem g r).2 ⟨hr, hk⟩), Pi.one_apply]
      · rw [if_neg hr, Set.indicator_of_notMem fun h => hr ((hmem g r).1 h).1]
    · rw [Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | gapKeys g t ∈ A} from hk)]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      exact Set.indicator_of_notMem (fun h => hk ((hmem g r).1 h).2) _
  have hid : (t : ℝ≥0∞) * iidLaw ρ (R 0 ⁻¹' Ev) = ∫⁻ g, {g : ℕ → ℝ | gapKeys g t ∈ A}.indicator
      (fun g => (cyclicCount eps (fun i : Fin t => g i) : ℝ≥0∞)) g ∂(iidLaw ρ) := by
    simp_rw [hpt]
    rw [lintegral_finsetSum _ fun r _ => measurable_one.indicator (hAm r)]
    simp_rw [lintegral_indicator_one (hAm _), hPA]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- positivity and the cyclic-two bound
  have hae : ∀ᵐ g ∂(iidLaw ρ), ∀ i, 0 < g i := by
    refine ae_all_iff.2 fun i => ?_
    rw [ae_iff]
    have hset : {g : ℕ → ℝ | ¬ 0 < g i} = (fun g : ℕ → ℝ => g i) ⁻¹' Iic 0 := by
      ext g
      simp
    rw [hset, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iic, iidLaw,
      Measure.infinitePi_map_eval]
    exact hpos
  have hle : ∫⁻ g, {g : ℕ → ℝ | gapKeys g t ∈ A}.indicator
      (fun g => (cyclicCount eps (fun i : Fin t => g i) : ℝ≥0∞)) g ∂(iidLaw ρ) ≤
        ∫⁻ g, (E ∩ {g | gapKeys g t ∈ A}).indicator (fun _ => (2 : ℝ≥0∞)) g ∂(iidLaw ρ) := by
    refine lintegral_mono_ae (hae.mono fun g hg => ?_)
    by_cases hk : g ∈ {g : ℕ → ℝ | gapKeys g t ∈ A}
    · rw [Set.indicator_of_mem hk]
      by_cases hK : 1 ≤ cyclicCount eps (fun i : Fin t => g i)
      · rw [Set.indicator_of_mem (show g ∈ E ∩ {g | gapKeys g t ∈ A} from ⟨hsub g hg hK, hk⟩)]
        exact_mod_cast cyclicCount_le_two heps (fun i => hg i)
      · have h0 : cyclicCount eps (fun i : Fin t => g i) = 0 := by omega
        rw [h0, Nat.cast_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hk]
      exact zero_le
  rw [lintegral_indicator_const (hE.inter hSA)] at hle
  rw [hstop, ← hA0]
  calc iidLaw ρ (R 0 ⁻¹' Ev) = (t : ℝ≥0∞)⁻¹ * ((t : ℝ≥0∞) * iidLaw ρ (R 0 ⁻¹' Ev)) := by
        rw [ENNReal.inv_mul_cancel_left (by exact_mod_cast ht.ne') (ENNReal.natCast_ne_top t)]
    _ ≤ (t : ℝ≥0∞)⁻¹ * (2 * iidLaw ρ (E ∩ {g | gapKeys g t ∈ A})) := by
        rw [hid]
        gcongr
    _ = 2 / (t : ℝ≥0∞) * iidLaw ρ (E ∩ {g | gapKeys g t ∈ A}) := by
        rw [div_eq_mul_inv]
        ring

/-! ## Deterministic inclusions -/

/-- **Early stop**: a cyclic failure at `t` needs one half of the walk to move by more than
`eps/6`. -/
theorem cyclicCount_pos_walk {eps : ℝ} {t r : ℕ} (hr : r ≤ t) {g : ℕ → ℝ}
    (h : 1 ≤ cyclicCount eps (fun i : Fin t => g i)) :
    (∃ j ≤ r, eps / 6 < |gapKeys g j - j|) ∨
      (∃ j ≤ t - r, eps / 6 < |gapKeys (fun i => g (r + i)) j - j|) := by
  by_contra hne
  rw [not_or] at hne
  have h1 : ∀ j ≤ r, |gapKeys g j - j| ≤ eps / 6 := fun j hj =>
    not_lt.1 fun hlt => hne.1 ⟨j, hj, hlt⟩
  have h2 : ∀ j ≤ t - r, |gapKeys (fun i => g (r + i)) j - j| ≤ eps / 6 := fun j hj =>
    not_lt.1 fun hlt => hne.2 ⟨j, hj, hlt⟩
  have hx : 0 ≤ eps / 6 := by
    have := h1 0 (Nat.zero_le _)
    simp only [gapKeys_zero, Nat.cast_zero, sub_zero, abs_zero] at this
    exact this
  have hW : ∀ j ≤ t, |∑ i ∈ Finset.range j, (g i / 1 - 1)| ≤ eps / 3 := by
    intro j hj
    have hsum : ∑ i ∈ Finset.range j, (g i / 1 - 1) = gapKeys g j - j := by
      simp only [div_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, gapKeys]
    rw [hsum]
    rcases le_or_gt j r with hjr | hjr
    · linarith [h1 j hjr]
    · obtain ⟨j', rfl⟩ : ∃ j', j = r + j' := ⟨j - r, by omega⟩
      have e : gapKeys g (r + j') - ((r + j' : ℕ) : ℝ) =
          (gapKeys g r - r) + (gapKeys (fun i => g (r + i)) j' - j') := by
        rw [gapKeys_shift]
        push_cast
        ring
      rw [e]
      have a := h1 r le_rfl
      have b := h2 j' (by omega)
      calc |(gapKeys g r - r) + (gapKeys (fun i => g (r + i)) j' - j')|
          ≤ |gapKeys g r - r| + |gapKeys (fun i => g (r + i)) j' - j'| := abs_add_le _ _
        _ ≤ eps / 3 := by linarith
  have h0 := cyclicCount_eq_zero_of_walk_le (m := 1) g hW
  omega

/-- A feasible window of translated gap keys that contains the keys `b, …, b + m` makes the
first segment of the gaps from `b` longer than `m`. -/
theorem lt_gapSegLen_of_window {eps : ℝ} {g : ℕ → ℝ} {c : ℝ} {a L b m : ℕ}
    (hfeas : prefixAffineFeasible eps (fun i => gapKeys g (a + i) + c) L)
    (hab : a ≤ b) (hbL : b + m + 1 ≤ a + L) :
    (m : ℕ∞) < gapSegLen eps (fun i => g (b + i)) := by
  have hw := prefixAffineFeasible_window (r := b - a) (w := m + 1) hfeas (by omega)
  rw [gapSegLen, lt_segLen_iff]
  have e : gapKeys (fun i => g (b + i)) =
      fun i => 1 * (gapKeys g (a + (b - a + i)) + c) + (-c - gapKeys g b) := by
    funext i
    rw [gapKeys_shift, show a + (b - a + i) = b + i by omega]
    ring
  rw [e]
  exact (prefixAffineFeasible_affine_iff (p := fun i => gapKeys g (a + (b - a + i)) + c)
    one_ne_zero).2 hw

/-- A feasible window of at least `2 ⌊t/8⌋` keys inside `[0, t]` contains one of the blocks
`[j m, (j + 1) m]`, `m = ⌊t/8⌋`, `j < 16`: take `j = ⌈a/m⌉` for the window start `a`. -/
theorem exists_block_of_window {eps : ℝ} {g : ℕ → ℝ} {c : ℝ} {t a L : ℕ} (ht : 16 ≤ t)
    (hfeas : prefixAffineFeasible eps (fun i => gapKeys g (a + i) + c) L)
    (hL : 2 * (t / 8) ≤ L) (haL : a + L ≤ t + 1) :
    ∃ j < 16, (j + 1) * (t / 8) ≤ t ∧
      ((t / 8 : ℕ) : ℕ∞) < gapSegLen eps (fun i => g (j * (t / 8) + i)) := by
  set m := t / 8 with hm
  have hm2 : 2 ≤ m := by omega
  have ht8 : t < 8 * m + 8 := by omega
  obtain ⟨q, rem, hrem, hq⟩ : ∃ q rem, rem < m ∧ a + m - 1 = q * m + rem :=
    ⟨(a + m - 1) / m, (a + m - 1) % m, Nat.mod_lt _ (by omega),
      (Nat.div_add_mod' (a + m - 1) m).symm⟩
  have hq1 : a ≤ q * m := by omega
  have hq2 : q * m + 1 ≤ a + m := by omega
  have hq16 : q < 16 := by
    by_contra hq16
    have := Nat.mul_le_mul_right m (not_lt.1 hq16)
    omega
  have hsucc : (q + 1) * m = q * m + m := by ring
  refine ⟨q, hq16, by omega, lt_gapSegLen_of_window hfeas hq1 (by omega)⟩

/-- **Long feasible window** (`density-tail.md` (4.3)): with `m = ⌊t/8⌋`, a cyclic failure at
`t ≥ 16` makes one of the blocks `[jm, (j+1)m]`, `j < 16`, feasible. -/
theorem cyclicCount_pos_block {eps : ℝ} (heps : 0 ≤ eps) {t : ℕ} (ht : 16 ≤ t)
    {g : ℕ → ℝ} (hg : ∀ i, 0 < g i) (h : 1 ≤ cyclicCount eps (fun i : Fin t => g i)) :
    ∃ j < 16, (j + 1) * (t / 8) ≤ t ∧
      ((t / 8 : ℕ) : ℕ∞) < gapSegLen eps (fun i => g (j * (t / 8) + i)) := by
  classical
  -- the positivity of the gaps and `0 ≤ eps` are not needed for this inclusion
  have _ := heps
  have _ := hg
  set z : Fin t → ℝ := fun i => g i with hz
  obtain ⟨r, hr⟩ : ∃ r : Fin t, stopsAt eps (rot z r) := by
    unfold cyclicCount at h
    obtain ⟨r, hr⟩ := Finset.card_pos.1 (show 0 < #{r : Fin t | stopsAt eps (rot z r)} by omega)
    exact ⟨r, (Finset.mem_filter.1 hr).2⟩
  have hfeas := ((stopsAt_rot_iff z r).1 hr).1
  have hpk : ∀ j ≤ t, pkeys z j = gapKeys g j := fun j hj => LocalCount.pkeys_eq_sum g hj
  have hrt : (r : ℕ) < t := r.2
  rcases Nat.eq_zero_or_pos (r : ℕ) with h0 | hpos
  · -- `r = 0`: the window `[0, t - 1]`
    refine exists_block_of_window (a := 0) (L := t) (c := 0) ht ?_ (by omega) (by omega)
    refine (prefixAffineFeasible_congr fun i hi => ?_).1 hfeas
    simp only [h0, zero_add, add_zero]
    exact hpk i hi.le
  · by_cases hlong : (r : ℕ) ≤ t - r + 1
    · -- the window `[r, t]`
      refine exists_block_of_window (a := r) (L := t - r + 1) (c := 0) ht ?_ (by omega)
        (by omega)
      have hf := prefixAffineFeasible_mono hfeas (show t - r + 1 ≤ t by omega)
      refine (prefixAffineFeasible_congr fun i hi => ?_).1 hf
      rw [add_zero, hpk _ (by omega)]
    · -- the window `[0, r - 1]`, translated by one period
      refine exists_block_of_window (a := 0) (L := r) (c := gapKeys g t) ht ?_ (by omega)
        (by omega)
      have hf := prefixAffineFeasible_window (r := t - r) (w := r) hfeas (by omega)
      refine (prefixAffineFeasible_congr fun i hi => ?_).1 hf
      show pkeys z (r + (t - r + i)) = gapKeys g (0 + i) + gapKeys g t
      rw [show (r : ℕ) + (t - r + i) = i + t by omega, pkeys_add_period, hpk i (by omega),
        hpk t le_rfl, zero_add]

/-! ## Factorisation -/

/-- A local bound of a probability law has a nonnegative constant. -/
theorem LocBd.const_nonneg {c : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : LocBd c μ) :
    0 ≤ c := by
  by_contra hc
  have h0 : ENNReal.ofReal c = 0 := ENNReal.ofReal_eq_zero.2 (le_of_lt (not_le.1 hc))
  have h1 := h univ MeasurableSet.univ
  rw [h0, zero_mul, measure_univ] at h1
  exact absurd h1 (by norm_num)

/-- Tonelli for the slices `A ∩ {x : |x - N|/2 ≤ |y - a|}`. -/
theorem lintegral_volume_inter_dev_eq {μ : Measure ℝ} [SFinite μ] (A : Set ℝ) (N a : ℝ) :
    ∫⁻ y, volume (A ∩ {x | |x - N| / 2 ≤ |y - a|}) ∂μ =
      ∫⁻ x in A, μ {y | |x - N| / 2 ≤ |y - a|} := by
  classical
  set f : ℝ → ℝ → ℝ≥0∞ := fun y x => if |x - N| / 2 ≤ |y - a| then 1 else 0 with hf
  have hfm : Measurable (Function.uncurry f) := by
    change Measurable fun p : ℝ × ℝ => if |p.2 - N| / 2 ≤ |p.1 - a| then (1 : ℝ≥0∞) else 0
    exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const
      measurable_const
  have h1 : ∀ y, volume (A ∩ {x | |x - N| / 2 ≤ |y - a|}) = ∫⁻ x in A, f y x := by
    intro y
    have hm : MeasurableSet {x : ℝ | |x - N| / 2 ≤ |y - a|} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have e : (fun x => f y x) = {x : ℝ | |x - N| / 2 ≤ |y - a|}.indicator 1 := by
      funext x
      simp only [hf, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [e, lintegral_indicator_one hm, Measure.restrict_apply hm, Set.inter_comm]
  have h2 : ∀ x, μ {y | |x - N| / 2 ≤ |y - a|} = ∫⁻ y, f y x ∂μ := by
    intro x
    have hm : MeasurableSet {y : ℝ | |x - N| / 2 ≤ |y - a|} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have e : (fun y => f y x) = {y : ℝ | |x - N| / 2 ≤ |y - a|}.indicator 1 := by
      funext y
      simp only [hf, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [e, lintegral_indicator_one hm]
  simp_rw [h1, h2]
  exact lintegral_lintegral_swap hfm.aemeasurable

/-- The deviating half: if `X` has `LocBd c` and is independent of `W`, the event that
`W + X ∈ A` while `W` deviates from `a` by at least `|W + X - N|/2` has probability at most
`c ∫_A P(|x - N|/2 ≤ |W - a|) dx`. -/
theorem measure_add_mem_dev_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {X W : Ω → ℝ} (hX : Measurable X) (hW : Measurable W) (hind : IndepFun X W P) {c : ℝ}
    (hc : LocBd c (P.map X)) {A : Set ℝ} (hA : MeasurableSet A) (N a : ℝ) :
    P {ω | W ω + X ω ∈ A ∧ |W ω + X ω - N| / 2 ≤ |W ω - a|} ≤
      ENNReal.ofReal c * ∫⁻ x in A, (P.map W) {y | |x - N| / 2 ≤ |y - a|} := by
  set F : Set (ℝ × ℝ) := {p | p.2 + p.1 ∈ A ∧ |p.2 + p.1 - N| / 2 ≤ |p.2 - a|} with hF
  have hFm : MeasurableSet F :=
    ((measurable_snd.add measurable_fst) hA).inter
      (measurableSet_le (f := fun p : ℝ × ℝ => |p.2 + p.1 - N| / 2) (g := fun p => |p.2 - a|)
        (by fun_prop) (by fun_prop))
  have hloc : ∀ B : Set ℝ, MeasurableSet B → P (X ⁻¹' B) ≤ ENNReal.ofReal c * volume B :=
    fun B hB => by
      rw [← Measure.map_apply hX hB]
      exact hc B hB
  have key := measure_pair_le_lintegral hX hW hind hloc hFm
  have hslice : ∀ w, volume ((fun x => (x, w)) ⁻¹' F) =
      volume (A ∩ {x | |x - N| / 2 ≤ |w - a|}) := by
    intro w
    have e : (fun x => (x, w)) ⁻¹' F = (fun x => w + x) ⁻¹' (A ∩ {x | |x - N| / 2 ≤ |w - a|}) := by
      ext x
      simp [hF]
    rw [e, measure_preimage_add]
  simp_rw [hslice] at key
  rw [lintegral_volume_inter_dev_eq A N a] at key
  exact key

/-- **Block factorisation**: an event of the gaps `u, …, u+m-1` meets `{S_t ∈ A}` with
probability at most `P(event) · c |A|` when `S_{t-m}` has `LocBd c`. -/
theorem measure_block_inter_le (ρ : ProbabilityMeasure ℝ) {u m t : ℕ} (hut : u + m ≤ t)
    {E' : Set (Fin m → ℝ)} (hE' : MeasurableSet E') {c : ℝ}
    (hc : LocBd c (convPow (ρ : Measure ℝ) (t - m))) {A : Set ℝ} (hA : MeasurableSet A) :
    iidLaw ρ ({g | (fun i : Fin m => g (u + i)) ∈ E'} ∩ {g | gapKeys g t ∈ A}) ≤
      iidLaw ρ {g | (fun i : Fin m => g (u + i)) ∈ E'} * (ENNReal.ofReal c * volume A) := by
  classical
  have hX := iidSeq_gapCoord ρ
  set T : Finset ℕ := Finset.Ico u (u + m) with hT
  set S : Finset ℕ := Finset.range t \ T with hSdef
  have hTsub : T ⊆ Finset.range t := by
    intro i hi
    simp only [hT, Finset.mem_Ico] at hi
    simp only [Finset.mem_range]
    omega
  have hcard : S.card = t - m := by
    rw [hSdef, Finset.card_sdiff_of_subset hTsub, Finset.card_range, hT, Nat.card_Ico]
    omega
  set Y : (ℕ → ℝ) → ℝ := gsum gapCoord S with hY
  set W : (ℕ → ℝ) → Fin m → ℝ := fun g i => g (u + i) with hW
  have hYm : Measurable Y := measurable_gsum hX.measurable S
  have hWm : Measurable W := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hind : IndepFun Y W (iidLaw ρ) := by
    refine hX.indepFun_of_disjoint Finset.sdiff_disjoint (measurable_gsum_sup subset_rfl) ?_
    refine @measurable_pi_lambda _ _ _
      (⨆ i ∈ (T : Set ℕ), MeasurableSpace.comap (gapCoord i) inferInstance) _ W fun i => ?_
    exact (comap_measurable (gapCoord (u + i))).mono
      (le_iSup₂ (f := fun i (_ : i ∈ (T : Set ℕ)) =>
        MeasurableSpace.comap (gapCoord i) inferInstance) (u + i) (by simp [hT])) le_rfl
  have hloc : ∀ B : Set ℝ, MeasurableSet B →
      iidLaw ρ (Y ⁻¹' B) ≤ ENNReal.ofReal c * volume B := by
    intro B hB
    rw [← Measure.map_apply hYm hB]
    have hlaw : (iidLaw ρ).map Y = convPow (ρ : Measure ℝ) (t - m) := by
      rw [← hcard, ← map_sum_finset_eq_convPow]
      rfl
    rw [hlaw]
    exact hc B hB
  set F : Set (ℝ × (Fin m → ℝ)) := {p | p.2 ∈ E' ∧ p.1 + ∑ i, p.2 i ∈ A} with hF
  have hFm : MeasurableSet F :=
    (measurable_snd hE').inter ((measurable_fst.add (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp measurable_snd)) hA)
  have hkeys : ∀ g : ℕ → ℝ, gapKeys g t = Y g + ∑ i, W g i := by
    intro g
    have h1 : ∑ i : Fin m, W g i = ∑ i ∈ T, g i := by
      rw [hT, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
        ← Fin.sum_univ_eq_sum_range (fun k => g (u + k)) m]
    rw [h1, gapKeys]
    simp only [hY, gsum, gapCoord]
    exact (Finset.sum_sdiff hTsub).symm
  have hset : {g : ℕ → ℝ | (fun i : Fin m => g (u + i)) ∈ E'} ∩ {g | gapKeys g t ∈ A} =
      (fun g => (Y g, W g)) ⁻¹' F := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, hF, hkeys]
    rfl
  have key := measure_pair_le_lintegral hYm hWm hind hloc hFm
  have hslice : ∀ w : Fin m → ℝ,
      volume ((fun x => (x, w)) ⁻¹' F) = E'.indicator (fun _ => volume A) w := by
    intro w
    by_cases hw : w ∈ E'
    · rw [Set.indicator_of_mem hw]
      have e : (fun x => (x, w)) ⁻¹' F = (fun x => x + ∑ i, w i) ⁻¹' A := by
        ext x
        simp [hF, hw]
      rw [e, measure_preimage_add_right]
    · rw [Set.indicator_of_notMem hw]
      have e : (fun x => (x, w)) ⁻¹' F = ∅ := by
        ext x
        simp [hF, hw]
      rw [e, measure_empty]
  simp_rw [hslice] at key
  rw [lintegral_indicator_const hE', Measure.map_apply hWm hE'] at key
  rw [hset]
  refine key.trans (le_of_eq ?_)
  rw [show W ⁻¹' E' = {g : ℕ → ℝ | (fun i : Fin m => g (u + i)) ∈ E'} from rfl]
  ring

/-- **Spatial localisation** (`density-tail.md` (4.5) in measure form). -/
theorem measure_gapKeys_le_spatial (ρ : ProbabilityMeasure ℝ) {r s : ℕ} {cr cs : ℝ}
    (hr : LocBd cr (convPow (ρ : Measure ℝ) r)) (hs : LocBd cs (convPow (ρ : Measure ℝ) s))
    {A : Set ℝ} (hA : MeasurableSet A) :
    iidLaw ρ {g | gapKeys g (r + s) ∈ A} ≤
      ∫⁻ x in A, ENNReal.ofReal
        (cs * (iidLaw ρ).real {g | |x - ((r + s : ℕ) : ℝ)| / 2 ≤ |gapKeys g r - r|} +
          cr * (iidLaw ρ).real {g | |x - ((r + s : ℕ) : ℝ)| / 2 ≤ |gapKeys g s - s|}) := by
  classical
  have hX := iidSeq_gapCoord ρ
  set Y : (ℕ → ℝ) → ℝ := gsum gapCoord (Finset.range r) with hY
  set Z : (ℕ → ℝ) → ℝ := gsum gapCoord (Finset.Ico r (r + s)) with hZ
  have hYm : Measurable Y := measurable_gsum hX.measurable _
  have hZm : Measurable Z := measurable_gsum hX.measurable _
  have hdisj : Disjoint (Finset.range r) (Finset.Ico r (r + s)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_range, Finset.mem_Ico] at hi hi'
    omega
  have hYZ : IndepFun Y Z (iidLaw ρ) :=
    hX.indepFun_of_disjoint hdisj (measurable_gsum_sup subset_rfl) (measurable_gsum_sup subset_rfl)
  have hYlaw : (iidLaw ρ).map Y = convPow (ρ : Measure ℝ) r := by
    have h := map_sum_finset_eq_convPow ρ (Finset.range r)
    rw [Finset.card_range] at h
    exact h
  have hZlaw : (iidLaw ρ).map Z = convPow (ρ : Measure ℝ) s := by
    have h := map_sum_finset_eq_convPow ρ (Finset.Ico r (r + s))
    rw [Nat.card_Ico, Nat.add_sub_cancel_left] at h
    exact h
  have hsplit : ∀ g, gapKeys g (r + s) = Y g + Z g := by
    intro g
    simp only [hY, hZ, gsum, gapCoord, gapKeys]
    rw [Finset.sum_range_add, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have hcr : 0 ≤ cr := hr.const_nonneg
  have hcs : 0 ≤ cs := hs.const_nonneg
  set N : ℝ := ((r + s : ℕ) : ℝ) with hN
  have h1 := measure_add_mem_dev_le hZm hYm hYZ.symm (c := cs) (by rw [hZlaw]; exact hs) hA N r
  have h2 := measure_add_mem_dev_le hYm hZm hYZ (c := cr) (by rw [hYlaw]; exact hr) hA N s
  have hmapY : ∀ x, (iidLaw ρ).map Y {y | |x - N| / 2 ≤ |y - r|} =
      iidLaw ρ {g | |x - N| / 2 ≤ |gapKeys g r - r|} := by
    intro x
    rw [Measure.map_apply hYm (measurableSet_le (f := fun _ : ℝ => |x - N| / 2)
      (g := fun y => |y - (r : ℝ)|) measurable_const (by fun_prop))]
    rfl
  have hmapZ : ∀ x, (iidLaw ρ).map Z {y | |x - N| / 2 ≤ |y - s|} =
      iidLaw ρ {g | |x - N| / 2 ≤ |gapKeys g s - s|} := by
    intro x
    rw [hZlaw, ← map_gapKeys_eq_convPow, Measure.map_apply (f := fun g : ℕ → ℝ => gapKeys g s)
      ((measurable_pi_apply s).comp measurable_gapKeys)
      (measurableSet_le (f := fun _ : ℝ => |x - N| / 2) (g := fun y => |y - (s : ℝ)|)
        measurable_const (by fun_prop))]
    rfl
  simp_rw [hmapY] at h1
  simp_rw [hmapZ] at h2
  have hcover : {g : ℕ → ℝ | gapKeys g (r + s) ∈ A} ⊆
      {g | Y g + Z g ∈ A ∧ |Y g + Z g - N| / 2 ≤ |Y g - r|} ∪
        {g | Z g + Y g ∈ A ∧ |Z g + Y g - N| / 2 ≤ |Z g - s|} := by
    intro g hg
    simp only [Set.mem_ofPred_eq, hsplit] at hg
    have htri : |Y g + Z g - N| ≤ |Y g - r| + |Z g - s| := by
      have e : Y g + Z g - N = (Y g - r) + (Z g - s) := by
        rw [hN]
        push_cast
        ring
      rw [e]
      exact abs_add_le _ _
    by_cases h : |Y g + Z g - N| / 2 ≤ |Y g - r|
    · exact Or.inl ⟨hg, h⟩
    · refine Or.inr ⟨by rwa [add_comm], ?_⟩
      rw [add_comm (Z g)]
      linarith
  calc iidLaw ρ {g | gapKeys g (r + s) ∈ A}
      ≤ iidLaw ρ ({g | Y g + Z g ∈ A ∧ |Y g + Z g - N| / 2 ≤ |Y g - r|} ∪
        {g | Z g + Y g ∈ A ∧ |Z g + Y g - N| / 2 ≤ |Z g - s|}) := measure_mono hcover
    _ ≤ iidLaw ρ {g | Y g + Z g ∈ A ∧ |Y g + Z g - N| / 2 ≤ |Y g - r|} +
        iidLaw ρ {g | Z g + Y g ∈ A ∧ |Z g + Y g - N| / 2 ≤ |Z g - s|} := measure_union_le _ _
    _ ≤ ENNReal.ofReal cs * (∫⁻ x in A, iidLaw ρ {g | |x - N| / 2 ≤ |gapKeys g r - r|}) +
        ENNReal.ofReal cr * ∫⁻ x in A, iidLaw ρ {g | |x - N| / 2 ≤ |gapKeys g s - s|} :=
        add_le_add h1 h2
    _ = (∫⁻ x in A, ENNReal.ofReal cs * iidLaw ρ {g | |x - N| / 2 ≤ |gapKeys g r - r|}) +
        ∫⁻ x in A, ENNReal.ofReal cr * iidLaw ρ {g | |x - N| / 2 ≤ |gapKeys g s - s|} := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ x in A, (ENNReal.ofReal cs * iidLaw ρ {g | |x - N| / 2 ≤ |gapKeys g r - r|} +
        ENNReal.ofReal cr * iidLaw ρ {g | |x - N| / 2 ≤ |gapKeys g s - s|}) :=
        le_lintegral_add _ _
    _ = _ := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hcs,
          ENNReal.ofReal_mul hcr, ofReal_measureReal, ofReal_measureReal]

end

end PGM
