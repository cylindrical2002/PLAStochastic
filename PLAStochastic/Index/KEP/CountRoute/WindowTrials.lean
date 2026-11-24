import PLAStochastic.Index.KEP.PivotTrials
import PLAStochastic.Index.KEP.CountRoute.WindowContraction

/-!
# Trials at the layer-`L` pivots inside a base window

Source: `pgm-analysis/research/2026-09-28-kep-additive/count-route.md`, §3.1 (adaptive
trials with the quantile condition (Q)), formalised on the sorted-uniform representation of
`PLAStochastic.Index.KEP.PivotTrials`.

For `v : Fin N → ℝ` let `ρ i = samplePivot eps Q L v i` be the layer-`L` pivots of the sample
keys `Q ∘ v`.  Fix a base window `[a, 𝔥)` with `𝔥 ≤ N` and a target gap `gap₀ ≥ 1`.  Trial `i`
is *window-active* if `a ≤ ρ i < 𝔥` (`winActive`); it *succeeds* if moreover the next gap is
at least `min gap₀ (𝔥 - ρ i)` (`winSuccess`).  In contrast to `trialActive` no good-anchor
window is imposed: the quantile condition is assumed for every anchor value `u ∈ [0, 1)`.

* **Counting** (`card_window_success_le`, `sum_indicator_winSuccess_le`): at most
  `(𝔥 - a) / gap₀ + 2` trials succeed, deterministically.
* **Reset** (`ofReal_mul_orderLaw_winActive_inter_le`, `ofReal_mul_orderLaw_winActive_le`):
  on `{ρ i = r}` the active event is a `pre r`-preimage up to the null event `{v r = 1}`, and
  the success event contains the anchored success event at `(v r, resc r v)`
  (`samplePairs_shift_eq_anchPairsW`); `mul_orderLaw_pre_le` gives
  `p · P(trial i active) ≤ P(trial i succeeds)`.
* **Main bound** (`integral_winCount_le`): under `orderLaw N`, if at every rank
  `a ≤ r < 𝔥` and every anchor value `u ∈ [0, 1)` the anchored pairs with `N - 1 - r` fresh
  sorted uniforms have leading layer-`L` pivot at least `min gap₀ (𝔥 - r)` with probability at
  least `p`, then `E[winCount eps (samplePairs Q v) L a 𝔥] ≤ ((𝔥 - a) / gap₀ + 2) / p`.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Finset

/-! ## Counting successful trials in a window (deterministic) -/

/-- **Window trial count.**  Along a strictly increasing pivot sequence `ρ`, the pivots
    `a ≤ ρ i < 𝔥` followed by a gap of at least `min gap₀ (𝔥 - ρ i)` number at most
    `(𝔥 - a) / gap₀ + 1`. -/
theorem card_window_success_le {ρ : ℕ → ℕ} (hρ : StrictMono ρ) {a 𝔥 gap₀ : ℕ} (hgap : 1 ≤ gap₀)
    (S : Finset ℕ) :
    #{i ∈ S | (a ≤ ρ i ∧ ρ i < 𝔥) ∧ min gap₀ (𝔥 - ρ i) ≤ ρ (i + 1) - ρ i} ≤
      (𝔥 - a) / gap₀ + 1 := by
  set T := {i ∈ S | (a ≤ ρ i ∧ ρ i < 𝔥) ∧ min gap₀ (𝔥 - ρ i) ≤ ρ (i + 1) - ρ i} with hT
  have hsplit := card_filter_add_card_filter_not (s := T) (fun i => ρ i + gap₀ ≤ 𝔥)
  have hmono := hρ.monotone
  have h1 : #{i ∈ T | ρ i + gap₀ ≤ 𝔥} ≤ (𝔥 - a) / gap₀ := by
    have hmaps : Set.MapsTo (fun i => (ρ i - a) / gap₀) ({i ∈ T | ρ i + gap₀ ≤ 𝔥} : Finset ℕ)
        (range ((𝔥 - a) / gap₀)) := by
      intro i hi
      simp only [coe_filter, hT, mem_filter, Set.mem_ofPred_eq] at hi
      simp only [coe_range, Set.mem_Iio]
      have h := Nat.div_le_div_right (c := gap₀) (show ρ i - a + gap₀ ≤ 𝔥 - a by omega)
      rw [Nat.add_div_right _ (by omega)] at h
      omega
    have hinj : Set.InjOn (fun i => (ρ i - a) / gap₀) ({i ∈ T | ρ i + gap₀ ≤ 𝔥} : Finset ℕ) := by
      have key : ∀ i j, i ∈ ({i ∈ T | ρ i + gap₀ ≤ 𝔥} : Finset ℕ) → i < j →
          (ρ i - a) / gap₀ < (ρ j - a) / gap₀ := by
        intro i j hi hij
        simp only [hT, mem_filter] at hi
        obtain ⟨⟨-, ⟨hia, hi1⟩, hi2⟩, hi3⟩ := hi
        have hg : ρ i + gap₀ ≤ ρ (i + 1) := by
          have : min gap₀ (𝔥 - ρ i) = gap₀ := min_eq_left (by omega)
          have := hρ (Nat.lt_succ_self i)
          omega
        have hj : ρ i + gap₀ ≤ ρ j := hg.trans (hmono (Nat.succ_le_of_lt hij))
        have h := Nat.div_le_div_right (c := gap₀) (show ρ i - a + gap₀ ≤ ρ j - a by omega)
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
      obtain ⟨⟨-, ⟨-, hi1⟩, hi2⟩, hi3⟩ := hi
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

/-! ## Window trials at the sample pivots -/

section Trials

/-- Trial `i` is window-active: the pivot `i` lies in `[a, 𝔥)`. -/
def winActive (eps : ℝ) (Q : ℝ → ℝ) (L a 𝔥 N i : ℕ) : Set (Fin N → ℝ) :=
  {v | a ≤ samplePivot eps Q L v i ∧ samplePivot eps Q L v i < 𝔥}

/-- Trial `i` succeeds: it is window-active and the next gap is at least
    `min gap₀ (𝔥 - ρ i)`. -/
def winSuccess (eps : ℝ) (Q : ℝ → ℝ) (L a 𝔥 gap₀ N i : ℕ) : Set (Fin N → ℝ) :=
  winActive eps Q L a 𝔥 N i ∩
    {v | min gap₀ (𝔥 - samplePivot eps Q L v i) ≤
      samplePivot eps Q L v (i + 1) - samplePivot eps Q L v i}

variable {N : ℕ} {Q : ℝ → ℝ} {eps : ℝ}

theorem measurableSet_winActive (hQ : Measurable Q) (eps : ℝ) (L a 𝔥 i : ℕ) :
    MeasurableSet (winActive eps Q L a 𝔥 N i) :=
  measurable_samplePivot hQ eps L i (MeasurableSet.of_discrete (s := {r : ℕ | a ≤ r ∧ r < 𝔥}))

theorem measurableSet_winSuccess (hQ : Measurable Q) (eps : ℝ) (L a 𝔥 gap₀ i : ℕ) :
    MeasurableSet (winSuccess eps Q L a 𝔥 gap₀ N i) := by
  refine (measurableSet_winActive hQ eps L a 𝔥 i).inter ?_
  have hm : Measurable fun v : Fin N → ℝ =>
      (samplePivot eps Q L v i, samplePivot eps Q L v (i + 1)) :=
    (measurable_samplePivot hQ eps L i).prodMk (measurable_samplePivot hQ eps L (i + 1))
  exact hm (MeasurableSet.of_discrete (s := {q : ℕ × ℕ | min gap₀ (𝔥 - q.1) ≤ q.2 - q.1}))

/-- The window count is the number of window-active trials. -/
theorem winCount_samplePairs_eq_sum_indicator (heps : 0 ≤ eps) (Q : ℝ → ℝ) {L a 𝔥 : ℕ}
    (h𝔥 : 𝔥 ≤ N) (v : Fin N → ℝ) :
    (winCount eps (samplePairs Q v) L a 𝔥 : ℝ) =
      ∑ i ∈ range N, (winActive eps Q L a 𝔥 N i).indicator 1 v := by
  rw [← card_filter_layerPivot_eq_winCount heps (samplePairs_snd Q v)
    (allLayersFinite_samplePairs eps Q v) L a h𝔥]
  classical
  rw [← sum_boole]
  refine sum_congr rfl fun i _ => ?_
  simp only [Set.indicator_apply, Pi.one_apply, winActive, Set.mem_ofPred_eq, samplePivot]

/-- **Counting successes.**  At most `(𝔥 - a) / gap₀ + 2` of the trials `i < N` succeed. -/
theorem sum_indicator_winSuccess_le (heps : 0 ≤ eps) (Q : ℝ → ℝ) {L a 𝔥 gap₀ : ℕ}
    (hgap : 1 ≤ gap₀) (v : Fin N → ℝ) :
    ∑ i ∈ range N, (winSuccess eps Q L a 𝔥 gap₀ N i).indicator 1 v ≤
      ((𝔥 - a : ℕ) : ℝ) / gap₀ + 2 := by
  classical
  have hsum : ∑ i ∈ range N, (winSuccess eps Q L a 𝔥 gap₀ N i).indicator 1 v =
      ((#{i ∈ range N | v ∈ winSuccess eps Q L a 𝔥 gap₀ N i} : ℕ) : ℝ) := by
    rw [← sum_boole]
    refine sum_congr rfl fun i _ => ?_
    simp only [Set.indicator_apply, Pi.one_apply]
  rw [hsum]
  have hmono := layerPivot_strictMono heps (samplePairs_snd Q v)
    (allLayersFinite_samplePairs eps Q v) L
  have h1 : #{i ∈ range N | v ∈ winSuccess eps Q L a 𝔥 gap₀ N i} ≤ (𝔥 - a) / gap₀ + 1 := by
    refine (card_le_card fun i hi => ?_).trans (card_window_success_le hmono hgap (range N))
    simp only [mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1, hi.2.2⟩
  have h2 : ((#{i ∈ range N | v ∈ winSuccess eps Q L a 𝔥 gap₀ N i} : ℕ) : ℝ) ≤
      (((𝔥 - a) / gap₀ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : (((𝔥 - a) / gap₀ : ℕ) : ℝ) ≤ ((𝔥 - a : ℕ) : ℝ) / gap₀ := Nat.cast_div_le
  push_cast at h2
  linarith

end Trials

/-! ## Reset at the `i`-th pivot -/

section Reset

variable {N : ℕ} {Q : ℝ → ℝ} {eps : ℝ}

/-- **Reset at the pivot `i`, one rank.**  On `{ρ i = r}` with `a ≤ r < 𝔥` the active event
    is (up to the null event `{v r = 1}`) a past event, and the success event contains the
    anchored success event at `(v r, resc r v)`. -/
theorem ofReal_mul_orderLaw_winActive_inter_le (hQ : Measurable Q) {L a 𝔥 gap₀ : ℕ}
    (h𝔥 : 𝔥 ≤ N) {p : ℝ}
    (hS : ∀ r, a ≤ r → r < 𝔥 → ∀ m, r + 1 + m = N → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ENNReal.ofReal p ≤
        Renyi.orderLaw m {w | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q u w) L 1})
    (i : ℕ) {r : ℕ} (hra : a ≤ r) (hr : r < 𝔥) :
    ENNReal.ofReal p *
        Renyi.orderLaw N (winActive eps Q L a 𝔥 N i ∩ {v | samplePivot eps Q L v i = r}) ≤
      Renyi.orderLaw N (winSuccess eps Q L a 𝔥 gap₀ N i ∩ {v | samplePivot eps Q L v i = r}) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = r + 1 + m := ⟨N - (r + 1), by omega⟩
  obtain ⟨C₀, hC₀, hC₀eq⟩ := Renyi.exists_preimage_pre_of_measurableSet_coordSigma
    (measurableSet_layerPivot_samplePairs_eq (eps := eps) hQ L i r)
  set C : Set (Fin (r + 1) → ℝ) := C₀ ∩ {x | x (Fin.last r) < 1} with hCdef
  have hC : MeasurableSet C :=
    hC₀.inter (measurableSet_lt (measurable_pi_apply (Fin.last r)) measurable_const)
  set F : Set (ℝ × (Fin m → ℝ)) :=
    {q | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q q.1 q.2) L 1} with hFdef
  have hF : MeasurableSet F :=
    measurable_anchPairsW_uncurry hQ (measurableSet_le_layerPivot eps _ L 1)
  have hmemC : ∀ v : Fin (r + 1 + m) → ℝ, v ∈ Renyi.pre r ⁻¹' C ↔
      samplePivot eps Q L v i = r ∧ Renyi.pivot r v < 1 := by
    intro v
    have h1 : v ∈ Renyi.pre r ⁻¹' C₀ ↔ samplePivot eps Q L v i = r := by
      rw [hC₀eq]
      rfl
    simp only [hCdef, Set.preimage_inter, Set.mem_inter_iff, h1]
    rfl
  -- the active event at rank `r` is `{ρ i = r}`, almost surely `pre r ⁻¹' C`
  have hA : Renyi.orderLaw (r + 1 + m)
      (winActive eps Q L a 𝔥 (r + 1 + m) i ∩ {v | samplePivot eps Q L v i = r}) =
      Renyi.orderLaw (r + 1 + m) (Renyi.pre r ⁻¹' C) := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [ae_orderLaw_mem_simplex (r + 1 + m)] with v hv
    rw [hmemC]
    simp only [winActive, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, hvr⟩
      exact ⟨hvr, Renyi.pivot_lt_one hv⟩
    · rintro ⟨hvr, -⟩
      exact ⟨⟨by rw [hvr]; exact hra, by rw [hvr]; exact hr⟩, hvr⟩
  -- the anchored success event at rank `r` is contained in the success event
  have hY : Renyi.pre r ⁻¹' C ∩ {v | (Renyi.pivot r v, Renyi.resc r v) ∈ F} ⊆
      winSuccess eps Q L a 𝔥 gap₀ (r + 1 + m) i ∩ {v | samplePivot eps Q L v i = r} := by
    rintro v ⟨hvC, hgap⟩
    obtain ⟨hv, hlt⟩ := (hmemC v).1 hvC
    have hv' : layerPivot eps (samplePairs Q v) L i = r := hv
    have e := layerPivot_samplePairs_succ_sub eps Q hlt.ne hv'
    simp only [winSuccess, winActive, Set.mem_inter_iff, Set.mem_ofPred_eq, hFdef] at hgap ⊢
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hv⟩
    · rw [hv]; exact hra
    · rw [hv]; exact hr
    · simp only [samplePivot]
      rw [e, hv']
      exact hgap
  rw [hA]
  refine le_trans ?_ (measure_mono hY)
  exact mul_orderLaw_pre_le hC hF fun x hx h0 => hS r hra hr m rfl _ h0 hx.2

/-- **Reset at the pivot `i`.**  `p · P(trial i window-active) ≤ P(trial i succeeds)`. -/
theorem ofReal_mul_orderLaw_winActive_le (hQ : Measurable Q) {L a 𝔥 gap₀ : ℕ}
    (h𝔥 : 𝔥 ≤ N) {p : ℝ}
    (hS : ∀ r, a ≤ r → r < 𝔥 → ∀ m, r + 1 + m = N → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ENNReal.ofReal p ≤
        Renyi.orderLaw m {w | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q u w) L 1})
    (i : ℕ) :
    ENNReal.ofReal p * Renyi.orderLaw N (winActive eps Q L a 𝔥 N i) ≤
      Renyi.orderLaw N (winSuccess eps Q L a 𝔥 gap₀ N i) := by
  have hf := measurable_samplePivot (N := N) hQ eps L i
  rw [measure_eq_sum_inter_eq _ (measurableSet_winActive hQ eps L a 𝔥 i) hf
      (𝔥 := 𝔥) fun v hv => hv.2,
    measure_eq_sum_inter_eq _ (measurableSet_winSuccess hQ eps L a 𝔥 gap₀ i) hf
      (𝔥 := 𝔥) fun v hv => hv.1.2, mul_sum]
  refine sum_le_sum fun r hr => ?_
  by_cases hra : a ≤ r
  · exact ofReal_mul_orderLaw_winActive_inter_le hQ h𝔥 hS i hra (mem_range.1 hr)
  · have hempty : winActive eps Q L a 𝔥 N i ∩ {v | samplePivot eps Q L v i = r} = ∅ := by
      ext v
      simp only [winActive, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro ⟨h1, -⟩ h2
      rw [h2] at h1
      exact hra h1
    rw [hempty, measure_empty, mul_zero]
    exact zero_le

end Reset

/-! ## The expected window count -/

section Main

variable {N : ℕ} {Q : ℝ → ℝ} {eps : ℝ}

/-- **Expected number of layer-`L` pivots in a base window.**  Let the layer-`L` pivots of
    the sample keys `Q ∘ v`, `v ∼ orderLaw N`, be `ρ i`.  Suppose that at every rank
    `a ≤ r < 𝔥` and every anchor value `u ∈ [0, 1)`, the anchored pairs with `N - 1 - r`
    fresh sorted uniforms have leading layer-`L` pivot at least `min gap₀ (𝔥 - r)` with
    probability at least `p`.  Then the expected number of layer-`L` pivots in `[a, 𝔥)` is at
    most `((𝔥 - a) / gap₀ + 2) / p`. -/
theorem integral_winCount_le (hQ : Measurable Q) (heps : 0 ≤ eps) {L a 𝔥 gap₀ : ℕ}
    (h𝔥 : 𝔥 ≤ N) (hgap : 1 ≤ gap₀) {p : ℝ} (hp : 0 < p)
    (hS : ∀ r, a ≤ r → r < 𝔥 → ∀ m, r + 1 + m = N → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ENNReal.ofReal p ≤
        Renyi.orderLaw m {w | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW Q u w) L 1}) :
    ∫ v, (winCount eps (samplePairs Q v) L a 𝔥 : ℝ) ∂(Renyi.orderLaw N) ≤
      (((𝔥 - a : ℕ) : ℝ) / gap₀ + 2) / p := by
  set μ := Renyi.orderLaw N
  have hA := measurableSet_winActive (N := N) hQ eps L a 𝔥
  have hY := measurableSet_winSuccess (N := N) hQ eps L a 𝔥 gap₀
  have hstep : ∀ i, p * μ.real (winActive eps Q L a 𝔥 N i) ≤
      μ.real (winSuccess eps Q L a 𝔥 gap₀ N i) := by
    intro i
    have h := ENNReal.toReal_mono (measure_ne_top _ _)
      (ofReal_mul_orderLaw_winActive_le hQ h𝔥 hS i)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le] at h
  have hsumY : ∑ i ∈ range N, μ.real (winSuccess eps Q L a 𝔥 gap₀ N i) ≤
      ((𝔥 - a : ℕ) : ℝ) / gap₀ + 2 := by
    have hint : ∀ i ∈ range N,
        Integrable (fun v => (winSuccess eps Q L a 𝔥 gap₀ N i).indicator 1 v) μ :=
      fun i _ => (integrable_const (1 : ℝ)).indicator (hY i)
    calc ∑ i ∈ range N, μ.real (winSuccess eps Q L a 𝔥 gap₀ N i)
        = ∫ v, ∑ i ∈ range N, (winSuccess eps Q L a 𝔥 gap₀ N i).indicator 1 v ∂μ := by
          rw [integral_finsetSum _ hint]
          exact sum_congr rfl fun i _ => (integral_indicator_one (hY i)).symm
      _ ≤ ∫ _v, (((𝔥 - a : ℕ) : ℝ) / gap₀ + 2) ∂μ :=
          integral_mono (integrable_finsetSum _ hint) (integrable_const _)
            fun v => sum_indicator_winSuccess_le heps Q hgap v
      _ = ((𝔥 - a : ℕ) : ℝ) / gap₀ + 2 := by simp
  have hsumA : ∑ i ∈ range N, μ.real (winActive eps Q L a 𝔥 N i) ≤
      (((𝔥 - a : ℕ) : ℝ) / gap₀ + 2) / p := by
    rw [le_div_iff₀ hp, sum_mul]
    refine le_trans (sum_le_sum fun i _ => ?_) hsumY
    rw [mul_comm]
    exact hstep i
  have hintA : ∀ i ∈ range N,
      Integrable (fun v => (winActive eps Q L a 𝔥 N i).indicator 1 v) μ :=
    fun i _ => (integrable_const (1 : ℝ)).indicator (hA i)
  calc ∫ v, (winCount eps (samplePairs Q v) L a 𝔥 : ℝ) ∂μ
      = ∫ v, ∑ i ∈ range N, (winActive eps Q L a 𝔥 N i).indicator 1 v ∂μ :=
        integral_congr_ae (ae_of_all _ fun v =>
          winCount_samplePairs_eq_sum_indicator heps Q h𝔥 v)
    _ = ∑ i ∈ range N, μ.real (winActive eps Q L a 𝔥 N i) := by
        rw [integral_finsetSum _ hintA]
        exact sum_congr rfl fun i _ => integral_indicator_one (hA i)
    _ ≤ _ := hsumA

end Main

end

end PGM
