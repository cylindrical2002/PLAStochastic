import PLAStochastic.Index.KEP.CountRoute.WindowConfiguration
import PLAStochastic.Index.KEP.FiniteWindow.CountOutput
import PLAStochastic.ForMathlib.Probability.Hellinger.Censoring

/-!
# The window bridge: finite sample to the Poisson window at Hellinger cost `p`

Source: `pgm-analysis/research/2026-09-28-kep-additive/poisson-bridge.md`, §2–§4 and §6.

The anchored keys after an anchor `u` are `Q (u + (1 - u) w_i)` for `M` sorted uniforms `w`.
In the window `[0, p)` of the uniform coordinate, the configuration of the finite sample is
`binomial M p ⊗ₘ winKernel p` (`map_winConf_orderLaw`), while the **Poisson window model**
`poissonWindow M p` replaces the binomial count by `Poisson (M p)` with the same conditional
configuration.  The two differ in Hellinger distance by at most `p` (`measureHellinger_window_le`,
from the finite-window count comparison), so square roots of probabilities of any
configuration event transfer at cost `p` (`sqrt_measureReal_le_add_measureHellinger`).

Two events of the configuration are read off the finite run of ALG-PGM on the window keys:

* `tailEvent`: the run on all window keys has height `≤ L`, i.e. no second layer-`L` pivot
  falls inside the window (censoring in §4).  The finite-sample event "no second layer-`L`
  pivot among all `M` keys" is contained in it (`le_layerPivot_subset_tailEvent`).
* `quantEvent g`: the window has at least `g` points and the run on the first `g + 1` keys has
  height `≤ L`, i.e. the second layer-`L` pivot has base rank `> g`.  It is contained in the
  finite-sample event `g + 1 ≤ ρ` (`quantEvent_subset_le_layerPivot`).

Consequently the two window conditions `KepWindowTail` and `KepWindowQuantile` follow from
the corresponding statements about the Poisson window model (`KepPoissonTail`,
`KepPoissonQuantile`), and the additive height for general Model K follows from these alone
(`H_EP_additive_kKeys_of_poissonWindow`).  The Poisson window conditions themselves are the
remaining input of the probabilistic side.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval

/-! ## Square roots of probabilities under a Hellinger bound -/

theorem sqrt_measureReal_le_add_measureHellinger {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {A : Set α}
    (hA : MeasurableSet A) :
    Real.sqrt (P.real A) ≤ Real.sqrt (Q.real A) + measureHellinger P Q ∧
      Real.sqrt (Q.real A) ≤ Real.sqrt (P.real A) + measureHellinger P Q := by
  set p := HellingerDensity.leftDensity P Q
  set q := HellingerDensity.rightDensity P Q
  have h1 := HellingerDensity.sqrt_mass_le_censored p q Aᶜ
  have h1' := HellingerDensity.sqrt_mass_le_censored q p Aᶜ
  have h2 : Real.sqrt (p.censoredSq q Aᶜ) ≤ p.hellinger q := by
    rw [Real.sqrt_le_left (p.hellinger_nonneg q)]
    exact HellingerDensity.censoredSq_le_hellinger_sq p q hA.compl
  have h2' : Real.sqrt (q.censoredSq p Aᶜ) ≤ p.hellinger q := by
    rw [Real.sqrt_le_left (p.hellinger_nonneg q), HellingerDensity.hellinger_comm]
    exact HellingerDensity.censoredSq_le_hellinger_sq q p hA.compl
  rw [compl_compl, HellingerDensity.mass_eq_measureReal p hA,
    HellingerDensity.mass_eq_measureReal q hA, HellingerDensity.leftDensity_toMeasure,
    HellingerDensity.rightDensity_toMeasure] at h1 h1'
  exact ⟨h1.trans (add_le_add le_rfl h2), h1'.trans (add_le_add le_rfl h2')⟩

/-! ## The binomial and Poisson window models -/

/-- The window configuration law of the finite sample: binomial count, conditional sorted
    uniforms on `[0, p]`. -/
def binomialWindow (M : ℕ) (p : I) : Measure (ℕ × (ℕ → ℝ)) :=
  binomial M p ⊗ₘ winKernel p

/-- The Poisson window model: Poisson `(M p)` count, the same conditional configuration. -/
def poissonWindow (M : ℕ) (p : I) : Measure (ℕ × (ℕ → ℝ)) :=
  poissonMeasure (binomialPoissonRate M p) ⊗ₘ winKernel p

instance isProbabilityMeasure_binomialWindow (M : ℕ) (p : I) :
    IsProbabilityMeasure (binomialWindow M p) := by
  unfold binomialWindow; infer_instance

instance isProbabilityMeasure_poissonWindow (M : ℕ) (p : I) :
    IsProbabilityMeasure (poissonWindow M p) := by
  unfold poissonWindow; infer_instance

theorem map_winConf_orderLaw_eq_binomialWindow {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (M : ℕ) : (orderLaw M).map (winConf (p : ℝ)) = binomialWindow M p := by
  rw [binomialWindow, map_winConf_orderLaw hp0 hp1 M]

theorem binomialWindow_real_eq {p : I} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {M : ℕ}
    {A : Set (ℕ × (ℕ → ℝ))} (hA : MeasurableSet A) :
    (binomialWindow M p).real A = (orderLaw M).real (winConf (p : ℝ) ⁻¹' A) := by
  rw [← map_winConf_orderLaw_eq_binomialWindow hp0 hp1 M,
    map_measureReal_apply (measurable_winConf _) hA]

theorem measureHellinger_window_le (M : ℕ) {p : I} (hp : (p : ℝ) ≤ 1 / 2) :
    measureHellinger (binomialWindow M p) (poissonWindow M p) ≤ (p : ℝ) :=
  kep_window_joint_kernel_hellinger_le M p hp (winKernel p)

/-- Finite-sample configuration events transfer to the Poisson window at cost `p`. -/
theorem sqrt_orderLaw_winConf_le (M : ℕ) {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) ≤ 1 / 2)
    {A : Set (ℕ × (ℕ → ℝ))} (hA : MeasurableSet A) :
    Real.sqrt ((orderLaw M).real (winConf (p : ℝ) ⁻¹' A)) ≤
      Real.sqrt ((poissonWindow M p).real A) + p := by
  have hp1 : (p : ℝ) < 1 := by linarith
  have h := (sqrt_measureReal_le_add_measureHellinger (binomialWindow M p) (poissonWindow M p)
    hA).1
  rw [binomialWindow_real_eq hp0 hp1 hA] at h
  exact h.trans (add_le_add le_rfl (measureHellinger_window_le M hp))

/-- Poisson window events transfer back to the finite sample at cost `p`. -/
theorem sqrt_poissonWindow_le (M : ℕ) {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) ≤ 1 / 2)
    {A : Set (ℕ × (ℕ → ℝ))} (hA : MeasurableSet A) :
    Real.sqrt ((poissonWindow M p).real A) ≤
      Real.sqrt ((orderLaw M).real (winConf (p : ℝ) ⁻¹' A)) + p := by
  have hp1 : (p : ℝ) < 1 := by linarith
  have h := (sqrt_measureReal_le_add_measureHellinger (binomialWindow M p) (poissonWindow M p)
    hA).2
  rw [binomialWindow_real_eq hp0 hp1 hA] at h
  exact h.trans (add_le_add le_rfl (measureHellinger_window_le M hp))

/-! ## Window keys and the two configuration events -/

/-- Position of the key of base rank `t` in a padded configuration: the anchor `0` at `t = 0`,
    the `(t-1)`-th window coordinate afterwards. -/
def padPos (x : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then 0 else x (t - 1)

/-- Keys of the window run: anchor `Q u`, then `Q (u + (1 - u) x_{t-1})`. -/
def winKeys (Q : ℝ → ℝ) (u : ℝ) (x : ℕ → ℝ) : ℕ → ℝ := fun t => Q (u + (1 - u) * padPos x t)

theorem measurable_winKeys {Q : ℝ → ℝ} (hQ : Measurable Q) (u : ℝ) :
    Measurable fun c : ℕ × (ℕ → ℝ) => winKeys Q u c.2 := by
  refine measurable_pi_lambda _ fun t => ?_
  unfold winKeys padPos
  split_ifs
  · exact measurable_const
  · exact hQ.comp (measurable_const.add
      (measurable_const.mul ((measurable_pi_apply _).comp measurable_snd)))

/-- The run on all window keys has height `≤ L`: no second layer-`L` pivot inside the window. -/
def tailEvent (eps : ℝ) (Q : ℝ → ℝ) (u : ℝ) (L : ℕ) : Set (ℕ × (ℕ → ℝ)) :=
  {c | epHeight eps (winKeys Q u c.2) (c.1 + 1) ≤ L}

/-- The window has at least `g` points and the run on the first `g + 1` keys has height `≤ L`:
    the second layer-`L` pivot has base rank `> g`, witnessed inside the window. -/
def quantEvent (eps : ℝ) (Q : ℝ → ℝ) (u : ℝ) (L g : ℕ) : Set (ℕ × (ℕ → ℝ)) :=
  {c | g ≤ c.1 ∧ epHeight eps (winKeys Q u c.2) (g + 1) ≤ L}

theorem measurableSet_tailEvent (eps : ℝ) {Q : ℝ → ℝ} (hQ : Measurable Q) (u : ℝ) (L : ℕ) :
    MeasurableSet (tailEvent eps Q u L) := by
  have : tailEvent eps Q u L = ⋃ k, {c : ℕ × (ℕ → ℝ) | c.1 = k} ∩
      {c | epHeight eps (winKeys Q u c.2) (k + 1) ≤ L} := by
    ext c
    simp only [tailEvent, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨c.1, rfl, h⟩
    · rintro ⟨k, rfl, h⟩
      exact h
  rw [this]
  refine MeasurableSet.iUnion fun k => (measurable_fst (measurableSet_singleton k)).inter ?_
  exact measurable_epHeight_comp eps (k + 1) (measurable_winKeys hQ u) measurableSet_Iic

theorem measurableSet_quantEvent (eps : ℝ) {Q : ℝ → ℝ} (hQ : Measurable Q) (u : ℝ) (L g : ℕ) :
    MeasurableSet (quantEvent eps Q u L g) :=
  (measurable_fst measurableSet_Ici).inter
    (measurable_epHeight_comp eps (g + 1) (measurable_winKeys hQ u) measurableSet_Iic)

/-! ## Reading the events on the finite sample -/

section Sample

variable {Q : ℝ → ℝ} {u eps β : ℝ} {M : ℕ}

theorem pairKeys_anchPairsW' (Q : ℝ → ℝ) (u : ℝ) (w : Fin M → ℝ) :
    ∀ t ≤ M, pairKeys (anchPairsW Q u w) t = Q (u + (1 - u) * anchPos w t) - Q u
  | 0, _ => by simp [pairKeys, anchPos]
  | t + 1, ht => by
    have ih := pairKeys_anchPairsW' Q u w t (by omega)
    simp only [pairKeys, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp only [anchPairsW, if_pos (show t < M by omega)]
    ring

theorem anchPairsW_fst_eq_zero' (Q : ℝ → ℝ) (u : ℝ) (w : Fin M → ℝ) {t : ℕ} (ht : M ≤ t) :
    (anchPairsW Q u w t).1 = 0 := by
  simp [anchPairsW, not_lt.2 ht]

theorem allLayersFinite_anchPairsW (eps : ℝ) (Q : ℝ → ℝ) (u : ℝ) (w : Fin M → ℝ) :
    AllLayersFinite eps (anchPairsW Q u w) :=
  allLayersFinite_of_fst_eq_zero (M := M) fun _ ht => anchPairsW_fst_eq_zero' Q u w ht

/-- Below the window count, a strictly increasing sample lies below `β`. -/
theorem lt_of_lt_winPts {w : Fin M → ℝ} (hmono : StrictMono w) {i : Fin M}
    (hi : (i : ℕ) < winPts β w) : w i < β := by
  by_contra h
  rw [not_lt] at h
  have hsub : (Finset.univ.filter fun a : Fin M => w a < β) ⊆ Finset.Iio i := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_Iio]
    by_contra hle
    rw [not_lt] at hle
    linarith [hmono.monotone hle, ha.2]
  have := Finset.card_le_card hsub
  rw [Fin.card_Iio] at this
  change winPts β w ≤ _ at this
  omega

/-- The window keys agree with the anchored keys up to the window count. -/
theorem winKeys_winPad_eq {w : Fin M → ℝ} (hmono : StrictMono w) {t : ℕ}
    (ht : t ≤ winPts β w) :
    winKeys Q u (winPad β w) t = Q u + pairKeys (anchPairsW Q u w) t := by
  have htM : t ≤ M := ht.trans (winPts_le β w)
  rw [pairKeys_anchPairsW' Q u w t htM, add_sub_cancel]
  unfold winKeys padPos anchPos
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp
  · rw [if_neg ht0.ne', dif_pos ⟨ht0, htM⟩]
    unfold winPad
    rw [dif_pos (show t - 1 < M by omega),
      if_pos (lt_of_lt_winPts hmono (i := ⟨t - 1, by omega⟩) (by simp; omega))]

theorem mem_tailEvent_iff (heps : 1 / 2 ≤ eps) {L : ℕ} (hL : 1 ≤ L) {w : Fin M → ℝ}
    (hmono : StrictMono w) :
    winConf β w ∈ tailEvent eps Q u L ↔
      winPts β w + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1 := by
  change epHeight eps (winKeys Q u (winPad β w)) (winPts β w + 1) ≤ L ↔ _
  rw [epHeight_congr (p' := fun t => Q u + pairKeys (anchPairsW Q u w) t)
    fun i hi => winKeys_winPad_eq hmono (by omega)]
  exact epHeight_le_iff_layerPivot heps (fun _ => rfl) (allLayersFinite_anchPairsW eps Q u w)
    (Q u) (by omega) hL

theorem mem_quantEvent_iff (heps : 1 / 2 ≤ eps) {L : ℕ} (hL : 1 ≤ L) {w : Fin M → ℝ}
    (hmono : StrictMono w) (g : ℕ) :
    winConf β w ∈ quantEvent eps Q u L g ↔
      g ≤ winPts β w ∧ g + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1 := by
  change g ≤ winPts β w ∧ epHeight eps (winKeys Q u (winPad β w)) (g + 1) ≤ L ↔ _
  refine and_congr_right fun hg => ?_
  rw [epHeight_congr (p' := fun t => Q u + pairKeys (anchPairsW Q u w) t)
    fun i hi => winKeys_winPad_eq hmono (by omega)]
  exact epHeight_le_iff_layerPivot heps (fun _ => rfl) (allLayersFinite_anchPairsW eps Q u w)
    (Q u) (by omega) hL

/-- No second layer-`L` pivot among all `M` keys forces the censored window event. -/
theorem le_layerPivot_subset_tailEvent (heps : 1 / 2 ≤ eps) {L : ℕ} (hL : 1 ≤ L) :
    ∀ᵐ w ∂(orderLaw M), w ∈ {w : Fin M → ℝ | M + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1} →
      w ∈ winConf β ⁻¹' tailEvent eps Q u L := by
  filter_upwards [ae_orderLaw_mem_simplex M] with w hw hM
  rw [mem_preimage, mem_tailEvent_iff heps hL hw.1]
  have := winPts_le β w
  change M + 1 ≤ _ at hM
  omega

/-- The window quantile event forces the second layer-`L` pivot beyond base rank `g`. -/
theorem quantEvent_subset_le_layerPivot (heps : 1 / 2 ≤ eps) {L : ℕ} (hL : 1 ≤ L) (g : ℕ) :
    ∀ᵐ w ∂(orderLaw M), w ∈ winConf β ⁻¹' quantEvent eps Q u L g →
      w ∈ {w : Fin M → ℝ | g + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1} := by
  filter_upwards [ae_orderLaw_mem_simplex M] with w hw hq
  rw [mem_preimage, mem_quantEvent_iff heps hL hw.1] at hq
  exact hq.2

end Sample

/-! ## The bridge for the two window conditions -/

section Bridge

variable {Q : ℝ → ℝ} {u eps : ℝ} {M : ℕ}

/-- **Tail bridge (10).**  The finite-sample probability of no second layer-`L` pivot is at
    most `(√τ + p)²`, `τ` the Poisson window probability of the censored event. -/
theorem sqrt_orderLaw_le_layerPivot_le (hQ : Measurable Q) (heps : 1 / 2 ≤ eps) {L : ℕ}
    (hL : 1 ≤ L) {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) ≤ 1 / 2) (u : ℝ) :
    Real.sqrt ((orderLaw M).real {w | M + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1}) ≤
      Real.sqrt ((poissonWindow M p).real (tailEvent eps Q u L)) + p := by
  refine le_trans (Real.sqrt_le_sqrt ?_)
    (sqrt_orderLaw_winConf_le M hp0 hp (measurableSet_tailEvent eps hQ u L))
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (le_layerPivot_subset_tailEvent heps hL))

/-- **Quantile bridge.**  The finite-sample probability that the second layer-`L` pivot has
    base rank `> g` is at least `(√π - p)²`, `π` the Poisson window probability of the window
    quantile event. -/
theorem sqrt_poissonWindow_quantEvent_le (hQ : Measurable Q) (heps : 1 / 2 ≤ eps) {L : ℕ}
    (hL : 1 ≤ L) {p : I} (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) ≤ 1 / 2) (u : ℝ) (g : ℕ) :
    Real.sqrt ((poissonWindow M p).real (quantEvent eps Q u L g)) ≤
      Real.sqrt ((orderLaw M).real {w | g + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1}) + p := by
  refine (sqrt_poissonWindow_le M hp0 hp (measurableSet_quantEvent eps hQ u L g)).trans
    (add_le_add (Real.sqrt_le_sqrt ?_) le_rfl)
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (quantEvent_subset_le_layerPivot heps hL g))

end Bridge

/-! ## The window conditions from the Poisson window model -/

/-- **Poisson window tail condition.**  For `eps ≥ eps0`, `L ≥ 1`, `M` remaining keys with
    `R eps^r m_L < M + 1` and every anchor `u ∈ [0, 1)`, some window mass `p ≤ 1/2` makes the
    Poisson window probability `τ` of "no second layer-`L` pivot inside the window" satisfy
    `(√τ + p)² ≤ K m_L / (M + 1)`. -/
def KepPoissonTail (Q : ℝ → ℝ) (eps0 R r K : ℝ) : Prop :=
  ∀ eps, eps0 ≤ eps → ∀ L, 1 ≤ L → ∀ M : ℕ,
    (R * eps ^ r) * kepReferenceSpan eps L < ((M + 1 : ℕ) : ℝ) → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∃ p : I, 0 < (p : ℝ) ∧ (p : ℝ) ≤ 1 / 2 ∧
        (Real.sqrt ((poissonWindow M p).real (tailEvent eps Q u L)) + p) ^ 2 ≤
          K * kepReferenceSpan eps L / ((M + 1 : ℕ) : ℝ)

/-- **Poisson window quantile condition.**  For `eps ≥ eps0`, `L ≥ 1`, `m ≥ ⌈Bc eps^γ m_L⌉`
    remaining keys and every anchor `u ∈ [0, 1)`, some window mass `q ≤ 1/2` makes the Poisson
    window probability of "at least `⌊a m_L⌋` window points and the second layer-`L` pivot of
    base rank `> ⌊a m_L⌋`" at least `(√p + q)²`. -/
def KepPoissonQuantile (Q : ℝ → ℝ) (eps0 a p Bc γ : ℝ) : Prop :=
  ∀ eps, eps0 ≤ eps → ∀ L, 1 ≤ L → ∀ m : ℕ, ⌈Bc * eps ^ γ * kepReferenceSpan eps L⌉₊ ≤ m →
    ∀ u : ℝ, 0 ≤ u → u < 1 →
      ∃ q : I, 0 < (q : ℝ) ∧ (q : ℝ) ≤ 1 / 2 ∧
        Real.sqrt p + q ≤ Real.sqrt ((poissonWindow m q).real
          (quantEvent eps Q u L ⌊a * kepReferenceSpan eps L⌋₊))

theorem kepWindowTail_of_poissonTail {Q : ℝ → ℝ} (hQ : Measurable Q) {eps0 R r K : ℝ}
    (heps0 : 1 / 2 ≤ eps0) (hT : KepPoissonTail Q eps0 R r K) : KepWindowTail Q eps0 R r K := by
  intro eps heps' L hL M n hn hlt u hu0 hu1
  subst hn
  have heps : 1 / 2 ≤ eps := heps0.trans heps'
  obtain ⟨p, hp0, hp, hbound⟩ := hT eps heps' L hL M (by exact_mod_cast hlt) u hu0 hu1
  have hsq := sqrt_orderLaw_le_layerPivot_le (M := M) hQ heps hL hp0 hp u
  have h0 : 0 ≤ Real.sqrt ((orderLaw M).real {w | M + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1}) :=
    Real.sqrt_nonneg _
  have hreal : (orderLaw M).real {w | M + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1} ≤
      K * kepReferenceSpan eps L / ((M + 1 : ℕ) : ℝ) := by
    rw [← Real.sq_sqrt (measureReal_nonneg (μ := orderLaw M))]
    exact (pow_le_pow_left₀ h0 hsq 2).trans hbound
  rw [measureReal_def] at hreal
  rw [← ENNReal.ofReal_toReal (measure_ne_top (orderLaw M) _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem kepWindowQuantile_of_poissonQuantile {Q : ℝ → ℝ} (hQ : Measurable Q)
    {eps0 a p Bc γ : ℝ} (heps0 : 1 / 2 ≤ eps0) (hp : 0 ≤ p)
    (hT : KepPoissonQuantile Q eps0 a p Bc γ) : KepWindowQuantile Q eps0 a p Bc γ := by
  intro eps heps' L hL m hm u hu0 hu1
  have heps : 1 / 2 ≤ eps := heps0.trans heps'
  obtain ⟨q, hq0, hq, hbound⟩ := hT eps heps' L hL m hm u hu0 hu1
  set g := ⌊a * kepReferenceSpan eps L⌋₊
  have hsq := sqrt_poissonWindow_quantEvent_le (M := m) hQ heps hL hq0 hq u g
  have hp' : Real.sqrt p ≤
      Real.sqrt ((orderLaw m).real {w | g + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1}) := by
    linarith
  have hreal : p ≤ (orderLaw m).real {w | g + 1 ≤ layerPivot eps (anchPairsW Q u w) L 1} := by
    rw [← Real.sq_sqrt hp, ← Real.sq_sqrt (measureReal_nonneg (μ := orderLaw m))]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hp' 2
  rw [measureReal_def] at hreal
  rw [← ENNReal.ofReal_toReal (measure_ne_top (orderLaw m) _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Additive height for general Model K from the Poisson window conditions.** -/
theorem H_EP_additive_kKeys_of_poissonWindow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ} (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps0 a p Bc γ : ℝ} (heps0 : 1 / 2 ≤ eps0) (ha : 0 < a) (hp : 0 < p) (hBc : 0 ≤ Bc)
    (hγ : 0 ≤ γ) (hQ : KepPoissonQuantile (quantK f A B) eps0 a p Bc γ)
    {R r K : ℝ} (hR : 1 ≤ R) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hT : KepPoissonTail (quantK f A B) eps0 R r K) :
    ∃ eps1 C : ℝ, ∀ eps, eps1 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |(∫ ω, (epHeight eps (kKeys X n ω) n : ℝ) ∂P) -
        Real.log n / Real.log (gepC eps)| ≤ C :=
  H_EP_additive_kKeys_of_windowQuantile_windowTail hf hXm hX hind ha hp hBc hγ
    (kepWindowQuantile_of_poissonQuantile (measurable_quantK hf) heps0 hp.le hQ) hR hr hK
    (kepWindowTail_of_poissonTail (measurable_quantK hf) heps0 hT)

end

end PGM
