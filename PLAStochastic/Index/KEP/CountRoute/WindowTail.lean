import PLAStochastic.Index.KEP.CountRoute.ReferenceCount

/-!
# The early-termination tail input from a window tail condition

Source: `pgm-analysis/research/2026-09-28-kep-additive/lower-count-interface.md`, §1
(condition (W)) and `conditional-assembly.md`, §6 (15).

The event `{epHeight ≤ L}` of the sorted Model K sample is, for `eps ≥ 1/2` and `L ≥ 1`,
the event that the anchored pairs at the first key have no second layer-`L` pivot before
the end of the sample (`epHeight_le_iff_layerPivot_anchPairsW`).  Conditioning on the first
key (`orderLaw_le_layerPivot_anchPairsW_resc_le_iSup`) reduces its probability to a supremum
over anchor values `u ∈ [0, 1)` of anchored probabilities.  The **window tail condition**
`KepWindowTail Q eps0 R r K` bounds these anchored probabilities by `K m_L / n` once
`n > R eps^r m_L`; it is the finite-sample form of (W) at the actual reference scale and is
**assumed** here.

* `one_le_epHeight`: the height is at least `1` for `eps ≥ 1/2`, `n ≥ 1`.
* `measureReal_epHeight_kKeys_le_of_windowTail`: the hypothesis `htail` of
  `H_EP_additive_of_reference_count_tail`, for all layers `L`.
* `H_EP_additive_kKeys_of_windowQuantile_windowTail`: the additive `O(1)` height formula for
  the sorted Model K sample under the two window conditions `KepWindowQuantile` and
  `KepWindowTail` alone.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-- For `eps ≥ 1/2` and `n ≥ 1` the finite run reaches a single key, so its height is a
    layer index `≥ 1`. -/
theorem one_le_epHeight {eps : ℝ} (heps : 1 / 2 ≤ eps) (p : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ epHeight eps p n :=
  (Nat.sInf_mem (exists_epLayer_snd_eq_one heps p hn)).1

/-- **Window tail condition (W) at the reference scale.**  For `eps ≥ eps0`, every layer
    `L ≥ 1`, every sample size `n = M + 1` with `R eps^r m_L < n` and every anchor value
    `u ∈ [0, 1)`, the anchored pairs with `M` further sorted uniforms have no second layer-`L`
    pivot of base rank `< n` with probability at most `K m_L / n`, `m_L = kepReferenceSpan eps L`. -/
def KepWindowTail (Q : ℝ → ℝ) (eps0 R r K : ℝ) : Prop :=
  ∀ eps, eps0 ≤ eps → ∀ L, 1 ≤ L → ∀ M n : ℕ, n = M + 1 →
    (R * eps ^ r) * kepReferenceSpan eps L < n → ∀ u : ℝ, 0 ≤ u → u < 1 →
      Renyi.orderLaw M {w | n ≤ layerPivot eps (anchPairsW Q u w) L 1} ≤
        ENNReal.ofReal (K * kepReferenceSpan eps L / n)

theorem KepWindowQuantile.mono {Q : ℝ → ℝ} {eps0 eps1 a p Bc γ : ℝ} (h : eps0 ≤ eps1)
    (hQ : KepWindowQuantile Q eps0 a p Bc γ) : KepWindowQuantile Q eps1 a p Bc γ :=
  fun eps heps => hQ eps (h.trans heps)

theorem KepWindowTail.mono {Q : ℝ → ℝ} {eps0 eps1 R r K : ℝ} (h : eps0 ≤ eps1)
    (hT : KepWindowTail Q eps0 R r K) : KepWindowTail Q eps1 R r K :=
  fun eps heps => hT eps (h.trans heps)

omit [IsProbabilityMeasure P] in
/-- **Early-termination tail from the window tail condition.**  For `eps ≥ max eps0 (1/2)`,
    `n ≥ 1`, every layer `L` and `R eps^r m_L < n`,
    `P(epHeight ≤ L) ≤ K m_L / n` for the sorted Model K sample. -/
theorem measureReal_epHeight_kKeys_le_of_windowTail (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps0 R r K : ℝ} (hK : 0 ≤ K) (hT : KepWindowTail (quantK f A B) eps0 R r K)
    {eps : ℝ} (heps0 : eps0 ≤ eps) (heps : 1 / 2 ≤ eps) {n : ℕ} (hn : 1 ≤ n) {L : ℕ}
    (hm : 0 ≤ kepReferenceSpan eps L) (hlt : (R * eps ^ r) * kepReferenceSpan eps L < n) :
    P.real {ω | epHeight eps (kKeys X n ω) n ≤ L} ≤ K * kepReferenceSpan eps L / n := by
  have hbound : 0 ≤ K * kepReferenceSpan eps L / n :=
    div_nonneg (mul_nonneg hK hm) (Nat.cast_nonneg n)
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · have hempty : {ω | epHeight eps (kKeys X n ω) n ≤ 0} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact one_le_epHeight heps _ hn
    rw [hempty, measureReal_empty]
    exact hbound
  · obtain ⟨M, rfl⟩ : ∃ M, n = 1 + M := ⟨n - 1, by omega⟩
    have hP : P {ω | epHeight eps (kKeys X (1 + M) ω) (1 + M) ≤ L} ≤
        ENNReal.ofReal (K * kepReferenceSpan eps L / ((1 + M : ℕ) : ℝ)) := by
      rw [measure_epHeight_kKeys_le_eq_orderLaw hf hX hind]
      have hae : {v : Fin (1 + M) → ℝ |
          epHeight eps (extendKeys (quantK f A B ∘ v)) (1 + M) ≤ L} =ᵐ[Renyi.orderLaw (1 + M)]
          {v | 1 + M ≤ layerPivot eps (anchPairsW (quantK f A B) (v 0) (Renyi.resc 0 v)) L 1} := by
        refine Filter.eventuallyEq_set.2 ?_
        filter_upwards [ae_orderLaw_mem_simplex (1 + M)] with v hv
        exact epHeight_le_iff_layerPivot_anchPairsW heps _ hv hL
      rw [measure_congr hae]
      refine (orderLaw_le_layerPivot_anchPairsW_resc_le_iSup (measurable_quantK hf) eps M
        (1 + M) L).trans (iSup₂_le fun u hu => ?_)
      exact hT eps heps0 L hL M (1 + M) (by omega) hlt u hu.1 hu.2
    exact ENNReal.toReal_le_of_le_ofReal hbound hP

/-- **Additive height for general Model K from the two window conditions.**  Under the window
    quantile condition and the window tail condition for the quantile map of `f`, the expected
    ALG-PGM height of the sorted Model K sample is `log n / log C_eps + O(1)` for all `n ≥ 2`
    and all sufficiently large `eps`. -/
theorem H_EP_additive_kKeys_of_windowQuantile_windowTail (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps0 a p Bc γ : ℝ} (ha : 0 < a) (hp : 0 < p) (hBc : 0 ≤ Bc) (hγ : 0 ≤ γ)
    (hQ : KepWindowQuantile (quantK f A B) eps0 a p Bc γ)
    {R r K : ℝ} (hR : 1 ≤ R) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hT : KepWindowTail (quantK f A B) eps0 R r K) :
    ∃ eps1 C : ℝ, ∀ eps, eps1 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |(∫ ω, (epHeight eps (kKeys X n ω) n : ℝ) ∂P) -
        Real.log n / Real.log (gepC eps)| ≤ C := by
  obtain ⟨e0, _, he0, -, hbud⟩ := kepReferenceSpan_budget
  refine H_EP_additive_kKeys_of_windowQuantile_tail hf hXm hX hind ha hp hBc hγ
    (hQ.mono (le_max_left eps0 e0)) hR hK hr ?_
  intro eps heps n hn L hlt
  have heps0 : eps0 ≤ eps := le_trans (le_max_left _ _) heps
  have he : e0 ≤ eps := le_trans (le_max_right _ _) heps
  have hhalf : 1 / 2 ≤ eps := by linarith
  obtain ⟨-, hpos, -, -, -⟩ := hbud eps he
  exact measureReal_epHeight_kKeys_le_of_windowTail hf hX hind hK hT heps0 hhalf (by omega)
    (hpos L).le hlt

end

end PGM
