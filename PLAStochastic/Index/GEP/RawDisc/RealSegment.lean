import PLAStochastic.Index.GEP.RawDisc.Telescoping

/-!
# WP4 `RawDisc` assembly, part 5: the occupation series on the real segment

For real `t ∈ [0, 1]` the occupation term is a real expectation under the mixture product
`ν_t^{⊗∞}`, `ν_t = (1-t) ν + t σ` (`occTerm_ofReal`):

  `Ψ_k(t) = (1-t) cSurv_k(t)(G_ν) + t cSurv_k(t)(G_σ) = E_{ν_t}[1{k<T} G_{ν_t}(S_k)]
          = E_{ν_t}[1{k<T} (F(S_{k+1}) - F(S_k))]`

(word expansion `cSurv_ofReal`, linearity of `incFn` along the mixture, independence of the next
gap `integral_incInd`).  Telescoping (`tendsto_telescope` with `i = 0`, `T ≥ 1`) then identifies
the occupation series: `F 0 + ∑_k Ψ_k(t) = E_{ν_t}[F(S_T)]` (`occ_series_ofReal`), as soon as the
series converges (it does, by the survival majorant) and `e^{l S_T}` is integrable.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

theorem smallMgf_word {l : ℝ} {ν σ : ProbabilityMeasure ℝ} (hν : SmallMgf l ν)
    (hσ : SmallMgf l σ) (S : Finset ℕ) :
    ∀ j, SmallMgf l ((fun i => if i ∈ S then σ else ν) j) := fun j => by
  dsimp only
  split_ifs
  · exact hσ
  · exact hν

/-- Survival integrands with a test `|G| ≤ 3 e^{l s}` are integrable under every word law. -/
theorem integrable_survInd_word {l : ℝ} {ν σ : ProbabilityMeasure ℝ} (hν : SmallMgf l ν)
    (hσ : SmallMgf l σ) (eps : ℝ) (k : ℕ) (S : Finset ℕ) {G : ℝ → ℝ} (hG : Measurable G)
    {C : ℝ} (hGb : ∀ y, 0 ≤ y → |G y| ≤ C * Real.exp (l * y)) :
    Integrable ((survSet eps k).indicator (fun g => G (gapKeys g k))) (wordLaw ν σ S) := by
  rw [wordLaw_eq_piLaw]
  exact integrable_survInd eps k (fun j => (smallMgf_word hν hσ S j).pos)
    (fun j => (smallMgf_word hν hσ S j).lle) hG hGb

/-- **The occupation term on the real segment.** -/
theorem occTerm_ofReal {eps l : ℝ} {ν σ : ProbabilityMeasure ℝ} (hν : SmallMgf l ν)
    (hσ : SmallMgf l σ) {F : ℝ → ℝ} (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    occTerm eps ν σ (incFn F ν) (incFn F σ) k (t : ℂ) =
      ((∫ g, incInd eps F k g ∂(iidLaw (mixPM ν σ t)) : ℝ) : ℂ) := by
  have hmix := hν.mix hσ ht
  have hGν : ∀ y, 0 ≤ y → |incFn F ν y| ≤ 3 * Real.exp (l * y) := fun y hy =>
    abs_incFn_le hν hFb hy
  have hGσ : ∀ y, 0 ≤ y → |incFn F σ y| ≤ 3 * Real.exp (l * y) := fun y hy =>
    abs_incFn_le hσ hFb hy
  have hmν := measurable_incFn hF ν
  have hmσ := measurable_incFn hF σ
  have e1 := cSurv_ofReal eps ν σ ht k hmν fun S _ =>
    integrable_survInd_word hν hσ eps k S hmν hGν
  have e2 := cSurv_ofReal eps ν σ ht k hmσ fun S _ =>
    integrable_survInd_word hν hσ eps k S hmσ hGσ
  -- integrability under the mixture product
  have iν : Integrable ((survSet eps k).indicator (fun g => incFn F ν (gapKeys g k)))
      (iidLaw (mixPM ν σ t)) :=
    integrable_survInd (ρ := fun _ => mixPM ν σ t) eps k (fun _ => hmix.pos) (fun _ => hmix.lle)
      hmν hGν
  have iσ : Integrable ((survSet eps k).indicator (fun g => incFn F σ (gapKeys g k)))
      (iidLaw (mixPM ν σ t)) :=
    integrable_survInd (ρ := fun _ => mixPM ν σ t) eps k (fun _ => hmix.pos) (fun _ => hmix.lle)
      hmσ hGσ
  have hlin : (1 - t) * survInt eps (iidLaw (mixPM ν σ t)) k (incFn F ν) +
      t * survInt eps (iidLaw (mixPM ν σ t)) k (incFn F σ) =
      survInt eps (iidLaw (mixPM ν σ t)) k (incFn F (mixPM ν σ t)) := by
    unfold survInt
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iν.const_mul _)
      (iσ.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [ae_pos_piLaw (ρ := fun _ => mixPM ν σ t) fun _ => hmix.pos] with g hg
    have hk : 0 ≤ gapKeys g k := gapKeys_nonneg (fun j => (hg j).le) k
    by_cases hs : g ∈ survSet eps k
    · simp only [Set.indicator_of_mem hs]
      rw [incFn_mixPM hν hσ ht hF hFb hk]
    · simp only [Set.indicator_of_notMem hs, mul_zero, add_zero]
  have hinc := integral_incInd (fun _ => mixPM ν σ t) eps hF k
    (integrable_incInd (fun _ => hmix) eps hF hFb k)
  rw [← iidLaw_eq_piLaw] at hinc
  rw [occTerm, e1, e2, hinc, ← hlin]
  push_cast
  rfl

/-- **The occupation series on the real segment** is the stopped test. -/
theorem occ_series_ofReal {eps l : ℝ} (heps : 0 ≤ eps) (hl : 0 ≤ l)
    {ν σ : ProbabilityMeasure ℝ} (hν : SmallMgf l ν) (hσ : SmallMgf l σ) {F : ℝ → ℝ}
    (hF : Measurable F) (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hfin : ∀ᵐ g ∂(iidLaw (mixPM ν σ t)), gapSegLen eps g ≠ ⊤)
    (hexp : Integrable (fun g => Real.exp (l * stopSum eps g)) (iidLaw (mixPM ν σ t)))
    (hsum : Summable fun k => occTerm eps ν σ (incFn F ν) (incFn F σ) k (t : ℂ)) :
    (F 0 : ℂ) + ∑' k, occTerm eps ν σ (incFn F ν) (incFn F σ) k (t : ℂ) =
      ((∫ g, F (stopSum eps g) ∂(iidLaw (mixPM ν σ t)) : ℝ) : ℂ) := by
  have hmix := hν.mix hσ ht
  set a : ℕ → ℝ := fun k => ∫ g, incInd eps F k g ∂(iidLaw (mixPM ν σ t)) with ha
  have hocc : ∀ k, occTerm eps ν σ (incFn F ν) (incFn F σ) k (t : ℂ) = ((a k : ℝ) : ℂ) :=
    fun k => occTerm_ofReal hν hσ hF hFb ht k
  simp_rw [hocc] at hsum ⊢
  have hsum' : Summable a := Complex.summable_ofReal.1 hsum
  have hpos : ∀ᵐ g ∂(iidLaw (mixPM ν σ t)), ∀ j, 0 ≤ g j := by
    filter_upwards [ae_pos_piLaw (ρ := fun _ => mixPM ν σ t) fun _ => hmix.pos] with g hg j
    exact (hg j).le
  have hS0 : survSet eps 0 = univ := survSet_zero heps
  have hint : Integrable ((survSet eps 0).indicator (fun g => Real.exp (l * stopSum eps g)))
      (iidLaw (mixPM ν σ t)) := by
    rw [hS0, Set.indicator_univ]; exact hexp
  have htel := tendsto_telescope hl hF hFb hpos hfin 0 hint
  simp only [zero_add, hS0, Set.indicator_univ, gapKeys_zero, integral_const, probReal_univ,
    one_smul] at htel
  have hlim := hsum'.hasSum.tendsto_sum_nat
  have heq : ∑' k, a k = ∫ g, F (stopSum eps g) ∂(iidLaw (mixPM ν σ t)) - F 0 :=
    tendsto_nhds_unique hlim htel
  rw [← Complex.ofReal_tsum, heq]
  push_cast
  ring

end

end PGM
