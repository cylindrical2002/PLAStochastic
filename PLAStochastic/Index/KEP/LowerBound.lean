import PLAStochastic.Index.KEP.AnchoredCoupling
import PLAStochastic.Index.KEP.SampleToAnchored
import PLAStochastic.Index.KEP.ReferenceGoodEvent
import PLAStochastic.Index.Endpoint.ReferenceNodes
import PLAStochastic.Index.Endpoint.HyperSegmentMoments
import PLAStochastic.Index.Model.ExpGaps
import PLAStochastic.Index.Model.ExpSequence

/-!
# Lower bound for the ALG-PGM height under Model K

Let `X 0, X 1, …` be iid with a Model K law (`DensityK f A B fmin fmax Lf`) and let `H` be the
height of ALG-PGM on the `N` sorted samples (`epHeight eps (kKeys X N ω) N`).  Write
`m ℓ = lcount expSeqMeasure (epLayerSeq eps expCoord ℓ)` for the mean layer-`ℓ` count of the
reference endpoint hierarchy of iid `Exp(1)` gaps.

* **Explicit bound** (`kepLowDelta`): the sum of the failure bound of the reference good event
  (`measureReal_not_refGood_le` with the class constants of iid `Exp(1)` gaps), the Gamma
  lower tail `exp (-N / 6)` and the reference leading-pivot tail `CK exp (-θK s / m L)`.
* **Per anchor** (`measureReal_le_layerPivot_anchPairs_le_kepLowDelta`): for every anchor
  value `0 ≤ v < 1`, the anchored leading layer-`L` pivot is at least `N` with probability at
  most `kepLowDelta`.
* **Height tail** (`measureReal_epHeight_kKeys_le_le`): `P(H ≤ L) ≤ kepLowDelta`, through the
  lower-bound bridge `measure_epHeight_kKeys_le_le_iSup_anchPairs`.
* **Expected height** (`integral_epHeight_kKeys_ge`): `(L + 1) (1 - kepLowDelta) ≤ E H`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-- The explicit bound `δLow` for `P(H ≤ L)`: the failure bound of the reference good event
for iid `Exp(1)` gaps (class constants `vmin = vIn 1 1`, `Kc = KcIn`), plus the Gamma lower
tail `exp (-N / 6)`, plus the reference leading-pivot tail `CK exp (-θK s / m L)`. -/
def kepLowDelta (eps : ℝ) (N L s j : ℕ) (u : ℕ → ℝ) (R : ℕ → ℕ) (lamG lamN : ℝ) : ℝ :=
  (∑ ℓ ∈ range L, (Real.exp (-(R ℓ / (16 * KcIn))) +
      R ℓ * (refMargin (vIn 1 1) eps (refK expSeqMeasure eps expCoord ℓ) (u ℓ) +
        (71 / 72 : ℝ) ^ j + CK * Real.exp (-(θK * lamG / 2)) +
        CK * Real.exp (-(θK * lamN))))) +
    Real.exp (-((N : ℝ) / 6)) +
    CK * Real.exp (-(θK * (s / lcount expSeqMeasure (epLayerSeq eps expCoord L))))

variable {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-- **Per-anchor bound.**  For every anchor value `0 ≤ v < 1`, the anchored canonical model
with `N - 1` further keys has leading layer-`L` pivot at least `N` with probability at most
`kepLowDelta`. -/
theorem measureReal_le_layerPivot_anchPairs_le_kepLowDelta (hf : DensityK f A B fmin fmax Lf)
    {eps : ℝ} (heps : epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps)
    {N L s Tmax j d : ℕ} {u Gmax : ℕ → ℝ} {R : ℕ → ℕ} {lamG lamN : ℝ} (hsN : s < N)
    (hu : ∀ ℓ < L, 0 < u ℓ ∧ u ℓ ≤ 1 / 2)
    (hRs : ∀ ℓ < L,
      32 * KcIn * s ≤ R ℓ * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)))
    (hTmax : j * refLen eps (vIn 1 1) ≤ Tmax)
    (hGmax : ∀ ℓ < L, lamG * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ Gmax ℓ)
    (hd : ∀ ℓ < L,
      (s : ℝ) + lamN * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ d)
    (hΨ : ∀ ℓ < L, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    expSeqMeasure.real {ω | N ≤ layerPivot eps (anchPairs (quantK f A B) v (N - 1) ω) L 1} ≤
      kepLowDelta eps N L s j u R lamG lamN := by
  have H := RefHyp.of_gapLaw (gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)) heps
  have h1 : (1 : ℝ) ≤ eps := H.one_le_eps
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNr : ((N - 1 : ℕ) : ℝ) + 1 = N := by
    rw [Nat.cast_sub hN1, Nat.cast_one]
    ring
  have hanch : 1 - v ≤ 2 * (((N - 1 : ℕ) : ℝ) + 1) / N := by
    rw [hNr, mul_div_assoc, div_self hNpos.ne']
    linarith
  have ha := measureReal_le_layerPivot_anchPairs_le_refGood' (s := s) (L_top := L) hf hv0 hv1
    hanch (by linarith) (by omega)
    (fun ℓ hℓ => ⟨(hu ℓ hℓ).1.le, by linarith [(hu ℓ hℓ).2]⟩) hΨ le_rfl hsN
  rw [hNr] at ha
  have hG := measureReal_not_refGood'_le expSeqMeasure eps expCoord L s d Tmax u Gmax
  have hG2 := measureReal_not_refGood_le iidSeq_expCoord (hasLaw_expCoord 0) H hu hRs hTmax
    hGmax hd
  have hT : expSeqMeasure.real {ω | s < layerPivot eps (refPairsE ω) L 1} ≤
      CK * Real.exp (-(θK * (s / lcount expSeqMeasure (epLayerSeq eps expCoord L)))) := by
    have hm := H.lcount_pos L
    refine le_trans (measureReal_mono fun ω hω => ?_)
      (measureReal_refSpan_gt_le H L 0 (s / lcount expSeqMeasure (epLayerSeq eps expCoord L)))
    simp only [Set.mem_ofPred_eq, layerPivot_refPairsE_one] at hω ⊢
    rw [div_mul_cancel₀ _ hm.ne']
    exact_mod_cast hω
  unfold kepLowDelta
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Height tail.**  ALG-PGM on `N` sorted Model K samples has height at most `L` with
probability at most `kepLowDelta`. -/
theorem measureReal_epHeight_kKeys_le_le (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps : ℝ} (heps : epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps)
    {N L s Tmax j d : ℕ} {u Gmax : ℕ → ℝ} {R : ℕ → ℕ} {lamG lamN : ℝ} (hL : 1 ≤ L)
    (hsN : s < N)
    (hu : ∀ ℓ < L, 0 < u ℓ ∧ u ℓ ≤ 1 / 2)
    (hRs : ∀ ℓ < L,
      32 * KcIn * s ≤ R ℓ * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)))
    (hTmax : j * refLen eps (vIn 1 1) ≤ Tmax)
    (hGmax : ∀ ℓ < L, lamG * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ Gmax ℓ)
    (hd : ∀ ℓ < L,
      (s : ℝ) + lamN * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ d)
    (hΨ : ∀ ℓ < L, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ) :
    P.real {ω | epHeight eps (kKeys X N ω) N ≤ L} ≤ kepLowDelta eps N L s j u R lamG lamN := by
  have H := RefHyp.of_gapLaw (gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)) heps
  have h1 : (1 : ℝ) ≤ eps := H.one_le_eps
  have hanch : ∀ v ∈ Set.Ico (0 : ℝ) 1,
      expSeqMeasure.real {ω | N ≤ layerPivot eps (anchPairs (quantK f A B) v (N - 1) ω) L 1} ≤
        kepLowDelta eps N L s j u R lamG lamN := fun v hv =>
    measureReal_le_layerPivot_anchPairs_le_kepLowDelta hf heps hsN hu hRs hTmax hGmax hd hΨ
      hv.1 hv.2
  have hnn : 0 ≤ kepLowDelta eps N L s j u R lamG lamN :=
    measureReal_nonneg.trans (hanch 0 ⟨le_rfl, one_pos⟩)
  refine ENNReal.toReal_le_of_le_ofReal hnn
    ((measure_epHeight_kKeys_le_le_iSup_anchPairs hf hX hind (by linarith) (by omega) hL).trans
      (iSup₂_le fun v hv => ?_))
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hanch v hv)

/-- **Expected height.**  `(L + 1) (1 - kepLowDelta) ≤ E H` for the height `H` of ALG-PGM on
`N` sorted Model K samples. -/
theorem integral_epHeight_kKeys_ge (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps : ℝ} (heps : epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps)
    {N L s Tmax j d : ℕ} {u Gmax : ℕ → ℝ} {R : ℕ → ℕ} {lamG lamN : ℝ} (hL : 1 ≤ L)
    (hsN : s < N)
    (hu : ∀ ℓ < L, 0 < u ℓ ∧ u ℓ ≤ 1 / 2)
    (hRs : ∀ ℓ < L,
      32 * KcIn * s ≤ R ℓ * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)))
    (hTmax : j * refLen eps (vIn 1 1) ≤ Tmax)
    (hGmax : ∀ ℓ < L, lamG * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ Gmax ℓ)
    (hd : ∀ ℓ < L,
      (s : ℝ) + lamN * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ d)
    (hΨ : ∀ ℓ < L, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ) :
    ((L : ℝ) + 1) * (1 - kepLowDelta eps N L s j u R lamG lamN) ≤
      ∫ ω, (epHeight eps (kKeys X N ω) N : ℝ) ∂P := by
  have H := RefHyp.of_gapLaw (gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)) heps
  have h1 : (1 : ℝ) ≤ eps := H.one_le_eps
  have hN1 : 1 ≤ N := by omega
  have := isProbabilityMeasure_densityLaw hf
  have : IsProbabilityMeasure P := (hX 0).isProbabilityMeasure
  have hlow := measureReal_epHeight_kKeys_le_le hf hX hind heps hL hsN hu hRs hTmax hGmax hd hΨ
  set h : Ω → ℝ := fun ω => (epHeight eps (kKeys X N ω) N : ℝ) with hdef
  have hmeas : AEMeasurable h P :=
    measurable_from_nat.comp_aemeasurable ((measurable_epHeight_extendKeys eps N).comp_aemeasurable
      (Renyi.measurable_sortVec.comp_aemeasurable
        (aemeasurable_pi_lambda _ fun i => (hX i).aemeasurable)))
  set C : ℕ := 0 + Nat.log (⌊2 * eps⌋₊ + 1) N + 1
  have hbd : ∀ ω, ‖h ω‖ ≤ C := fun ω => by
    rw [hdef, Real.norm_natCast]
    exact_mod_cast epHeight_le_add_log h1 (kKeys X N ω) hN1 0
  have hint : Integrable h P := Integrable.of_bound hmeas.aestronglyMeasurable C (ae_of_all _ hbd)
  have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => Nat.cast_nonneg _) hint
    ((L : ℝ) + 1)
  have hU : 1 ≤ P.real {ω | epHeight eps (kKeys X N ω) N ≤ L} +
      P.real {ω | (L : ℝ) + 1 ≤ h ω} := by
    calc (1 : ℝ) = P.real Set.univ := by simp
      _ ≤ P.real ({ω | epHeight eps (kKeys X N ω) N ≤ L} ∪ {ω | (L : ℝ) + 1 ≤ h ω}) := by
          refine measureReal_mono (fun ω _ => ?_)
          rcases le_or_gt (epHeight eps (kKeys X N ω) N) L with hle | hgt
          · exact Or.inl hle
          · refine Or.inr ?_
            change (L : ℝ) + 1 ≤ (epHeight eps (kKeys X N ω) N : ℝ)
            exact_mod_cast hgt
      _ ≤ _ := measureReal_union_le _ _
  have hL0 : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
  calc ((L : ℝ) + 1) * (1 - kepLowDelta eps N L s j u R lamG lamN)
      ≤ ((L : ℝ) + 1) * P.real {ω | (L : ℝ) + 1 ≤ h ω} :=
        mul_le_mul_of_nonneg_left (by linarith) hL0
    _ ≤ ∫ ω, h ω ∂P := hM

end

end PGM
