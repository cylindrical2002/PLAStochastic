import PLAStochastic.Index.KEP.PivotTrials
import PLAStochastic.Index.KEP.AnchoredCoupling
import PLAStochastic.Index.KEP.SampleToAnchored
import PLAStochastic.Index.KEP.ReferenceGoodEvent
import PLAStochastic.Index.Endpoint.ReferenceNodes
import PLAStochastic.Index.Algorithm.EndpointTop
import PLAStochastic.Index.KEP.GoodAnchor
import PLAStochastic.Index.Model.ExpGaps

/-!
# Upper bound for the ALG-PGM height under Model K

Source: `proofs/proofK_endpoint_scale.tex`, proof of `ksc:thm:endpoint-scale`, part
"Upper bound before a deterministic horizon".

Let `X 0, X 1, …` be iid with a Model K law (`DensityK f A B fmin fmax Lf`), `Q = quantK f A B`,
and let `H = epHeight eps (kKeys X N ω) N` be the height of ALG-PGM on the `N` sorted samples.
Write `m ℓ = lcount expSeqMeasure (epLayerSeq eps expCoord ℓ)` for the mean layer-`ℓ` count of
the reference endpoint hierarchy of iid `Exp(1)` gaps and `q = ⌊2 eps⌋₊ + 1`.  Fix a horizon
`𝔥 ≤ N - 1`, a target gap `1 ≤ gap₀ ≤ m L / 2 + 1` and `D ≤ N - 𝔥`.

* **Trial success** (`ofReal_kepTrialProb_le_orderLaw`).  At a rank `r < 𝔥` with a good anchor
  value `0 ≤ a`, the anchored leading layer-`L` pivot is at least `min gap₀ (𝔥 - r)` with
  probability at least `kepTrialProb = 1 / (4 KcIn) - kepRefDelta - exp (-(N - 𝔥) / 6)`:
  Paley–Zygmund for the leading reference count (`measureReal_count_gt_half_ge`), the anchored
  coupling (`measureReal_lt_layerPivot_anchPairs_ge_refGood'`) and the failure bound of the
  reference good event (`measureReal_not_refGood_le`, `kepRefDelta`).
* **Expected layer size** (`integral_epLayer_snd_quantK_le`): `E[layer-L size] ≤ kepLayerUp`,
  the bound `(𝔥 / gap₀ + 2) / p + (N / q^L + 1) P(goodAnchorsᶜ) + (N - 𝔥) / q^L + 1` of
  `integral_epLayer_snd_le` with `p = kepTrialProb`.  That theorem asks for the trial success
  bound only at nonnegative anchor values, where the anchored coupling applies.
* **Expected height** (`integral_epHeight_kKeys_le`): `E H ≤ L + log kepLayerUp / log q + 1`,
  through `integral_epHeight_kKeys_eq_orderLaw` and `integral_epHeight_le`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-- The failure bound of the reference good event for iid `Exp(1)` gaps
(`measureReal_not_refGood_le` with `vmin = vIn 1 1`, `Kc = KcIn`). -/
def kepRefDelta (eps : ℝ) (L j : ℕ) (u : ℕ → ℝ) (R : ℕ → ℕ) (lamG lamN : ℝ) : ℝ :=
  ∑ ℓ ∈ range L, (Real.exp (-(R ℓ / (16 * KcIn))) +
    R ℓ * (refMargin (vIn 1 1) eps (refK expSeqMeasure eps expCoord ℓ) (u ℓ) +
      (71 / 72 : ℝ) ^ j + CK * Real.exp (-(θK * lamG / 2)) +
      CK * Real.exp (-(θK * lamN))))

/-- The trial success probability: the Paley–Zygmund bound `1 / (4 KcIn)` for a large leading
reference count, minus the failure bound of the reference good event and the Gamma lower
tail `exp (-(N - 𝔥) / 6)`. -/
def kepTrialProb (eps : ℝ) (N L 𝔥 j : ℕ) (u : ℕ → ℝ) (R : ℕ → ℕ) (lamG lamN : ℝ) : ℝ :=
  1 / (4 * KcIn) - kepRefDelta eps L j u R lamG lamN - Real.exp (-(((N - 𝔥 : ℕ) : ℝ) / 6))

/-- The bound on the expected layer-`L` size: `integral_epLayer_snd_le` with the trial success
probability `kepTrialProb`, `q = ⌊2 eps⌋₊ + 1`. -/
def kepLayerUp (eps : ℝ) (N L 𝔥 gap₀ D j : ℕ) (u : ℕ → ℝ) (R : ℕ → ℕ) (lamG lamN : ℝ) : ℝ :=
  ((𝔥 : ℝ) / gap₀ + 2) / kepTrialProb eps N L 𝔥 j u R lamG lamN +
    ((N : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1) * (Renyi.orderLaw N (goodAnchors N D)ᶜ).toReal +
    ((N : ℝ) - 𝔥) / (⌊2 * eps⌋₊ + 1 : ℝ) ^ L + 1

variable {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-- **Trial success.**  At a rank `r < 𝔥 ≤ N - 1` with `r + 1 + m = N` and a good anchor value
`0 ≤ a`, the anchored pairs with `m` further sorted uniforms have leading layer-`L` pivot at
least `min gap₀ (𝔥 - r)` with probability at least `kepTrialProb`. -/
theorem ofReal_kepTrialProb_le_orderLaw (hf : DensityK f A B fmin fmax Lf)
    {eps : ℝ} (heps : epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps)
    {N L 𝔥 gap₀ Tmax j d : ℕ} {u Gmax : ℕ → ℝ} {R : ℕ → ℕ} {lamG lamN : ℝ}
    (h𝔥 : 𝔥 ≤ N - 1) (hgap : 1 ≤ gap₀)
    (hgapL : (gap₀ : ℝ) ≤ lcount expSeqMeasure (epLayerSeq eps expCoord L) / 2 + 1)
    (hu : ∀ ℓ < L, 0 < u ℓ ∧ u ℓ ≤ 1 / 2)
    (hRs : ∀ ℓ < L,
      32 * KcIn * gap₀ ≤ R ℓ * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)))
    (hTmax : j * refLen eps (vIn 1 1) ≤ Tmax)
    (hGmax : ∀ ℓ < L, lamG * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ Gmax ℓ)
    (hd : ∀ ℓ < L,
      (gap₀ : ℝ) + lamN * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ d)
    (hΨ : ∀ ℓ < L, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ)
    {r m : ℕ} (hr : r < 𝔥) (hrm : r + 1 + m = N) {a : ℝ} (ha0 : 0 ≤ a)
    (haL : ((N - r : ℕ) : ℝ) / (2 * N) ≤ 1 - a) (haU : 1 - a ≤ 2 * ((N - r : ℕ) : ℝ) / N) :
    ENNReal.ofReal (kepTrialProb eps N L 𝔥 j u R lamG lamN) ≤
      Renyi.orderLaw m
        {w | min gap₀ (𝔥 - r) ≤ layerPivot eps (anchPairsW (quantK f A B) a w) L 1} := by
  have H := RefHyp.of_gapLaw (gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)) heps
  have h1 : (1 : ℝ) ≤ eps := H.one_le_eps
  have hKc : (0 : ℝ) < KcIn := H.Kc_pos
  set x := min gap₀ (𝔥 - r) with hx
  set s := x - 1 with hs
  have hx1 : 1 ≤ x := le_min hgap (by omega)
  have hxs : x = s + 1 := by omega
  have hsm : s ≤ m := by omega
  have hsg : s ≤ gap₀ := by omega
  have hsg' : (s : ℝ) + 1 ≤ gap₀ := by exact_mod_cast (show s + 1 ≤ gap₀ by omega)
  have ha1 : a < 1 := AnchorGood.lt_one (N := N) (r := r) (by omega) ⟨haL, haU⟩
  have hNr : ((N - r : ℕ) : ℝ) = (m : ℝ) + 1 := by
    rw [show N - r = m + 1 by omega]
    push_cast
    ring
  have hanch : 1 - a ≤ 2 * ((m : ℝ) + 1) / N := by rwa [hNr] at haU
  -- (b) of the anchored coupling
  have hb := measureReal_lt_layerPivot_anchPairs_ge_refGood' (s := s) (L_top := L) hf ha0 ha1
    hanch (by linarith) hsm (fun ℓ hℓ => ⟨(hu ℓ hℓ).1.le, by linarith [(hu ℓ hℓ).2]⟩) hΨ
    (L := L) le_rfl
  -- the reference good event
  have hG := measureReal_not_refGood'_le expSeqMeasure eps expCoord L s d Tmax u Gmax
  have hG2 := measureReal_not_refGood_le iidSeq_expCoord (hasLaw_expCoord 0) H (s := s) (d := d)
    hu (fun ℓ hℓ => le_trans (by gcongr) (hRs ℓ hℓ)) hTmax hGmax
    (fun ℓ hℓ => le_trans (by linarith) (hd ℓ hℓ))
  -- the reference leading pivot
  have hPZ := measureReal_count_gt_half_ge (H.layerOK L) hKc 0
  have hR : expSeqMeasure.real
      {ω | 1 / 2 * lcount expSeqMeasure (epLayerSeq eps expCoord L) <
        ((epLayerSeq eps expCoord L 0 ω).2 : ℝ)} ≤
      expSeqMeasure.real {ω | s < layerPivot eps (refPairsE ω) L 1} := by
    refine measureReal_mono fun ω hω => ?_
    simp only [Set.mem_ofPred_eq, layerPivot_refPairsE_one] at hω ⊢
    have : (s : ℝ) < ((epLayerSeq eps expCoord L 0 ω).2 : ℝ) := by linarith
    exact_mod_cast this
  -- the Gamma tail
  have hE : Real.exp (-(((m : ℝ) + 1) / 6)) ≤ Real.exp (-(((N - 𝔥 : ℕ) : ℝ) / 6)) := by
    refine Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_right ?_ (by norm_num)))
    have : N - 𝔥 ≤ m + 1 := by omega
    exact_mod_cast this
  -- the canonical realisation
  have hset : Renyi.orderLaw m
      {w | x ≤ layerPivot eps (anchPairsW (quantK f A B) a w) L 1} =
      expSeqMeasure {ω | s < layerPivot eps (anchPairs (quantK f A B) a m ω) L 1} := by
    refine (orderLaw_anchPairsW_mem_eq_expSeqMeasure (measurable_quantK hf) a m
      (measurableSet_le_layerPivot eps x L 1)).trans ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, hxs]
    omega
  rw [hset, ← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold kepTrialProb kepRefDelta
  linarith

/-! ## The expected layer size and the expected height -/

section Height

/-- **Expected layer-`L` size.**  Under `orderLaw N`, the expected size of layer `L` of ALG-PGM
on the keys `quantK f A B ∘ v` is at most `kepLayerUp`. -/
theorem integral_epLayer_snd_quantK_le (hf : DensityK f A B fmin fmax Lf)
    {eps : ℝ} (heps : epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps)
    {N L 𝔥 gap₀ D Tmax j d : ℕ} {u Gmax : ℕ → ℝ} {R : ℕ → ℕ} {lamG lamN : ℝ}
    (h𝔥 : 𝔥 ≤ N - 1) (hgap : 1 ≤ gap₀)
    (hgapL : (gap₀ : ℝ) ≤ lcount expSeqMeasure (epLayerSeq eps expCoord L) / 2 + 1)
    (hD : D ≤ N - 𝔥)
    (hu : ∀ ℓ < L, 0 < u ℓ ∧ u ℓ ≤ 1 / 2)
    (hRs : ∀ ℓ < L,
      32 * KcIn * gap₀ ≤ R ℓ * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)))
    (hTmax : j * refLen eps (vIn 1 1) ≤ Tmax)
    (hGmax : ∀ ℓ < L, lamG * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ Gmax ℓ)
    (hd : ∀ ℓ < L,
      (gap₀ : ℝ) + lamN * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ d)
    (hΨ : ∀ ℓ < L, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ)
    (hp : 0 < kepTrialProb eps N L 𝔥 j u R lamG lamN) :
    ∫ v, ((epLayer eps (extendKeys (quantK f A B ∘ v)) N L).2 : ℝ) ∂(Renyi.orderLaw N) ≤
      kepLayerUp eps N L 𝔥 gap₀ D j u R lamG lamN := by
  have H := RefHyp.of_gapLaw (gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)) heps
  have h1 : (1 : ℝ) ≤ eps := H.one_le_eps
  exact integral_epLayer_snd_le (measurable_quantK hf) (by linarith) (by omega) hgap
    hD hp fun r hr m hrm a haL haU ha0 =>
      ofReal_kepTrialProb_le_orderLaw hf heps h𝔥 hgap hgapL hu hRs hTmax hGmax hd hΨ hr hrm ha0
        haL haU

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Expected height.**  For ALG-PGM on `N` sorted Model K samples,
`E H ≤ L + log (kepLayerUp) / log q + 1`, `q = ⌊2 eps⌋₊ + 1`. -/
theorem integral_epHeight_kKeys_le (hf : DensityK f A B fmin fmax Lf)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {eps : ℝ} (heps : epsK (bIn 1 1) (βIn 1 (lkap expSeqMeasure (inputPairs expCoord))) ≤ eps)
    {N L 𝔥 gap₀ D Tmax j d : ℕ} {u Gmax : ℕ → ℝ} {R : ℕ → ℕ} {lamG lamN : ℝ}
    (hN : 1 ≤ N) (h𝔥 : 𝔥 ≤ N - 1) (hgap : 1 ≤ gap₀)
    (hgapL : (gap₀ : ℝ) ≤ lcount expSeqMeasure (epLayerSeq eps expCoord L) / 2 + 1)
    (hD : D ≤ N - 𝔥)
    (hu : ∀ ℓ < L, 0 < u ℓ ∧ u ℓ ≤ 1 / 2)
    (hRs : ∀ ℓ < L,
      32 * KcIn * gap₀ ≤ R ℓ * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)))
    (hTmax : j * refLen eps (vIn 1 1) ≤ Tmax)
    (hGmax : ∀ ℓ < L, lamG * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ Gmax ℓ)
    (hd : ∀ ℓ < L,
      (gap₀ : ℝ) + lamN * lcount expSeqMeasure (epLayerSeq eps expCoord (ℓ + 1)) ≤ d)
    (hΨ : ∀ ℓ < L, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ)
    (hp : 0 < kepTrialProb eps N L 𝔥 j u R lamG lamN) :
    ∫ ω, (epHeight eps (kKeys X N ω) N : ℝ) ∂P ≤
      L + Real.log (kepLayerUp eps N L 𝔥 gap₀ D j u R lamG lamN) /
        Real.log (⌊2 * eps⌋₊ + 1) + 1 := by
  have H := RefHyp.of_gapLaw (gapLaw_exp iidSeq_expCoord (hasLaw_expCoord 0)) heps
  have h1 : (1 : ℝ) ≤ eps := H.one_le_eps
  rw [integral_epHeight_kKeys_eq_orderLaw hf hX hind eps N]
  have hkeys : Measurable fun v : Fin N → ℝ => extendKeys (quantK f A B ∘ v) :=
    measurable_extendKeys.comp
      (measurable_pi_lambda _ fun i => (measurable_quantK hf).comp (measurable_pi_apply i))
  refine (integral_epHeight_le h1 hkeys hN L).trans ?_
  have hlay := integral_epLayer_snd_quantK_le hf heps h𝔥 hgap hgapL hD hu hRs hTmax hGmax hd hΨ hp
  -- the expected layer size is at least one
  set S : (Fin N → ℝ) → ℝ := fun v => ((epLayer eps (extendKeys (quantK f A B ∘ v)) N L).2 : ℝ)
    with hSdef
  have hSm : Measurable S :=
    measurable_from_nat.comp (measurable_snd.comp ((measurable_epLayer eps N L).comp hkeys))
  have hSint : Integrable S (Renyi.orderLaw N) :=
    Integrable.of_bound hSm.aestronglyMeasurable N (ae_of_all _ fun v => by
      rw [hSdef, Real.norm_natCast]
      exact_mod_cast epLayer_snd_le h1 _ N L)
  have hS1 : (1 : ℝ) ≤ ∫ v, S v ∂(Renyi.orderLaw N) := by
    have h := integral_mono (integrable_const (1 : ℝ)) hSint fun v => by
      change (1 : ℝ) ≤ ((epLayer eps (extendKeys (quantK f A B ∘ v)) N L).2 : ℝ)
      exact_mod_cast one_le_epLayer_snd (eps := eps) _ hN L
    simpa using h
  have hc : 0 ≤ Real.log (⌊2 * eps⌋₊ + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌊2 * eps⌋₊)])
  have hlog := Real.log_le_log (by linarith) hlay
  have := div_le_div_of_nonneg_right hlog hc
  linarith

end Height

end

end PGM
