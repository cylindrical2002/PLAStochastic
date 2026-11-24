import PLAStochastic.Index.KEP.AnchoredSample
import PLAStochastic.Index.KEP.ReferenceGoodEvent
import PLAStochastic.Index.KEP.PathwiseCoupling
import PLAStochastic.Index.KEP.GoodAnchor
import PLAStochastic.Index.ModelK.Density
import PLAStochastic.Index.Model.ExpSequence
import PLAStochastic.Index.Model.ExpGaps
import PLAStochastic.Index.KRE.FixedParameter

/-!
# Coupling the anchored Model K sample with its affine reference

On the canonical exponential sequence space (`expSeqMeasure`, coordinates `ω i` iid
`Exp(1)`), write `Γ t = ∑_{i<t} ω i = pairKeys (refPairsE ω) t` and `S = Γ (M + 1)`.  For a
Model K quantile `Q = quantK f A B` and an anchor value `0 ≤ v < 1`, the anchored base pairs
`anchPairs Q v M ω` are compared with the affine reference `refPairsE ω`.

* **Curve identity** (`pairKeys_anchPairs`).  For `t ≤ M`,
  `pairKeys (anchPairs Q v M ω) t = φ (Γ t / S) - φ 0` with `φ = anchCurve Q v`,
  `φ w = Q (v + (1 - v) w)` (pathwise, no positivity needed).
* **Analytic data of `φ` on `[0, 1]`** (`hasDerivWithinAt_anchCurve`, `anchCurve_deriv_lip`,
  `anchCurve_deriv_ge`, `anchCurve_ratio`): `φ' w = (1 - v) / f (Q (v + (1 - v) w))`, with
  Lipschitz constant `Lφ = (1 - v)² (Lf / fmin³ + 1)` and lower bound `δφ = (1 - v) / fmax`,
  so `Lφ / (2 δφ) = (1 - v) (Lf / fmin³ + 1) fmax / 2`.
* **Good event without the rank span** (`refGood'`): the coupling
  `layerPivot_coupling_of_le` of `PLAStochastic.Index.KEP.PathwiseCoupling` needs, besides `s ≤ d`, only the families
  (M), (T), (G) of `refGood`; `refGood'` is their conjunction (independent of `d`), bounded by
  `measureReal_not_refGood_le` through `measureReal_not_refGood'_le` for any `d`.
* **The anchored coupling** (`agree_anchPairs`, `measureReal_not_agree_le`).  If
  `1 - v ≤ 2 (M + 1) / N`, `s ≤ M`, `0 ≤ u ℓ ≤ eps` and
  `(Tmax + 1 + 2 (eps + u ℓ)) (2 (Lf / fmin³ + 1) fmax) Gmax ℓ / N ≤ u ℓ` for `ℓ < L_top`, then
  `P(¬ agree) ≤ P(¬ refGood') + exp (-(M + 1) / 6)`, where `agree` is the agreement of the
  two hierarchies through layer `L_top` at the positions `≤ s`.  The exponential term is the
  Gamma lower tail `P(S ≤ (M + 1) / 2)`, off which `(1 - v) / S ≤ 4 / N`.
* **Leading-pivot consequences** (`measureReal_le_layerPivot_anchPairs_le`,
  `measureReal_lt_layerPivot_anchPairs_ge` and their `refGood'` forms); the reference leading
  pivot is `(epLayerSeq eps expCoord L 0 ω).2` (`layerPivot_refPairsE_one`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

/-! ## The curve identity -/

section Curve

/-- The anchored curve `φ w = Q (u + (1 - u) w)`. -/
def anchCurve (Q : ℝ → ℝ) (u w : ℝ) : ℝ := Q (u + (1 - u) * w)

theorem pairKeys_refPairsE (ω : ℕ → ℝ) (t : ℕ) :
    pairKeys (refPairsE ω) t = ∑ i ∈ range t, ω i := rfl

/-- The Rényi partial sums are the reference keys. -/
theorem gammaSum_eq_pairKeys (ω : ℕ → ℝ) {M : ℕ} :
    ∀ t ≤ M + 1, Renyi.gammaSum (fun i : Fin (M + 1) => ω i) t = pairKeys (refPairsE ω) t
  | 0, _ => by rw [Renyi.gammaSum_zero]; rfl
  | t + 1, ht => by
    have h := Renyi.gammaSum_succ (fun i : Fin (M + 1) => ω i) ⟨t, by omega⟩
    simp only at h
    rw [h, gammaSum_eq_pairKeys ω t (by omega), pairKeys_refPairsE, pairKeys_refPairsE,
      sum_range_succ]

theorem anchPos_zero {M : ℕ} (w : Fin M → ℝ) : anchPos w 0 = 0 := by
  simp [anchPos]

/-- Telescoping: the anchored keys below the base rank `M`. -/
theorem pairKeys_anchPairsW (Q : ℝ → ℝ) (u : ℝ) {M : ℕ} (w : Fin M → ℝ) :
    ∀ t ≤ M, pairKeys (anchPairsW Q u w) t =
      Q (u + (1 - u) * anchPos w t) - Q (u + (1 - u) * anchPos w 0)
  | 0, _ => by simp [pairKeys]
  | t + 1, ht => by
    have ih := pairKeys_anchPairsW Q u w t (by omega)
    simp only [pairKeys] at ih ⊢
    rw [sum_range_succ, ih]
    simp only [anchPairsW, if_pos (show t < M by omega)]
    ring

/-- The anchored positions are the normalized reference keys. -/
theorem anchPos_gammaRatio (ω : ℕ → ℝ) {M : ℕ} {t : ℕ} (ht : t ≤ M) :
    anchPos (Renyi.gammaRatio (fun i : Fin (M + 1) => ω i)) t =
      pairKeys (refPairsE ω) t / pairKeys (refPairsE ω) (M + 1) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [anchPos_zero, pairKeys_refPairsE, sum_range_zero, zero_div]
  · rw [anchPos, dif_pos ⟨ht0, ht⟩, Renyi.gammaRatio]
    simp only
    rw [Nat.sub_add_cancel ht0, gammaSum_eq_pairKeys ω t (by omega),
      gammaSum_eq_pairKeys ω (M + 1) le_rfl]

/-- **The curve identity.**  Up to the base rank `M`, the anchored keys are the curve
`φ = anchCurve Q u` evaluated at the normalized reference keys `Γ t / Γ (M + 1)`, shifted
by `φ 0`. -/
theorem pairKeys_anchPairs (Q : ℝ → ℝ) (u : ℝ) (M : ℕ) (ω : ℕ → ℝ) {t : ℕ} (ht : t ≤ M) :
    pairKeys (anchPairs Q u M ω) t =
      anchCurve Q u (pairKeys (refPairsE ω) t / pairKeys (refPairsE ω) (M + 1)) -
        anchCurve Q u 0 := by
  rw [anchPairs, pairKeys_anchPairsW Q u _ t ht, anchPos_gammaRatio ω ht, anchPos_zero]
  rfl

end Curve

/-! ## Analytic data of the anchored curve -/

section Analytic

variable {f : ℝ → ℝ} {A B fmin fmax Lf v : ℝ}

theorem anchor_mem_Icc (hv0 : 0 ≤ v) (hv1 : v ≤ 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    v + (1 - v) * x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  have h1 : 0 ≤ 1 - v := by linarith
  constructor
  · nlinarith
  · nlinarith

/-- The derivative of the anchored curve: `φ' x = (1 - v) / f (Q (v + (1 - v) x))`. -/
theorem hasDerivWithinAt_anchCurve (hf : DensityK f A B fmin fmax Lf) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (anchCurve (quantK f A B) v)
        ((1 - v) * (1 / f (quantK f A B (v + (1 - v) * x)))) (Set.Icc 0 1) x := by
  intro x hx
  have hg : HasDerivWithinAt (fun y : ℝ => v + (1 - v) * y) ((1 - v) * 1) (Set.Icc 0 1) x :=
    (((hasDerivAt_id x).const_mul (1 - v)).const_add v).hasDerivWithinAt
  have h := HasDerivWithinAt.comp x (kre_quantK_deriv hf _ (anchor_mem_Icc hv0 hv1 hx)) hg
    (fun y hy => anchor_mem_Icc hv0 hv1 hy)
  rw [mul_one, mul_comm] at h
  exact h

/-- The derivative of the anchored curve is `(1 - v)² (Lf / fmin³ + 1)`-Lipschitz. -/
theorem anchCurve_deriv_lip (hf : DensityK f A B fmin fmax Lf) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |(1 - v) * (1 / f (quantK f A B (v + (1 - v) * x))) -
          (1 - v) * (1 / f (quantK f A B (v + (1 - v) * y)))| ≤
        (1 - v) ^ 2 * (Lf / fmin ^ 3 + 1) * |x - y| := by
  intro x hx y hy
  have h1 : 0 ≤ 1 - v := by linarith
  have hL := kre_quantK_lip hf _ (anchor_mem_Icc hv0 hv1 hx) _ (anchor_mem_Icc hv0 hv1 hy)
  have e : v + (1 - v) * x - (v + (1 - v) * y) = (1 - v) * (x - y) := by ring
  rw [e, abs_mul, abs_of_nonneg h1] at hL
  rw [← mul_sub, abs_mul, abs_of_nonneg h1]
  calc (1 - v) * |1 / f (quantK f A B (v + (1 - v) * x)) -
        1 / f (quantK f A B (v + (1 - v) * y))|
      ≤ (1 - v) * ((Lf / fmin ^ 3 + 1) * ((1 - v) * |x - y|)) :=
        mul_le_mul_of_nonneg_left hL h1
    _ = (1 - v) ^ 2 * (Lf / fmin ^ 3 + 1) * |x - y| := by ring

/-- The curvature ratio `Lφ / (2 δφ)` of the anchored curve. -/
theorem anchCurve_ratio (hf : DensityK f A B fmin fmax Lf) (hv1 : v < 1) :
    (1 - v) ^ 2 * (Lf / fmin ^ 3 + 1) / (2 * ((1 - v) * (1 / fmax))) =
      (1 - v) * (Lf / fmin ^ 3 + 1) * fmax / 2 := by
  have h1 : 1 - v ≠ 0 := by linarith
  have h2 := hf.fmax_pos.ne'
  field_simp

/-- The derivative of the anchored curve is at least `(1 - v) / fmax`. -/
theorem anchCurve_deriv_ge (hf : DensityK f A B fmin fmax Lf) (hv1 : v ≤ 1) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - v) * (1 / fmax) ≤ (1 - v) * (1 / f (quantK f A B (v + (1 - v) * x))) :=
  fun _ _ => mul_le_mul_of_nonneg_left (inv_f_quantK_mem_Icc hf _).1 (by linarith)

end Analytic

/-! ## The events -/

section Events

variable {Ω : Type*}

/-- Agreement of two hierarchies: through layer `L_top`, the pivots at every position where
one of them is at or before `s` coincide. -/
def agree (eps : ℝ) (L_top s : ℕ) (z z' : ℕ → ℝ × ℕ) : Prop :=
  ∀ ℓ ≤ L_top, ∀ j, (layerPivot eps z ℓ j ≤ s ∨ layerPivot eps z' ℓ j ≤ s) →
    layerPivot eps z ℓ j = layerPivot eps z' ℓ j

/-- **The reference good event without the rank-span family**: the families (M) margin,
(T) block length and (G) key span of `refGood`, for the blocks of the layers `ℓ < L_top`
starting before `s`.  It does not depend on a base rank `d`. -/
def refGood' (eps : ℝ) (g : ℕ → Ω → ℝ) (L_top s Tmax : ℕ) (u Gmax : ℕ → ℝ) (ω : Ω) : Prop :=
  (∀ ℓ < L_top, ∀ k, blockPivots eps (seq (inputPairs g) ω) ℓ k 0 < s →
    prefixAffineFeasible (eps - u ℓ)
        (fun i => pairKeys (seq (inputPairs g) ω) (blockPivots eps (seq (inputPairs g) ω) ℓ k i))
        (layerBlockLen eps (seq (inputPairs g) ω) ℓ k) ∧
      ¬ prefixAffineFeasible (eps + u ℓ)
        (fun i => pairKeys (seq (inputPairs g) ω) (blockPivots eps (seq (inputPairs g) ω) ℓ k i))
        (layerBlockLen eps (seq (inputPairs g) ω) ℓ k + 1)) ∧
  (∀ ℓ < L_top, ∀ k, blockPivots eps (seq (inputPairs g) ω) ℓ k 0 < s →
    layerBlockLen eps (seq (inputPairs g) ω) ℓ k ≤ Tmax) ∧
  (∀ ℓ < L_top, ∀ k, blockPivots eps (seq (inputPairs g) ω) ℓ k 0 < s →
    pairKeys (seq (inputPairs g) ω) (blockPivots eps (seq (inputPairs g) ω) ℓ k
        (layerBlockLen eps (seq (inputPairs g) ω) ℓ k)) -
      pairKeys (seq (inputPairs g) ω) (blockPivots eps (seq (inputPairs g) ω) ℓ k 0) ≤ Gmax ℓ)

theorem refGood'_of_refGood {eps : ℝ} {g : ℕ → Ω → ℝ} {L_top s d Tmax : ℕ} {u Gmax : ℕ → ℝ}
    {ω : Ω} (h : refGood eps g L_top s d Tmax u Gmax ω) : refGood' eps g L_top s Tmax u Gmax ω :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- `refGood'` fails at most as often as `refGood` for any base rank `d` (so
`measureReal_not_refGood_le` bounds it, with `d` as large as needed). -/
theorem measureReal_not_refGood'_le [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (eps : ℝ) (g : ℕ → Ω → ℝ) (L_top s d Tmax : ℕ) (u Gmax : ℕ → ℝ) :
    P.real {ω | ¬ refGood' eps g L_top s Tmax u Gmax ω} ≤
      P.real {ω | ¬ refGood eps g L_top s d Tmax u Gmax ω} :=
  measureReal_mono fun _ hω h => hω (refGood'_of_refGood h)

end Events

/-! ## The anchored coupling -/

section Anchored

variable {f : ℝ → ℝ} {A B fmin fmax Lf v : ℝ}

theorem seq_inputPairs_expCoord (ω : ℕ → ℝ) : seq (inputPairs expCoord) ω = refPairsE ω := rfl

/-- The anchored base pairs have finite segments on every layer (zero gaps after `M`). -/
theorem allLayersFinite_anchPairs (eps : ℝ) (Q : ℝ → ℝ) (u : ℝ) (M : ℕ) (ω : ℕ → ℝ) :
    AllLayersFinite eps (anchPairs Q u M ω) :=
  allLayersFinite_of_fst_eq_zero (M := M) fun i hi => by
    change (if i < M then _ else 0) = 0
    rw [if_neg (by omega)]

/-- **Reset coefficient** from the good-anchor bound `1 - v ≤ 2 (M + 1) / N` and a Gamma
total `S ≥ (M + 1) / 2`. -/
theorem reset_coef_le_of_anchor {M N : ℕ} {S : ℝ} (hv1 : v < 1)
    (hanch : 1 - v ≤ 2 * ((M : ℝ) + 1) / N) (hS : ((M : ℝ) + 1) / 2 ≤ S) :
    0 < (N : ℝ) ∧ (1 - v) / S ≤ 4 / N := by
  have hNpos : 0 < (N : ℝ) := by
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at hanch
      linarith
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hSpos : 0 < S := by linarith
  refine ⟨hNpos, ?_⟩
  rw [div_le_div_iff₀ hSpos hNpos]
  have h := (le_div_iff₀ hNpos).1 hanch
  linarith

/-- **Pathwise anchored coupling.**  Let `Q = quantK f A B`, `0 ≤ v < 1` with
`1 - v ≤ 2 (M + 1) / N`, and `s ≤ M`.  For a reference path `ω` with positive coordinates,
finite reference layers, Gamma total `Γ (M + 1) ≥ (M + 1) / 2` and the good event
`refGood'`, the numeric condition
`(Tmax + 1 + 2 (eps + u ℓ)) (2 (Lf / fmin³ + 1) fmax) Gmax ℓ / N ≤ u ℓ` makes the anchored and
the reference hierarchies agree through layer `L_top` at the positions `≤ s`. -/
theorem agree_anchPairs (hf : DensityK f A B fmin fmax Lf) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {M N : ℕ} (hanch : 1 - v ≤ 2 * ((M : ℝ) + 1) / N)
    {eps : ℝ} (heps : 0 ≤ eps) {L_top s Tmax : ℕ} {u Gmax : ℕ → ℝ} (hsM : s ≤ M)
    (hu : ∀ ℓ < L_top, 0 ≤ u ℓ ∧ u ℓ ≤ eps)
    (hΨ : ∀ ℓ < L_top, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ)
    {ω : ℕ → ℝ} (hpos : ∀ i, 0 < ω i) (hfin' : AllLayersFinite eps (refPairsE ω))
    (hS : ((M : ℝ) + 1) / 2 ≤ pairKeys (refPairsE ω) (M + 1))
    (hgood : refGood' eps expCoord L_top s Tmax u Gmax ω) :
    agree eps L_top s (anchPairs (quantK f A B) v M ω) (refPairsE ω) := by
  obtain ⟨hNpos, hcoef⟩ := reset_coef_le_of_anchor hv1 hanch hS
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hSpos : 0 < pairKeys (refPairsE ω) (M + 1) := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hK := kre_quantK_lip_pos hf
  have hfmax := hf.fmax_pos
  have hIcc : Set.Icc 0 (pairKeys (refPairsE ω) M / pairKeys (refPairsE ω) (M + 1)) ⊆
      Set.Icc (0 : ℝ) 1 := by
    refine Set.Icc_subset_Icc le_rfl (div_le_one_of_le₀ ?_ hSpos.le)
    rw [pairKeys_refPairsE, pairKeys_refPairsE, sum_range_succ]
    linarith [hpos M]
  refine layerPivot_coupling_of_le (z := anchPairs (quantK f A B) v M ω) (z' := refPairsE ω)
    (φ := anchCurve (quantK f A B) v)
    (φ' := fun x => (1 - v) * (1 / f (quantK f A B (v + (1 - v) * x))))
    (L := (1 - v) ^ 2 * (Lf / fmin ^ 3 + 1)) (δ := (1 - v) * (1 / fmax)) (d := M)
    heps (fun _ => rfl) (fun _ => rfl) hpos (allLayersFinite_anchPairs eps _ v M ω) hfin'
    Set.ordConnected_Icc hIcc (hasDerivWithinAt_anchCurve hf hv0 hv1.le)
    (anchCurve_deriv_lip hf hv0 hv1.le) (mul_pos h1v (one_div_pos.2 hfmax))
    (anchCurve_deriv_ge hf hv1.le) hSpos (fun t ht => pairKeys_anchPairs _ v M ω ht) hsM hu
    (fun ℓ hℓ => ?_) hgood.1 hgood.2.1 hgood.2.2
  rw [anchCurve_ratio hf hv1]
  have hC : 0 ≤ (Tmax : ℝ) + 1 + 2 * (eps + u ℓ) := by
    linarith [(Nat.cast_nonneg Tmax : (0 : ℝ) ≤ Tmax), (hu ℓ hℓ).1]
  set C := (Tmax : ℝ) + 1 + 2 * (eps + u ℓ)
  set K := Lf / fmin ^ 3 + 1
  set S := pairKeys (refPairsE ω) (M + 1)
  rcases le_or_gt 0 (Gmax ℓ) with hG | hG
  · calc C * ((1 - v) * K * fmax / 2) * Gmax ℓ / S
        = C * K * fmax * Gmax ℓ / 2 * ((1 - v) / S) := by ring
      _ ≤ C * K * fmax * Gmax ℓ / 2 * (4 / N) := by
          refine mul_le_mul_of_nonneg_left hcoef ?_
          have := mul_nonneg (mul_nonneg (mul_nonneg hC hK.le) hfmax.le) hG
          linarith
      _ = C * (2 * K * fmax) * Gmax ℓ / N := by ring
      _ ≤ u ℓ := hΨ ℓ hℓ
  · have h0 : 0 ≤ C * ((1 - v) * K * fmax / 2) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg hC h1v.le) hK.le) hfmax.le
      nlinarith
    have : C * ((1 - v) * K * fmax / 2) * Gmax ℓ / S ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h0 hG.le) hSpos.le
    linarith [(hu ℓ hℓ).1]


/-- The Gamma total `Γ (M + 1)` of the canonical exponential sequence is at most
`(M + 1) / 2` with probability at most `exp (-(M + 1) / 6)`. -/
theorem measureReal_gammaTotal_le_half (M : ℕ) :
    expSeqMeasure.real {ω | pairKeys (refPairsE ω) (M + 1) ≤ ((M : ℝ) + 1) / 2} ≤
      Real.exp (-(((M : ℝ) + 1) / 6)) := by
  have h := expSum_lower_half_tail iidSeq_expCoord (hasLaw_expCoord 0) 0 (M + 1)
  simp only [Nat.sub_zero, Nat.cast_add, Nat.cast_one] at h
  convert h using 4
  simp [expSum, expCoord, pairKeys_refPairsE]

/-- Almost surely the canonical exponential sequence has positive coordinates and finite
reference layers. -/
theorem ae_pos_allLayersFinite_refPairsE {eps : ℝ} (heps : 0 ≤ eps) :
    ∀ᵐ ω ∂expSeqMeasure, (∀ i, 0 < ω i) ∧ AllLayersFinite eps (refPairsE ω) :=
  (ae_all_iff.2 fun i => iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) i).and
    (ae_allLayersFinite_exp iidSeq_expCoord (hasLaw_expCoord 0) heps)

/-- **The anchored coupling.**  Let `Q = quantK f A B` for a Model K density, `0 ≤ v < 1`
an anchor value with `1 - v ≤ 2 (M + 1) / N`, and `s ≤ M`.  If for every layer `ℓ < L_top`,
`0 ≤ u ℓ ≤ eps` and `(Tmax + 1 + 2 (eps + u ℓ)) (2 (Lf / fmin³ + 1) fmax) Gmax ℓ / N ≤ u ℓ`,
then on the canonical exponential sequence space the anchored and the reference hierarchies
fail to agree through layer `L_top` at the positions `≤ s` with probability at most
`P(¬ refGood') + exp (-(M + 1) / 6)`. -/
theorem measureReal_not_agree_le (hf : DensityK f A B fmin fmax Lf) (hv0 : 0 ≤ v)
    (hv1 : v < 1) {M N : ℕ} (hanch : 1 - v ≤ 2 * ((M : ℝ) + 1) / N)
    {eps : ℝ} (heps : 0 ≤ eps) {L_top s Tmax : ℕ} {u Gmax : ℕ → ℝ} (hsM : s ≤ M)
    (hu : ∀ ℓ < L_top, 0 ≤ u ℓ ∧ u ℓ ≤ eps)
    (hΨ : ∀ ℓ < L_top, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ) :
    expSeqMeasure.real {ω | ¬ agree eps L_top s (anchPairs (quantK f A B) v M ω) (refPairsE ω)} ≤
      expSeqMeasure.real {ω | ¬ refGood' eps expCoord L_top s Tmax u Gmax ω} +
        Real.exp (-(((M : ℝ) + 1) / 6)) := by
  set Z := {ω : ℕ → ℝ | ¬ ((∀ i, 0 < ω i) ∧ AllLayersFinite eps (refPairsE ω))}
  have hZ : expSeqMeasure.real Z = 0 := by
    rw [Measure.real, ae_iff.1 (ae_pos_allLayersFinite_refPairsE heps), ENNReal.toReal_zero]
  set G := {ω : ℕ → ℝ | ¬ refGood' eps expCoord L_top s Tmax u Gmax ω}
  set C := {ω : ℕ → ℝ | pairKeys (refPairsE ω) (M + 1) ≤ ((M : ℝ) + 1) / 2}
  have hsub : {ω | ¬ agree eps L_top s (anchPairs (quantK f A B) v M ω) (refPairsE ω)} ⊆
      G ∪ C ∪ Z := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨⟨hG, hC⟩, hZ'⟩ := hno
    simp only [G, C, Z, Set.mem_ofPred_eq, not_not, not_le] at hG hC hZ'
    exact hω (agree_anchPairs hf hv0 hv1 hanch heps hsM hu hΨ hZ'.1 hZ'.2 hC.le hG)
  calc expSeqMeasure.real
        {ω | ¬ agree eps L_top s (anchPairs (quantK f A B) v M ω) (refPairsE ω)}
      ≤ expSeqMeasure.real (G ∪ C ∪ Z) := measureReal_mono hsub
    _ ≤ expSeqMeasure.real G + expSeqMeasure.real C + expSeqMeasure.real Z :=
        (measureReal_union_le _ _).trans (by gcongr; exact measureReal_union_le _ _)
    _ ≤ expSeqMeasure.real G + Real.exp (-(((M : ℝ) + 1) / 6)) := by
        rw [hZ, add_zero]
        gcongr
        exact measureReal_gammaTotal_le_half M

end Anchored

/-! ## Leading-pivot consequences -/

section Consequences

variable {eps : ℝ} {L_top s : ℕ}

/-- Under agreement, for `s' ≤ s` and `L ≤ L_top`, the two layer-`L` pivots `j` exceed `s'`
simultaneously. -/
theorem agree_lt_iff {z z' : ℕ → ℝ × ℕ} (h : agree eps L_top s z z') {L : ℕ} (hL : L ≤ L_top)
    {s' : ℕ} (hs : s' ≤ s) (j : ℕ) :
    s' < layerPivot eps z L j ↔ s' < layerPivot eps z' L j := by
  constructor
  · intro h1
    by_contra h2
    have := h L hL j (Or.inr ((not_lt.1 h2).trans hs))
    omega
  · intro h1
    by_contra h2
    have := h L hL j (Or.inl ((not_lt.1 h2).trans hs))
    omega

/-- The reference leading layer-`L` pivot is the count of the leading layer-`L` pair of the
reference endpoint hierarchy. -/
theorem layerPivot_refPairsE_one (eps : ℝ) (L : ℕ) (ω : ℕ → ℝ) :
    layerPivot eps (refPairsE ω) L 1 = (epLayerSeq eps expCoord L 0 ω).2 := by
  rw [layerPivot, pairRank_one, ← seq_inputPairs_expCoord, ← seq_epLayerSeq]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Transfer of a pivot tail through agreement: for `s' ≤ s` and `L ≤ L_top`,
`P(s' < pivot of Z) ≤ P(¬ agree) + P(s' < pivot of Z')`. -/
theorem measureReal_lt_layerPivot_le_of_agree (Z Z' : Ω → ℕ → ℝ × ℕ) {L s' : ℕ}
    (hL : L ≤ L_top) (hs : s' ≤ s) (j : ℕ) :
    P.real {ω | s' < layerPivot eps (Z ω) L j} ≤
      P.real {ω | ¬ agree eps L_top s (Z ω) (Z' ω)} +
        P.real {ω | s' < layerPivot eps (Z' ω) L j} := by
  refine (measureReal_mono fun ω hω => ?_).trans (measureReal_union_le _ _)
  by_cases ha : agree eps L_top s (Z ω) (Z' ω)
  · exact Or.inr ((agree_lt_iff ha hL hs j).1 hω)
  · exact Or.inl ha

/-- The reverse transfer: `P(s' < pivot of Z') - P(¬ agree) ≤ P(s' < pivot of Z)`. -/
theorem measureReal_lt_layerPivot_ge_of_agree (Z Z' : Ω → ℕ → ℝ × ℕ) {L s' : ℕ}
    (hL : L ≤ L_top) (hs : s' ≤ s) (j : ℕ) :
    P.real {ω | s' < layerPivot eps (Z' ω) L j} -
        P.real {ω | ¬ agree eps L_top s (Z ω) (Z' ω)} ≤
      P.real {ω | s' < layerPivot eps (Z ω) L j} := by
  have h : P.real {ω | s' < layerPivot eps (Z' ω) L j} ≤
      P.real {ω | ¬ agree eps L_top s (Z ω) (Z' ω)} +
        P.real {ω | s' < layerPivot eps (Z ω) L j} := by
    refine (measureReal_mono fun ω hω => ?_).trans (measureReal_union_le _ _)
    by_cases ha : agree eps L_top s (Z ω) (Z' ω)
    · exact Or.inr ((agree_lt_iff ha hL hs j).2 hω)
    · exact Or.inl ha
  linarith

end Consequences

/-! ## The leading anchored pivot -/

section Leading

variable {eps : ℝ} {L_top s : ℕ}

/-- **(a) Upper tail of the leading anchored pivot.**  For `s < n` and `L ≤ L_top`:
`P(n ≤ anchored leading layer-L pivot) ≤ P(¬ agree) + P(s < reference leading pivot)`. -/
theorem measureReal_le_layerPivot_anchPairs_le (Q : ℝ → ℝ) (v : ℝ) (M : ℕ) {L n : ℕ}
    (hL : L ≤ L_top) (hsn : s < n) :
    expSeqMeasure.real {ω | n ≤ layerPivot eps (anchPairs Q v M ω) L 1} ≤
      expSeqMeasure.real {ω | ¬ agree eps L_top s (anchPairs Q v M ω) (refPairsE ω)} +
        expSeqMeasure.real {ω | s < layerPivot eps (refPairsE ω) L 1} :=
  (measureReal_mono fun _ hω => lt_of_lt_of_le hsn hω).trans
    (measureReal_lt_layerPivot_le_of_agree (fun ω => anchPairs Q v M ω) refPairsE hL le_rfl 1)

/-- **(b) Lower tail of the leading anchored pivot.**  For `L ≤ L_top`:
`P(s < reference leading pivot) - P(¬ agree) ≤ P(s < anchored leading layer-L pivot)`. -/
theorem measureReal_lt_layerPivot_anchPairs_ge (Q : ℝ → ℝ) (v : ℝ) (M : ℕ) {L : ℕ}
    (hL : L ≤ L_top) :
    expSeqMeasure.real {ω | s < layerPivot eps (refPairsE ω) L 1} -
        expSeqMeasure.real {ω | ¬ agree eps L_top s (anchPairs Q v M ω) (refPairsE ω)} ≤
      expSeqMeasure.real {ω | s < layerPivot eps (anchPairs Q v M ω) L 1} :=
  measureReal_lt_layerPivot_ge_of_agree (fun ω => anchPairs Q v M ω) refPairsE hL le_rfl 1

variable {f : ℝ → ℝ} {A B fmin fmax Lf v : ℝ}

/-- **(a) with the coupling bound.**  Under the hypotheses of `measureReal_not_agree_le`,
for `s < n` and `L ≤ L_top`:
`P(n ≤ anchored leading layer-L pivot) ≤ P(¬ refGood') + exp (-(M + 1) / 6)
  + P(s < reference leading pivot)`. -/
theorem measureReal_le_layerPivot_anchPairs_le_refGood' (hf : DensityK f A B fmin fmax Lf)
    (hv0 : 0 ≤ v) (hv1 : v < 1) {M N : ℕ} (hanch : 1 - v ≤ 2 * ((M : ℝ) + 1) / N)
    (heps : 0 ≤ eps) {Tmax : ℕ} {u Gmax : ℕ → ℝ} (hsM : s ≤ M)
    (hu : ∀ ℓ < L_top, 0 ≤ u ℓ ∧ u ℓ ≤ eps)
    (hΨ : ∀ ℓ < L_top, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ) {L n : ℕ} (hL : L ≤ L_top) (hsn : s < n) :
    expSeqMeasure.real {ω | n ≤ layerPivot eps (anchPairs (quantK f A B) v M ω) L 1} ≤
      expSeqMeasure.real {ω | ¬ refGood' eps expCoord L_top s Tmax u Gmax ω} +
        Real.exp (-(((M : ℝ) + 1) / 6)) +
        expSeqMeasure.real {ω | s < layerPivot eps (refPairsE ω) L 1} := by
  have h1 := measureReal_le_layerPivot_anchPairs_le (eps := eps) (quantK f A B) v M hL hsn
  have h2 := measureReal_not_agree_le hf hv0 hv1 hanch heps hsM hu hΨ
  linarith

/-- **(b) with the coupling bound.**  Under the hypotheses of `measureReal_not_agree_le`,
for `L ≤ L_top`: `P(s < reference leading pivot) - P(¬ refGood') - exp (-(M + 1) / 6)
  ≤ P(s < anchored leading layer-L pivot)`. -/
theorem measureReal_lt_layerPivot_anchPairs_ge_refGood' (hf : DensityK f A B fmin fmax Lf)
    (hv0 : 0 ≤ v) (hv1 : v < 1) {M N : ℕ} (hanch : 1 - v ≤ 2 * ((M : ℝ) + 1) / N)
    (heps : 0 ≤ eps) {Tmax : ℕ} {u Gmax : ℕ → ℝ} (hsM : s ≤ M)
    (hu : ∀ ℓ < L_top, 0 ≤ u ℓ ∧ u ℓ ≤ eps)
    (hΨ : ∀ ℓ < L_top, ((Tmax : ℝ) + 1 + 2 * (eps + u ℓ)) * (2 * (Lf / fmin ^ 3 + 1) * fmax) *
      Gmax ℓ / N ≤ u ℓ) {L : ℕ} (hL : L ≤ L_top) :
    expSeqMeasure.real {ω | s < layerPivot eps (refPairsE ω) L 1} -
        expSeqMeasure.real {ω | ¬ refGood' eps expCoord L_top s Tmax u Gmax ω} -
        Real.exp (-(((M : ℝ) + 1) / 6)) ≤
      expSeqMeasure.real {ω | s < layerPivot eps (anchPairs (quantK f A B) v M ω) L 1} := by
  have h1 := measureReal_lt_layerPivot_anchPairs_ge (eps := eps) (s := s) (quantK f A B) v M hL
  have h2 := measureReal_not_agree_le hf hv0 hv1 hanch heps hsM hu hΨ
  linarith

end Leading

end

end PGM
