import PLAStochastic.Index.Endpoint.HyperSegmentMoments
import PLAStochastic.ForMathlib.Probability.Moments.PaleyZygmund
import Mathlib.Probability.Independence.Integration

/-!
# Reference endpoint hierarchy: regeneration, node counts, node lengths and node spans

A simplified form of `ksc:lem:tree-truncation` (`proofK_endpoint_scale.tex`).  Write
`W ℓ = epLayerSeq eps g ℓ` for layer `ℓ` of the endpoint hierarchy of an input `g` under the
hypotheses of `hyperexp_all` (bundled in `RefHyp`; `RefHyp.of_gapLaw` covers any input gap
law, in particular iid `Exp(1)` gaps via `gapLaw_exp`), and `m ℓ = lcount P (W ℓ)`.
The `k`-th layer-`ℓ` node (block) is the ALG-OPT segment starting at the `k`-th
layer-`(ℓ+1)` pivot; its layer-`ℓ` sequence is `(pairShift eps)^[k] (seq (W ℓ) ω)`, its
length is `pairSegLen eps` of that sequence, and its base-rank span is
`(W (ℓ+1) k ω).2` (`epLayerSeq_succ_apply`).

* **Regeneration** (`identDistrib_refShift`, `measure_refShift_mem`): the layer-`ℓ` sequence
  restarted at the `k`-th block has the law of `seq (W ℓ)`.
* **Node counts** (`measureReal_pairRank_le`, `measureReal_pairRank_le_of_le`):
  `P(pairRank (seq (W ℓ) ω) R ≤ s) ≤ exp(2 s / m ℓ - R / (8 Kc))`, hence
  `≤ exp(-R / (16 Kc))` when `32 Kc s ≤ R m ℓ`.  The proof is Paley–Zygmund
  (`P(N > m/2) ≥ 1 / (4 Kc)`, `measureReal_count_gt_half_ge`) and an exponential Chernoff
  bound for the number of `i < R` with `N_i > m/2`.
* **Node lengths** (`measureReal_refSegLen_gt_le`): with the layer-uniform length
  `refLen eps vmin = ⌈5185 eps² / vmin⌉₊ ≤ (5185 / vmin + 1) eps²`,
  `P(pairSegLen of the k-th block > j · refLen) ≤ (71/72)^j`.
* **Node spans** (`measureReal_refSpan_gt_le`, `measureReal_refNodeSpan_gt_le`):
  `P((W ℓ k ω).2 > λ m ℓ) ≤ CK exp(-θK λ)`.
* **Union bounds** (`measureReal_exists_refSegLen_gt_le`, `measureReal_exists_refSpan_gt_le`,
  `measureReal_exists_refNodeSpan_gt_le`) over the first `R` blocks.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## Standing hypotheses -/

/-- The hypotheses of `hyperexp_all` on the input of the reference endpoint hierarchy. -/
structure RefHyp (P : Measure Ω) (g : ℕ → Ω → ℝ) (b β vmin Kc eps : ℝ) : Prop where
  input : LayerOK P (inputPairs g) b β vmin Kc
  hb : bAbs ≤ b
  hβ : βAbs ≤ β
  hvmin0 : 0 < vmin
  hvmin : vmin ≤ deltaVar / 2
  hKc : KcAbs ≤ Kc
  heps : epsZero b β ≤ eps
  hepsK : GK * b ≤ eps ^ 2

/-- Any input gap law with `eps ≥ epsK` satisfies the standing hypotheses with its class
constants (for iid `Exp(1)` gaps use `gapLaw_exp`). -/
theorem RefHyp.of_gapLaw [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsK (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) :
    RefHyp P g (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) (vIn μ₀ σ₀) KcIn eps where
  input := layerOK_input hg
  hb := bAbs_le_bIn μ₀ σ₀
  hβ := βAbs_le_βIn _ _
  hvmin0 := vIn_pos hg.mu_pos hg.sigma_pos
  hvmin := vIn_le μ₀ σ₀
  hKc := KcAbs_le_KcIn
  heps := epsZero_le_of_epsK_le heps
  hepsK := GK_mul_le_sq_of_epsK_le (le_trans bAbs_pos.le (bAbs_le_bIn μ₀ σ₀)) heps

variable {g : ℕ → Ω → ℝ} {b β vmin Kc eps : ℝ}

namespace RefHyp

/-- Every layer satisfies the invariant. -/
theorem layerOK [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) :
    LayerOK P (epLayerSeq eps g ℓ) b β vmin Kc :=
  (layerOK_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps ℓ).1

/-- Every layer is an iid pair sequence. -/
theorem iid [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) :
    IIDPairs P (epLayerSeq eps g ℓ) :=
  (H.layerOK ℓ).iid

/-- The first segment of every layer is almost surely finite. -/
theorem ae_ne_top [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) :
    ∀ᵐ ω ∂P, pairSegLen eps (seq (epLayerSeq eps g ℓ) ω) ≠ ⊤ :=
  (layerOK_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps ℓ).2.1

theorem Kc_pos (H : RefHyp P g b β vmin Kc eps) : 0 < Kc :=
  lt_of_lt_of_le KcAbs_pos H.hKc

theorem one_le_eps (H : RefHyp P g b β vmin Kc eps) : 1 ≤ eps :=
  le_trans (one_le_epsZero b β) H.heps

theorem lcount_pos [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) :
    0 < lcount P (epLayerSeq eps g ℓ) :=
  (H.layerOK ℓ).cnt_pos

end RefHyp

/-! ## Blocks of a layer -/

omit mΩ in
/-- Layer `ℓ + 1` at index `k` is the aggregated `k`-th block of layer `ℓ`. -/
theorem epLayerSeq_succ_apply (eps : ℝ) (g : ℕ → Ω → ℝ) (ℓ k : ℕ) (ω : Ω) :
    epLayerSeq eps g (ℓ + 1) k ω =
      firstBlock eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω)) := by
  simp only [epLayerSeq, Function.iterate_succ_apply']
  rfl

/-! ## 1. Regeneration of blocks -/

/-- **Regeneration.**  The layer-`ℓ` sequence restarted at the `k`-th block has the law of
the layer-`ℓ` sequence. -/
theorem identDistrib_refShift [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps)
    (ℓ k : ℕ) :
    IdentDistrib (fun ω => (pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω))
      (seq (epLayerSeq eps g ℓ)) P P :=
  identDistrib_iterate_shiftBy (H.iid ℓ).measurable (H.iid ℓ).indep (H.iid ℓ).ident
    (isStoppingRule_pairSegLen eps) (H.ae_ne_top ℓ) k

/-- Event form of the regeneration. -/
theorem measure_refShift_mem [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps)
    (ℓ k : ℕ) {E : Set (ℕ → ℝ × ℕ)} (hE : MeasurableSet E) :
    P {ω | (pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω) ∈ E} =
      P {ω | seq (epLayerSeq eps g ℓ) ω ∈ E} :=
  (identDistrib_refShift H ℓ k).measure_mem_eq hE

theorem measureReal_refShift_mem [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps)
    (ℓ k : ℕ) {E : Set (ℕ → ℝ × ℕ)} (hE : MeasurableSet E) :
    P.real {ω | (pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω) ∈ E} =
      P.real {ω | seq (epLayerSeq eps g ℓ) ω ∈ E} := by
  simp only [measureReal_def, measure_refShift_mem H ℓ k hE]

/-! ## 2. Node counts -/

/-- **Paley–Zygmund for the counts.**  Under the layer invariant,
`P(N_i > m/2) ≥ 1 / (4 Kc)` for every pair `i`. -/
theorem measureReal_count_gt_half_ge [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ × ℕ}
    {b β vmin Kc : ℝ} (hL : LayerOK P Z b β vmin Kc) (hKc : 0 < Kc) (i : ℕ) :
    1 / (4 * Kc) ≤ P.real {ω | 1 / 2 * lcount P Z < ((Z i ω).2 : ℝ)} := by
  have hWm : Measurable (fun ω => ((Z 0 ω).2 : ℝ)) :=
    measurable_natCast_snd.comp (hL.iid.measurable 0)
  have hpz := paley_zygmund hWm (fun ω => Nat.cast_nonneg _) hL.cnt2 (θ := 1 / 2)
    (by norm_num) (by norm_num)
  change (1 - 1 / 2) ^ 2 * lcount P Z ^ 2 ≤
    lcount2 P Z * P.real {ω | 1 / 2 * lcount P Z < ((Z 0 ω).2 : ℝ)} at hpz
  have hid : IdentDistrib (fun ω => ((Z i ω).2 : ℝ)) (fun ω => ((Z 0 ω).2 : ℝ)) P P :=
    (hL.iid.ident i).comp measurable_natCast_snd
  have he := hid.measure_mem_eq (measurableSet_Ioi (a := 1 / 2 * lcount P Z))
  have he' : P.real {ω | 1 / 2 * lcount P Z < ((Z i ω).2 : ℝ)} =
      P.real {ω | 1 / 2 * lcount P Z < ((Z 0 ω).2 : ℝ)} := by
    simp only [measureReal_def]
    exact congrArg ENNReal.toReal he
  rw [he']
  set q := P.real {ω | 1 / 2 * lcount P Z < ((Z 0 ω).2 : ℝ)}
  set m := lcount P Z
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hm := hL.cnt_pos
  have h1 : 1 / 4 * m ^ 2 ≤ (Kc * q) * m ^ 2 := by
    calc 1 / 4 * m ^ 2 = (1 - 1 / 2) ^ 2 * m ^ 2 := by norm_num
      _ ≤ lcount2 P Z * q := hpz
      _ ≤ (Kc * m ^ 2) * q := mul_le_mul_of_nonneg_right hL.cnt_sq hq0
      _ = (Kc * q) * m ^ 2 := by ring
  have h2 : 1 / 4 ≤ Kc * q := le_of_mul_le_mul_right h1 (by positivity)
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The indicator weight of a large count. -/
private def bigCount (m : ℝ) (x : ℝ × ℕ) : ℝ := {x : ℝ × ℕ | 1 / 2 * m < (x.2 : ℝ)}.indicator 1 x

omit mΩ in
private theorem measurable_bigCount (m : ℝ) : Measurable (bigCount m) :=
  measurable_one.indicator (measurableSet_lt measurable_const measurable_natCast_snd)

omit mΩ in
/-- A count is at least `m/2` times its large-count indicator. -/
private theorem half_mul_bigCount_le (m : ℝ) (x : ℝ × ℕ) :
    m / 2 * bigCount m x ≤ (x.2 : ℝ) := by
  unfold bigCount
  by_cases h : 1 / 2 * m < (x.2 : ℝ)
  · rw [Set.indicator_of_mem (by exact h)]
    simp only [Pi.one_apply, mul_one]
    linarith
  · rw [Set.indicator_of_notMem (by exact h)]
    simp

private theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h := Real.add_one_le_exp 1
  rw [Real.exp_neg]
  rw [inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
  linarith

/-- **Chernoff lower tail for iid counts.**  If `P(N_0 > m/2) ≥ p` for an iid pair sequence,
then `P(N_0 + ⋯ + N_{R-1} ≤ s) ≤ exp(2 s / m - p R / 2)`. -/
theorem measureReal_pairRank_le_of_iid [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ × ℕ}
    (hZ : IIDPairs P Z) {m p : ℝ} (hm : 0 < m)
    (hp : p ≤ P.real {ω | 1 / 2 * m < ((Z 0 ω).2 : ℝ)}) (R s : ℕ) :
    P.real {ω | pairRank (seq Z ω) R ≤ s} ≤ Real.exp (2 * s / m - p * R / 2) := by
  set c := 1 - Real.exp (-1) with hc
  have hc2 : 1 / 2 ≤ c := by have := exp_neg_one_le_half; linarith
  have hc1 : c ≤ 1 := by have := Real.exp_pos (-1); linarith
  set f : ℝ × ℕ → ℝ := fun x => Real.exp (-bigCount m x) with hf
  have hfm : Measurable f := (measurable_bigCount m).neg.exp
  set F : Ω → ℝ := fun ω => ∏ i : Fin R, f (Z i ω) with hF
  -- independence over the first `R` pairs
  have hind : iIndepFun (fun i : Fin R => Z (i : ℕ)) P :=
    hZ.indep.precomp (g := fun i : Fin R => (i : ℕ)) Fin.val_injective
  have hprod : ∫ ω, F ω ∂P = ∏ i : Fin R, ∫ ω, f (Z i ω) ∂P :=
    hind.integral_fun_prod_comp (f := fun _ => f) (fun i => (hZ.measurable i).aemeasurable)
      (fun _ => hfm.aestronglyMeasurable)
  -- one factor
  set q := P.real {ω | 1 / 2 * m < ((Z 0 ω).2 : ℝ)} with hqdef
  have hq1 : q ≤ 1 := measureReal_le_one
  have hq0 : 0 ≤ q := measureReal_nonneg
  set S := {ω | 1 / 2 * m < ((Z 0 ω).2 : ℝ)} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_natCast_snd.comp (hZ.measurable 0))
  have hint0 : ∫ ω, f (Z 0 ω) ∂P = 1 - c * q := by
    have hpt : ∀ ω, f (Z 0 ω) = 1 - c * S.indicator 1 ω := by
      intro ω
      simp only [hf, bigCount, hc, hSdef, Set.indicator_apply, Set.mem_ofPred_eq]
      split_ifs <;> simp
    have h1 : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const _
    have h2 : Integrable (fun ω => c * S.indicator (1 : Ω → ℝ) ω) P :=
      ((integrable_const (1 : ℝ)).indicator hS).const_mul c
    simp_rw [hpt]
    rw [integral_sub (f := fun _ => (1 : ℝ)) (g := fun ω => c * S.indicator 1 ω) h1 h2,
      integral_const_mul, integral_indicator_one hS]
    simp [hqdef]
  have hfac : ∀ i : Fin R, ∫ ω, f (Z i ω) ∂P = 1 - c * q := by
    intro i
    rw [← hint0]
    exact ((hZ.ident i).comp hfm).integral_eq
  have hEF : ∫ ω, F ω ∂P ≤ Real.exp (-(p * R / 2)) := by
    rw [hprod]
    simp only [hfac, prod_const, card_univ, Fintype.card_fin]
    have h0 : 0 ≤ 1 - c * q := by nlinarith
    have h1 : 1 - c * q ≤ Real.exp (-(c * q)) := by
      have := Real.add_one_le_exp (-(c * q)); linarith
    have hpq : p / 2 ≤ c * q := by nlinarith
    calc (1 - c * q) ^ R ≤ Real.exp (-(c * q)) ^ R := pow_le_pow_left₀ h0 h1 R
      _ = Real.exp (-(c * q) * R) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(p * R / 2)) := by
          rw [Real.exp_le_exp]
          have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
          nlinarith
  -- Markov
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => prod_nonneg fun i _ => (Real.exp_pos _).le
  have hF1 : ∀ ω, F ω ≤ 1 := by
    intro ω
    refine prod_le_one (fun i _ => (Real.exp_pos _).le) fun i _ => ?_
    rw [Real.exp_le_one_iff, neg_nonpos]
    unfold bigCount
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hFm : Measurable F :=
    Finset.measurable_prod _ fun i _ => hfm.comp (hZ.measurable i)
  have hFint : Integrable F P :=
    (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]; exact hF1 ω)
  have hsub : {ω | pairRank (seq Z ω) R ≤ s} ⊆
      {ω | Real.exp (-(2 * s / m)) ≤ F ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hFe : F ω = Real.exp (-∑ i ∈ range R, bigCount m (Z i ω)) := by
      rw [hF, ← Fin.sum_univ_eq_sum_range (fun i => bigCount m (Z i ω)), ← sum_neg_distrib,
        Real.exp_sum]
    rw [hFe, Real.exp_le_exp, neg_le_neg_iff]
    have hsum : m / 2 * ∑ i ∈ range R, bigCount m (Z i ω) ≤ (pairRank (seq Z ω) R : ℝ) := by
      rw [mul_sum, pairRank, Nat.cast_sum]
      exact sum_le_sum fun i _ => half_mul_bigCount_le m (Z i ω)
    have hs : (pairRank (seq Z ω) R : ℝ) ≤ s := by exact_mod_cast hω
    rw [le_div_iff₀ hm]
    linarith
  have hmark := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hF0) hFint
    (Real.exp (-(2 * s / m)))
  have hP : Real.exp (-(2 * s / m)) * P.real {ω | pairRank (seq Z ω) R ≤ s} ≤
      Real.exp (-(p * R / 2)) :=
    le_trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le)
      (hmark.trans hEF)
  have he : Real.exp (2 * s / m - p * R / 2) =
      Real.exp (-(p * R / 2)) / Real.exp (-(2 * s / m)) := by
    rw [← Real.exp_sub]; ring_nf
  rw [he, le_div_iff₀ (Real.exp_pos _), mul_comm]
  exact hP

/-- **Node counts.**  The first `R` layer-`ℓ` pairs span more than `s` base ranks except with
probability `exp(2 s / m ℓ - R / (8 Kc))`. -/
theorem measureReal_pairRank_le [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps)
    (ℓ R s : ℕ) :
    P.real {ω | pairRank (seq (epLayerSeq eps g ℓ) ω) R ≤ s} ≤
      Real.exp (2 * s / lcount P (epLayerSeq eps g ℓ) - R / (8 * Kc)) := by
  have hKc := H.Kc_pos
  have h := measureReal_pairRank_le_of_iid (H.iid ℓ) (H.lcount_pos ℓ)
    (measureReal_count_gt_half_ge (H.layerOK ℓ) hKc 0) R s
  have e : 1 / (4 * Kc) * R / 2 = R / (8 * Kc) := by field_simp; ring
  rwa [e] at h

/-- **Node counts, explicit form.**  If `32 Kc s ≤ R m ℓ`, then at most `R` layer-`ℓ` pivots
lie in `[0, s]` (`pairRank R > s`) except with probability `exp(-R / (16 Kc))`. -/
theorem measureReal_pairRank_le_of_le [IsProbabilityMeasure P]
    (H : RefHyp P g b β vmin Kc eps) (ℓ R s : ℕ)
    (hRs : 32 * Kc * s ≤ R * lcount P (epLayerSeq eps g ℓ)) :
    P.real {ω | pairRank (seq (epLayerSeq eps g ℓ) ω) R ≤ s} ≤
      Real.exp (-(R / (16 * Kc))) := by
  have hKc := H.Kc_pos
  have hm := H.lcount_pos ℓ
  refine (measureReal_pairRank_le H ℓ R s).trans (Real.exp_le_exp.2 ?_)
  set m := lcount P (epLayerSeq eps g ℓ)
  have h1 : 2 * (s : ℝ) / m ≤ R / (16 * Kc) := by
    rw [div_le_div_iff₀ hm (by positivity)]
    nlinarith
  have h2 : (R : ℝ) / (8 * Kc) = 2 * (R / (16 * Kc)) := by field_simp; ring
  linarith

/-! ## 3. Node lengths -/

/-- The layer-uniform node length scale `⌈5185 eps² / vmin⌉₊`. -/
def refLen (eps vmin : ℝ) : ℕ := ⌈5185 * eps ^ 2 / vmin⌉₊

theorem refLen_le (H : RefHyp P g b β vmin Kc eps) :
    (refLen eps vmin : ℝ) ≤ (5185 / vmin + 1) * eps ^ 2 := by
  have h1 := H.one_le_eps
  have hv := H.hvmin0
  have hle : (refLen eps vmin : ℝ) ≤ 5185 * eps ^ 2 / vmin + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have he2 : 1 ≤ eps ^ 2 := one_le_pow₀ h1
  calc (refLen eps vmin : ℝ) ≤ 5185 * eps ^ 2 / vmin + 1 := hle
    _ ≤ 5185 * eps ^ 2 / vmin + eps ^ 2 := by linarith
    _ = (5185 / vmin + 1) * eps ^ 2 := by ring

/-- The layer-`ℓ` block tail at the layer-dependent scale `L ≤ 5185 G ≤ 5185 eps² / vmin`. -/
theorem exists_segLen_tail [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) :
    ∃ L : ℕ, 1 ≤ L ∧ (L : ℝ) ≤ 5185 * eps ^ 2 / vmin ∧
      ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < pairSegLen eps (seq (epLayerSeq eps g ℓ) ω)} ≤
        (71 / 72 : ℝ) ^ j := by
  set Z := epLayerSeq eps g ℓ
  have hL := H.layerOK ℓ
  set μ := lmean P Z with hμdef
  set σ := lsig P Z with hσdef
  set κ := lkap P Z with hκdef
  have hX := hL.law
  have hμ : 0 < μ := hX.mu_pos
  have hσ : 0 < σ := hX.sigma_pos
  have hκ : 0 ≤ κ := hX.kappa_nonneg
  have hepspos : 0 < eps := by linarith [H.one_le_eps]
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := largeConditions hμ hσ hκ hL.var_le hL.third_le H.heps
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX hepspos rfl c1 c2 c3 c4
  have hGv : μ ^ 2 * eps ^ 2 / σ ^ 2 ≤ eps ^ 2 / vmin := by
    rw [div_le_div_iff₀ (by positivity) H.hvmin0]
    calc μ ^ 2 * eps ^ 2 * vmin = eps ^ 2 * (vmin * μ ^ 2) := by ring
      _ ≤ eps ^ 2 * σ ^ 2 := mul_le_mul_of_nonneg_left hL.var_ge (sq_nonneg eps)
  refine ⟨L, hL1, ?_, htail⟩
  calc (L : ℝ) ≤ 5185 * (μ ^ 2 * eps ^ 2 / σ ^ 2) := hLG
    _ ≤ 5185 * (eps ^ 2 / vmin) := by gcongr
    _ = 5185 * eps ^ 2 / vmin := by ring

/-- Geometric tail of the first layer-`ℓ` node length at the uniform scale `refLen`. -/
theorem measureReal_segLen_gt_le [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps)
    (ℓ j : ℕ) :
    P.real {ω | ((j * refLen eps vmin : ℕ) : ℕ∞) <
      pairSegLen eps (seq (epLayerSeq eps g ℓ) ω)} ≤ (71 / 72 : ℝ) ^ j := by
  obtain ⟨L, -, hLv, htail⟩ := exists_segLen_tail H ℓ
  have hLr : L ≤ refLen eps vmin := by
    have : (L : ℝ) ≤ refLen eps vmin := hLv.trans (Nat.le_ceil _)
    exact_mod_cast this
  refine le_trans (measureReal_mono fun ω hω => ?_) (htail j)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine lt_of_le_of_lt ?_ hω
  exact_mod_cast Nat.mul_le_mul_left j hLr

/-- **Node lengths.**  The `k`-th layer-`ℓ` node has
`P(length > j · refLen eps vmin) ≤ (71/72)^j`. -/
theorem measureReal_refSegLen_gt_le [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps)
    (ℓ k j : ℕ) :
    P.real {ω | ((j * refLen eps vmin : ℕ) : ℕ∞) <
      pairSegLen eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω))} ≤
        (71 / 72 : ℝ) ^ j := by
  have hE : MeasurableSet {z : ℕ → ℝ × ℕ | ((j * refLen eps vmin : ℕ) : ℕ∞) < pairSegLen eps z} :=
    measurable_pairSegLen eps
      (MeasurableSet.of_discrete (s := Set.Ioi ((j * refLen eps vmin : ℕ) : ℕ∞)))
  rw [show {ω | ((j * refLen eps vmin : ℕ) : ℕ∞) <
      pairSegLen eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω))} =
      {ω | (pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω) ∈
        {z : ℕ → ℝ × ℕ | ((j * refLen eps vmin : ℕ) : ℕ∞) < pairSegLen eps z}} from rfl,
    measureReal_refShift_mem H ℓ k hE]
  exact measureReal_segLen_gt_le H ℓ j

/-! ## 4. Node spans -/

/-- **Node spans.**  Every layer-`ℓ` pair has the exponential count tail
`P((W ℓ k).2 > λ m ℓ) ≤ CK exp(-θK λ)`. -/
theorem measureReal_refSpan_gt_le [IsProbabilityMeasure P] (H : RefHyp P g b β vmin Kc eps)
    (ℓ k : ℕ) (lam : ℝ) :
    P.real {ω | lam * lcount P (epLayerSeq eps g ℓ) < ((epLayerSeq eps g ℓ k ω).2 : ℝ)} ≤
      CK * Real.exp (-(θK * lam)) := by
  have hid : IdentDistrib (fun ω => ((epLayerSeq eps g ℓ k ω).2 : ℝ))
      (fun ω => ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)) P P :=
    ((H.iid ℓ).ident k).comp measurable_natCast_snd
  have he := hid.measure_mem_eq (measurableSet_Ioi (a := lam * lcount P (epLayerSeq eps g ℓ)))
  have he' : P.real {ω | lam * lcount P (epLayerSeq eps g ℓ) < ((epLayerSeq eps g ℓ k ω).2 : ℝ)} =
      P.real {ω | lam * lcount P (epLayerSeq eps g ℓ) < ((epLayerSeq eps g ℓ 0 ω).2 : ℝ)} := by
    simp only [measureReal_def]
    exact congrArg ENNReal.toReal he
  rw [he']
  exact hyperexp_tail_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps H.hepsK ℓ lam

/-- Node spans in block form: the base-rank span of the `k`-th layer-`ℓ` node satisfies
`P(span > λ m (ℓ+1)) ≤ CK exp(-θK λ)`. -/
theorem measureReal_refNodeSpan_gt_le [IsProbabilityMeasure P]
    (H : RefHyp P g b β vmin Kc eps) (ℓ k : ℕ) (lam : ℝ) :
    P.real {ω | lam * lcount P (epLayerSeq eps g (ℓ + 1)) <
      ((firstBlock eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω))).2 : ℝ)} ≤
        CK * Real.exp (-(θK * lam)) := by
  simp_rw [← epLayerSeq_succ_apply]
  exact measureReal_refSpan_gt_le H (ℓ + 1) k lam

/-! ## 5. Union bounds over the first `R` nodes -/

/-- Union bound over the indices `k < R`. -/
private theorem measureReal_exists_lt_le {p : ℕ → Ω → Prop} {a : ℝ}
    (h : ∀ k, P.real {ω | p k ω} ≤ a) (R : ℕ) :
    P.real {ω | ∃ k < R, p k ω} ≤ R * a := by
  have hset : {ω | ∃ k < R, p k ω} = ⋃ k ∈ range R, {ω | p k ω} := by
    ext ω; simp
  rw [hset]
  calc P.real (⋃ k ∈ range R, {ω | p k ω}) ≤ ∑ k ∈ range R, P.real {ω | p k ω} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ range R, a := sum_le_sum fun k _ => h k
    _ = R * a := by rw [sum_const, card_range, nsmul_eq_mul]

/-- Union bound for the node lengths of the first `R` layer-`ℓ` nodes. -/
theorem measureReal_exists_refSegLen_gt_le [IsProbabilityMeasure P]
    (H : RefHyp P g b β vmin Kc eps) (ℓ R j : ℕ) :
    P.real {ω | ∃ k < R, ((j * refLen eps vmin : ℕ) : ℕ∞) <
      pairSegLen eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω))} ≤
        R * (71 / 72 : ℝ) ^ j :=
  measureReal_exists_lt_le (fun k => measureReal_refSegLen_gt_le H ℓ k j) R

/-- Union bound for the spans of the first `R` layer-`ℓ` pairs. -/
theorem measureReal_exists_refSpan_gt_le [IsProbabilityMeasure P]
    (H : RefHyp P g b β vmin Kc eps) (ℓ R : ℕ) (lam : ℝ) :
    P.real {ω | ∃ k < R, lam * lcount P (epLayerSeq eps g ℓ) <
      ((epLayerSeq eps g ℓ k ω).2 : ℝ)} ≤ R * (CK * Real.exp (-(θK * lam))) :=
  measureReal_exists_lt_le (fun k => measureReal_refSpan_gt_le H ℓ k lam) R

/-- Union bound for the base-rank spans of the first `R` layer-`ℓ` nodes. -/
theorem measureReal_exists_refNodeSpan_gt_le [IsProbabilityMeasure P]
    (H : RefHyp P g b β vmin Kc eps) (ℓ R : ℕ) (lam : ℝ) :
    P.real {ω | ∃ k < R, lam * lcount P (epLayerSeq eps g (ℓ + 1)) <
      ((firstBlock eps ((pairShift eps)^[k] (seq (epLayerSeq eps g ℓ) ω))).2 : ℝ)} ≤
        R * (CK * Real.exp (-(θK * lam))) :=
  measureReal_exists_lt_le (fun k => measureReal_refNodeSpan_gt_le H ℓ k lam) R

end

end PGM
