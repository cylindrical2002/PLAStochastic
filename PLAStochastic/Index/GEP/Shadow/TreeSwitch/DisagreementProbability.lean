import PLAStochastic.Index.GEP.Shadow.TreeSwitch.Deterministic
import PLAStochastic.Index.GEP.Shadow.Regeneration
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass
import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments

/-!
# WP3 tree switch: the probability that the two trees differ (tree-prob)

Source: `research/2026-09-28-gep-closure/memory-route.md` §6, (tree-prob), in the polynomial
form of `research/2026-09-29-lean-gep-shadow-defects/README.md` (line B).

Setting: an iid sequence of (active, passive) pairs `V i = (X_i, Y_i)` on a probability space
whose passive law `ν` is regular (`RegLaw D θ vlo vhi ν`), with `E (X - Y)² ≤ τ¹²`,
`0 < τ ≤ 1/2`.  Nothing is assumed on the active component besides square integrability of
`X - Y`.  With `s = τ`, `h = τ⁴`, `R = ⌈eps²/(c₀ τ)⌉` and `u = 2 (R + 2 eps) τ³`, the event
`T_X ≠ T_Y` is contained (almost surely) in the union of

* `Y_0 < τ` (probability `≤ D τ`, density bound of `ν`);
* `∑_{j<R} |X_j - Y_j| > τ⁴` (Markov, `≤ R τ⁶/τ⁴`);
* `T_Y > R` (`gapSegLen_tail` of WP2, `≤ (72/71) τ`);
* a near-tie of the passive path at its stop (`LocalGapLaw.stopped_margin_segLen` of
  `PLAStochastic/Index/OneLayer/ThresholdMargin.lean`, with `u (1 + log(1/u))^5 ≤ 11^5 √u`),

by the deterministic `gapSegLen_eq_of_close`.  Result (`treeProb_le`):
`P(T_X ≠ T_Y) ≤ treeK D vlo · eps¹¹ · τ` for `eps ≥ epsZero (regB vhi) (regBeta D θ vlo)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

/-! ## Constants -/

/-- The passive stopping rate `c₀ = tailRate · regV vlo` of `gapSegLen_tail`. -/
def trC (vlo : ℝ) : ℝ := tailRate * regV vlo

/-- The margin constant `64 (1/c₀ + 2)^5 D` of `stopped_margin_segLen`. -/
def trKM (D vlo : ℝ) : ℝ := 64 * (1 / trC vlo + 2) ^ 5 * D

/-- `κ = √(2 (1/c₀ + 3))`, so that `u ≤ κ² eps² τ²`. -/
def trKappa (vlo : ℝ) : ℝ := Real.sqrt (2 * (1 / trC vlo + 3))

/-- The constant of (tree-prob). -/
def treeK (D vlo : ℝ) : ℝ :=
  D + 1 / trC vlo + 1 + 72 / 71 + (trKM D vlo * 11 ^ 5 + 72 / 71 + 2) * trKappa vlo

theorem trC_pos {vlo : ℝ} (hvlo : 0 < vlo) : 0 < trC vlo :=
  mul_pos tailRate_pos (regV_pos hvlo)

theorem trKM_nonneg {D vlo : ℝ} (hD : 0 ≤ D) (hvlo : 0 < vlo) : 0 ≤ trKM D vlo := by
  have := trC_pos hvlo
  unfold trKM; positivity

theorem treeK_nonneg {D vlo : ℝ} (hD : 0 ≤ D) (hvlo : 0 < vlo) : 0 ≤ treeK D vlo := by
  have := trC_pos hvlo
  have := trKM_nonneg hD hvlo
  have : 0 ≤ trKappa vlo := Real.sqrt_nonneg _
  unfold treeK; positivity

/-! ## An elementary logarithmic bound -/

/-- `u (1 + log(1/u))⁵ ≤ 11⁵ √u` for `0 < u ≤ 1`. -/
theorem mul_one_add_log_pow_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    u * (1 + Real.log (1 / u)) ^ 5 ≤ 11 ^ 5 * Real.sqrt u := by
  set w : ℝ := u ^ ((1 : ℝ) / 10) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hu0 _
  have hw1 : w ≤ 1 := Real.rpow_le_one hu0.le hu1 (by norm_num)
  have hw10 : w ^ 10 = u := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
    norm_num
  have hlog : Real.log (1 / u) = 10 * Real.log (1 / w) := by
    rw [← hw10, one_div, one_div, Real.log_inv, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hlw : Real.log (1 / w) ≤ 1 / w - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hinv : 1 ≤ 1 / w := by rw [le_div_iff₀ hw0]; linarith
  have hlog0 : 0 ≤ Real.log (1 / u) := Real.log_nonneg (by rw [le_div_iff₀ hu0]; linarith)
  have h1 : 1 + Real.log (1 / u) ≤ 11 * (1 / w) := by rw [hlog]; linarith
  have h5 : (1 + Real.log (1 / u)) ^ 5 ≤ (11 * (1 / w)) ^ 5 :=
    pow_le_pow_left₀ (by linarith) h1 5
  have hsq : Real.sqrt u = w ^ 5 := by
    rw [← hw10, show w ^ 10 = (w ^ 5) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq]
  calc u * (1 + Real.log (1 / u)) ^ 5 ≤ u * (11 * (1 / w)) ^ 5 :=
        mul_le_mul_of_nonneg_left h5 hu0.le
    _ = 11 ^ 5 * w ^ 5 := by
        rw [← hw10]
        field_simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {V : ℕ → Ω → ℝ × ℝ}

/-! ## The passive coordinates -/

omit [IsProbabilityMeasure P] in
theorem IIDSeqE.iidSeq_pas (hV : IIDSeqE P V) : IIDSeq P (fun t ω => (V t ω).2) := by
  have h := hV.comp Prod.snd measurable_snd
  exact ⟨h.measurable, h.indep, h.ident⟩

omit [IsProbabilityMeasure P] in
/-- All passive coordinates are a.s. positive when the passive law charges no `(-∞, 0]`. -/
theorem IIDSeqE.ae_pos_snd_all (hV : IIDSeqE P V) {ν : Measure ℝ}
    (hν : P.map (fun ω => (V 0 ω).2) = ν) (hpos : ν (Iic 0) = 0) :
    ∀ᵐ ω ∂P, ∀ i, 0 < (V i ω).2 := by
  have hY := hV.iidSeq_pas
  refine ae_all_iff.2 fun i => ?_
  have hmap : P.map (fun ω => (V i ω).2) = ν := by
    rw [(hY.ident i).map_eq]; exact hν
  have h0 : P ((fun ω => (V i ω).2) ⁻¹' Iic 0) = 0 := by
    rw [← Measure.map_apply (hY.measurable i) measurableSet_Iic, hmap, hpos]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  simpa using hω

omit [IsProbabilityMeasure P] in
/-- `P(Y_0 < s) ≤ D s`. -/
theorem measure_snd_lt_le (hV : IIDSeqE P V) {ν : Measure ℝ}
    (hν : P.map (fun ω => (V 0 ω).2) = ν) (hpos : ν (Iic 0) = 0) {D : ℝ} (hD : LocBd D ν)
    (hD0 : 0 ≤ D) (s : ℝ) :
    P {ω | (V 0 ω).2 < s} ≤ ENNReal.ofReal (D * s) := by
  have hm : Measurable fun ω => (V 0 ω).2 := (hV.measurable 0).snd
  have e1 : P {ω | (V 0 ω).2 < s} = ν (Iio s) := by
    rw [← hν, Measure.map_apply hm measurableSet_Iio]; rfl
  rw [e1]
  have hsub : Iio s ⊆ Iic 0 ∪ Ioo 0 s := by
    intro x hx
    rcases le_or_gt x 0 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hx⟩
  calc ν (Iio s) ≤ ν (Iic 0 ∪ Ioo 0 s) := measure_mono hsub
    _ ≤ ν (Iic 0) + ν (Ioo 0 s) := measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal D * volume (Ioo (0 : ℝ) s) := by
        rw [hpos]; exact add_le_add le_rfl (hD _ measurableSet_Ioo)
    _ = ENNReal.ofReal (D * s) := by
        rw [zero_add, Real.volume_Ioo, sub_zero, ENNReal.ofReal_mul hD0]

/-- `E|X - Y| ≤ δ` from `E (X - Y)² ≤ δ²`, and integrability. -/
theorem integral_abs_sub_le (hV : IIDSeqE P V) {δ : ℝ} (hδ : 0 < δ)
    (hDi : Integrable (fun ω => ((V 0 ω).1 - (V 0 ω).2) ^ 2) P)
    (hDle : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P ≤ δ ^ 2) :
    Integrable (fun ω => |(V 0 ω).1 - (V 0 ω).2|) P ∧
      ∫ ω, |(V 0 ω).1 - (V 0 ω).2| ∂P ≤ δ := by
  have hf : Measurable fun p : ℝ × ℝ => |p.1 - p.2| :=
    continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)
  have hpt : ∀ x : ℝ, |x| ≤ (x ^ 2 / δ + δ) / 2 := fun x => by
    rw [show (x ^ 2 / δ + δ) / 2 = (x ^ 2 + δ ^ 2) / (2 * δ) by field_simp,
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|x| - δ), sq_abs x]
  have hbd : Integrable (fun ω => (((V 0 ω).1 - (V 0 ω).2) ^ 2 / δ + δ) / 2) P :=
    ((hDi.div_const δ).add (integrable_const δ)).div_const 2
  have hint : Integrable (fun ω => |(V 0 ω).1 - (V 0 ω).2|) P :=
    hbd.mono' (hf.comp (hV.measurable 0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_abs]; exact hpt _)
  refine ⟨hint, ?_⟩
  calc ∫ ω, |(V 0 ω).1 - (V 0 ω).2| ∂P
      ≤ ∫ ω, (((V 0 ω).1 - (V 0 ω).2) ^ 2 / δ + δ) / 2 ∂P :=
        integral_mono hint hbd fun ω => hpt _
    _ = ((∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P) / δ + δ) / 2 := by
        rw [integral_div, integral_add (hDi.div_const δ) (integrable_const δ), integral_div]
        simp
    _ ≤ (δ ^ 2 / δ + δ) / 2 := by gcongr
    _ = δ := by field_simp; ring

/-- **Residual bound** (Markov): `P(∑_{j<R} |X_j - Y_j| > h) ≤ R δ / h`. -/
theorem measure_resid_gt_le (hV : IIDSeqE P V) {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hDi : Integrable (fun ω => ((V 0 ω).1 - (V 0 ω).2) ^ 2) P)
    (hDle : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P ≤ δ ^ 2) (R : ℕ) :
    P {ω | h < ∑ j ∈ range R, |(V j ω).1 - (V j ω).2|} ≤ ENNReal.ofReal (R * δ / h) := by
  have hf : Measurable fun p : ℝ × ℝ => |p.1 - p.2| :=
    continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)
  obtain ⟨hint0, hle0⟩ := integral_abs_sub_le hV hδ hDi hDle
  have hint : ∀ j, Integrable (fun ω => |(V j ω).1 - (V j ω).2|) P := fun j =>
    ((hV.ident j).comp hf).integrable_iff.mpr hint0
  have hS : Integrable (fun ω => ∑ j ∈ range R, |(V j ω).1 - (V j ω).2|) P :=
    integrable_finsetSum _ fun j _ => hint j
  have hSint : ∫ ω, ∑ j ∈ range R, |(V j ω).1 - (V j ω).2| ∂P ≤ R * δ := by
    rw [integral_finsetSum _ fun j _ => hint j]
    calc ∑ j ∈ range R, ∫ ω, |(V j ω).1 - (V j ω).2| ∂P
        = ∑ _j ∈ range R, ∫ ω, |(V 0 ω).1 - (V 0 ω).2| ∂P :=
          sum_congr rfl fun j _ => hV.integral_comp hf j
      _ ≤ ∑ _j ∈ range R, δ := sum_le_sum fun _ _ => hle0
      _ = R * δ := by rw [sum_const, card_range, nsmul_eq_mul]
  have hM := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => sum_nonneg fun j _ => abs_nonneg _) hS h
  have hreal : P.real {ω | h ≤ ∑ j ∈ range R, |(V j ω).1 - (V j ω).2|} ≤ R * δ / h := by
    rw [le_div_iff₀ hh, mul_comm]
    exact hM.trans hSint
  calc P {ω | h < ∑ j ∈ range R, |(V j ω).1 - (V j ω).2|}
      ≤ P {ω | h ≤ ∑ j ∈ range R, |(V j ω).1 - (V j ω).2|} :=
        measure_mono (ofPred_subset_ofPred.2 fun _ hω => hω.le)
    _ = ENNReal.ofReal (P.real {ω | h ≤ ∑ j ∈ range R, |(V j ω).1 - (V j ω).2|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (R * δ / h) := ENNReal.ofReal_le_ofReal hreal

omit [IsProbabilityMeasure P] in
/-- **Passive stopping tail** on the pair space. -/
theorem measure_pasLen_gt_le (hV : IIDSeqE P V) {ν : ProbabilityMeasure ℝ}
    (hν : P.map (fun ω => (V 0 ω).2) = (ν : Measure ℝ)) {b β vmin eps : ℝ} (hvmin0 : 0 < vmin)
    (heps : epsZero b β ≤ eps) (hρ : MomClass b β vmin ν) (m : ℕ) :
    P {ω | (m : ℕ∞) < pasLen eps V ω} ≤
      ENNReal.ofReal (72 / 71 * Real.exp (-(tailRate * vmin) * m / eps ^ 2)) := by
  have hY := hV.iidSeq_pas
  have hmap := map_seq_eq_iidLaw hY ν hν.symm
  calc P {ω | (m : ℕ∞) < pasLen eps V ω}
      = P (seq (fun t ω => (V t ω).2) ⁻¹' {g | (m : ℕ∞) < gapSegLen eps g}) := rfl
    _ ≤ P.map (seq (fun t ω => (V t ω).2)) {g | (m : ℕ∞) < gapSegLen eps g} :=
        Measure.le_map_apply (measurable_seq hY.measurable).aemeasurable _
    _ = iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} := by rw [hmap]
    _ ≤ _ := gapSegLen_tail hvmin0 heps hρ m

omit [IsProbabilityMeasure P] in
/-- The passive coordinates form a `LocalGapLaw` with mean one and constant `D`. -/
theorem localGapLaw_snd (hV : IIDSeqE P V) {ν : ProbabilityMeasure ℝ}
    (hν : P.map (fun ω => (V 0 ω).2) = (ν : Measure ℝ)) (hpos : (ν : Measure ℝ) (Iic 0) = 0)
    (hmean : lawMean ν = 1) {D : ℝ} (hD : LocBd D ν) :
    LocalGapLaw P (fun t ω => (V t ω).2) 1 D := by
  have hY := hV.iidSeq_pas
  have hm : Measurable fun ω => (V 0 ω).2 := hY.measurable 0
  refine ⟨hY, ?_, ?_, one_pos, fun A hA => ?_⟩
  · filter_upwards [hV.ae_pos_snd_all hν hpos] with ω hω using hω 0
  · have := integral_map (μ := P) hm.aemeasurable (f := fun x : ℝ => x)
      aestronglyMeasurable_id
    rw [hν] at this
    change ∫ ω, (V 0 ω).2 ∂P = 1
    rw [← this]
    exact hmean
  · rw [div_one, ← Measure.map_apply hm hA, hν]
    exact hD A hA


/-! ## The parameters `R = ⌈eps²/(c₀ τ)⌉`, `u = 2 (R + 2 eps) τ³` -/

theorem tree_params {c₀ eps τ : ℝ} {R : ℕ} (hc₀ : 0 < c₀) (heps : 1 ≤ eps) (hτ0 : 0 < τ)
    (hτ : τ ≤ 1 / 2) (hRlo : eps ^ 2 / c₀ / τ ≤ R) (hRhi : (R : ℝ) < eps ^ 2 / c₀ / τ + 1) :
    (R : ℝ) * τ ≤ eps ^ 2 / c₀ + τ ∧ 1 / τ ≤ c₀ * R / eps ^ 2 ∧
      2 * ((R : ℝ) + 2 * eps) * τ ^ 3 ≤ 2 * (1 / c₀ + 3) * eps ^ 2 * τ ^ 2 ∧
      2 * τ ^ 4 ≤ τ := by
  have hepspos : 0 < eps := by linarith
  have hτ1 : τ ≤ 1 := by linarith
  have hRτ : (R : ℝ) * τ ≤ eps ^ 2 / c₀ + τ := by
    have := mul_le_mul_of_nonneg_right hRhi.le hτ0.le
    rwa [add_mul, div_mul_cancel₀ _ hτ0.ne', one_mul] at this
  refine ⟨hRτ, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hRlo hc₀.le
    have e1 : c₀ * (eps ^ 2 / c₀ / τ) = 1 / τ * eps ^ 2 := by field_simp
    linarith
  · have hτ3 : τ ^ 3 ≤ τ ^ 2 := pow_le_pow_of_le_one hτ0.le hτ1 (by norm_num)
    have heps2 : eps ≤ eps ^ 2 := by nlinarith
    have h1 : 2 * ((R : ℝ) + 2 * eps) * τ ^ 3 = 2 * ((R : ℝ) * τ) * τ ^ 2 + 4 * eps * τ ^ 3 := by
      ring
    have h2 : 2 * ((R : ℝ) * τ) * τ ^ 2 ≤ 2 * (eps ^ 2 / c₀ + τ) * τ ^ 2 := by gcongr
    have h5 : τ * τ ^ 2 ≤ eps ^ 2 * τ ^ 2 := by
      have : τ ≤ eps ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg τ)
    have h6 : eps * τ ^ 3 ≤ eps ^ 2 * τ ^ 2 :=
      mul_le_mul heps2 hτ3 (by positivity) (by positivity)
    have e2 : 2 * (1 / c₀ + 3) * eps ^ 2 * τ ^ 2 =
        2 * (eps ^ 2 / c₀) * τ ^ 2 + 2 * (eps ^ 2 * τ ^ 2) + 4 * (eps ^ 2 * τ ^ 2) := by ring
    have e3 : 2 * (eps ^ 2 / c₀ + τ) * τ ^ 2 = 2 * (eps ^ 2 / c₀) * τ ^ 2 + 2 * (τ * τ ^ 2) := by
      ring
    rw [h1, e2]
    linarith
  · have hτ3 : τ ^ 3 ≤ 1 / 8 := by
      calc τ ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hτ0.le hτ 3
        _ = 1 / 8 := by norm_num
    have e1 : 2 * τ ^ 4 = 2 * τ * τ ^ 3 := by ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hτ3 (by positivity : (0 : ℝ) ≤ 2 * τ)
    linarith

/-! ## The four bad events -/

omit [IsProbabilityMeasure P] in
/-- Almost surely, `T_X ≠ T_Y` forces one of the four bad events. -/
theorem treeProb_subset (hpos : ∀ᵐ ω ∂P, ∀ i, 0 < (V i ω).2) {eps τ u : ℝ} {R : ℕ}
    (heps : 1 ≤ eps) (hτ0 : 0 < τ) (h2τ : 2 * τ ^ 4 ≤ τ)
    (hu : 2 * ((R : ℝ) + 2 * eps) * τ ^ 4 ≤ u * τ) :
    ∀ᵐ ω ∂P, ω ∈ {ω | actLen eps V ω ≠ pasLen eps V ω} →
      ω ∈ {ω | (V 0 ω).2 < τ} ∪ {ω | τ ^ 4 < ∑ j ∈ range R, |(V j ω).1 - (V j ω).2|} ∪
        {ω | (R : ℕ∞) < pasLen eps V ω} ∪
        {ω | ∃ t : ℕ, gapSegLen eps (seq (fun t ω => (V t ω).2) ω) = t ∧
          (nearTie eps u (gapKeys (seq (fun t ω => (V t ω).2) ω)) t ∨
            nearTie eps u (gapKeys (seq (fun t ω => (V t ω).2) ω)) (t + 1))} := by
  filter_upwards [hpos] with ω hpos hB
  by_contra hc
  simp only [mem_union, not_or] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  simp only [mem_ofPred_eq, not_lt, not_exists, not_and] at h1 h2 h3 h4
  obtain ⟨t, htdef, htR⟩ := ENat.le_natCast_iff.mp h3
  have hT : gapSegLen eps (fun i => (V i ω).2) = t := htdef
  have hnt := h4 t hT
  simp only [not_or] at hnt
  have hres : ∀ k ≤ R, |gapKeys (fun i => (V i ω).1) k - gapKeys (fun i => (V i ω).2) k| ≤
      τ ^ 4 := fun k hk =>
    (abs_gapKeys_sub_le (fun i => (V i ω).1) (fun i => (V i ω).2) hk).trans h2
  have hxs : gapSegLen eps (fun i => (V i ω).1) = t :=
    gapSegLen_eq_of_close heps hτ0 (by positivity) h2τ hu (fun i => (hpos i).le) h1 hres hT htR
      hnt.1 hnt.2
  exact hB (hxs.trans htdef.symm)

/-- The measure of `T_X ≠ T_Y` is at most the sum of the four event bounds. -/
theorem treeProb_measure_le {D θ vlo vhi eps τ u : ℝ} {R : ℕ} (hV : IIDSeqE P V)
    {ν : ProbabilityMeasure ℝ} (hν : P.map (fun ω => (V 0 ω).2) = (ν : Measure ℝ))
    (hreg : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) (hτ0 : 0 < τ) (h2τ : 2 * τ ^ 4 ≤ τ)
    (hDi : Integrable (fun ω => ((V 0 ω).1 - (V 0 ω).2) ^ 2) P)
    (hDle : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P ≤ τ ^ 12)
    (hu0 : 0 < u) (hu2 : u ≤ 1 / 2) (hu : 2 * ((R : ℝ) + 2 * eps) * τ ^ 4 ≤ u * τ) :
    P {ω | actLen eps V ω ≠ pasLen eps V ω} ≤
      ENNReal.ofReal (D * τ + R * τ ^ 6 / τ ^ 4 +
        72 / 71 * Real.exp (-(tailRate * regV vlo) * R / eps ^ 2) +
        (trKM D vlo * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 + 72 / 71 * u)) := by
  have hM := hreg.momClass hθ hvlo
  have hD0 : 0 ≤ D := hreg.D_nonneg
  have hloc : LocBd D (ν : Measure ℝ) := hreg.envBd.locBd hD0 hθ.le
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hc₀ : 0 < trC vlo := trC_pos hvlo
  have hsub := treeProb_subset (hV.ae_pos_snd_all hν hM.pos) heps1 hτ0 h2τ hu
  have hP1 := measure_snd_lt_le hV hν hM.pos hloc hD0 τ
  have hP2 := measure_resid_gt_le hV (pow_pos hτ0 6) (pow_pos hτ0 4) hDi
    (by rw [← pow_mul]; exact hDle) R
  have hP3 := measure_pasLen_gt_le hV hν (regV_pos hvlo) heps hM R
  have hP4 := (localGapLaw_snd hV hν hM.pos hM.mean hloc).stopped_margin_segLen heps1 hu0 hu2
    (by norm_num : (0 : ℝ) ≤ 72 / 71) hc₀ (fun R' _ => by
      refine (measure_pasLen_gt_le hV hν (regV_pos hvlo) heps hM R').trans (le_of_eq ?_)
      simp only [trC, neg_mul, neg_div])
  refine (measure_mono_ae hsub).trans ?_
  refine ((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)).trans ?_
  have hnn1 : 0 ≤ D * τ := by positivity
  have hnn2 : 0 ≤ (R : ℝ) * τ ^ 6 / τ ^ 4 := by positivity
  have hnn3 : 0 ≤ 72 / 71 * Real.exp (-(tailRate * regV vlo) * R / eps ^ 2) := by positivity
  have hlog0 : 0 ≤ Real.log (1 / u) :=
    Real.log_nonneg (by rw [le_div_iff₀ hu0]; linarith)
  have hnn4 : 0 ≤ trKM D vlo * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 + 72 / 71 * u := by
    have := trKM_nonneg hD0 hvlo
    have : 0 ≤ eps := by linarith
    positivity
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hnn1 hnn2) hnn3) hnn4,
    ENNReal.ofReal_add (add_nonneg hnn1 hnn2) hnn3, ENNReal.ofReal_add hnn1 hnn2]
  gcongr
  exact hP4

/-! ## Arithmetic of the final bound -/

theorem treeProb_arith_large {D c₀ KM κ eps τ u : ℝ} (hD0 : 0 ≤ D) (hc₀ : 0 < c₀)
    (hKM : 0 ≤ KM) (hκ0 : 0 ≤ κ) (heps : 1 ≤ eps) (hτ0 : 0 < τ) (hu2 : 1 / 2 < u)
    (hsqrtu : Real.sqrt u ≤ κ * eps * τ) :
    1 ≤ (D + 1 / c₀ + 1 + 72 / 71 + (KM * 11 ^ 5 + 72 / 71 + 2) * κ) * eps ^ 11 * τ := by
  have h1 : 1 / 2 < κ * eps * τ := by
    have : (1 : ℝ) / 2 < Real.sqrt u := by
      rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    linarith
  have h2 : κ * eps * τ ≤ κ * eps ^ 11 * τ := by
    have := pow_le_pow_right₀ heps (by norm_num : 1 ≤ 11)
    rw [pow_one] at this
    gcongr
  have h3 : 0 ≤ (D + 1 / c₀ + 1 + 72 / 71 + (KM * 11 ^ 5 + 72 / 71) * κ) * (eps ^ 11 * τ) := by
    positivity
  have e1 : (D + 1 / c₀ + 1 + 72 / 71 + (KM * 11 ^ 5 + 72 / 71 + 2) * κ) * eps ^ 11 * τ =
      (D + 1 / c₀ + 1 + 72 / 71 + (KM * 11 ^ 5 + 72 / 71) * κ) * (eps ^ 11 * τ) +
        2 * (κ * eps ^ 11 * τ) := by ring
  rw [e1]
  linarith

theorem treeProb_arith {D c₀ KM κ eps τ u : ℝ} {R : ℕ} (hD0 : 0 ≤ D) (hc₀ : 0 < c₀)
    (hKM : 0 ≤ KM) (hκ0 : 0 ≤ κ) (heps : 1 ≤ eps) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hu0 : 0 < u)
    (hu1 : u ≤ 1) (hsqrtu : Real.sqrt u ≤ κ * eps * τ) (hRτ : (R : ℝ) * τ ≤ eps ^ 2 / c₀ + τ)
    (hexp : 72 / 71 * Real.exp (-c₀ * R / eps ^ 2) ≤ 72 / 71 * τ) :
    D * τ + R * τ ^ 6 / τ ^ 4 + 72 / 71 * Real.exp (-c₀ * R / eps ^ 2) +
        (KM * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 + 72 / 71 * u) ≤
      (D + 1 / c₀ + 1 + 72 / 71 + (KM * 11 ^ 5 + 72 / 71 + 2) * κ) * eps ^ 11 * τ := by
  have hepspos : 0 < eps := by linarith
  have heps11 : ∀ k : ℕ, k ≤ 11 → eps ^ k ≤ eps ^ 11 := fun k hk => pow_le_pow_right₀ heps hk
  have h1e : (1 : ℝ) ≤ eps ^ 11 := one_le_pow₀ heps
  have hlog := mul_one_add_log_pow_le hu0 hu1
  have hsu : u ≤ Real.sqrt u := by
    calc u = Real.sqrt u * Real.sqrt u := (Real.mul_self_sqrt hu0.le).symm
      _ ≤ Real.sqrt u * 1 := by
          gcongr
          rw [Real.sqrt_le_one]; exact hu1
      _ = Real.sqrt u := mul_one _
  have hE2 : (R : ℝ) * τ ^ 6 / τ ^ 4 ≤ (eps ^ 2 / c₀ + 1) * τ := by
    rw [div_le_iff₀ (by positivity)]
    have e1 : (R : ℝ) * τ ^ 6 = (R * τ) * τ ^ 5 := by ring
    rw [e1]
    have h1 : (R : ℝ) * τ * τ ^ 5 ≤ (eps ^ 2 / c₀ + τ) * τ ^ 5 :=
      mul_le_mul_of_nonneg_right hRτ (by positivity)
    have h2 : (eps ^ 2 / c₀ + τ) * τ ^ 5 ≤ (eps ^ 2 / c₀ + 1) * τ * τ ^ 4 := by
      have e2 : (eps ^ 2 / c₀ + τ) * τ ^ 5 = (eps ^ 2 / c₀ + τ) * τ * τ ^ 4 := by ring
      rw [e2]; gcongr
    linarith
  have hE4 : KM * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 + 72 / 71 * u ≤
      (KM * 11 ^ 5 + 72 / 71) * κ * eps ^ 11 * τ := by
    have h1 : KM * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 ≤
        KM * eps ^ 10 * (11 ^ 5 * Real.sqrt u) := by
      rw [mul_assoc (KM * eps ^ 10)]
      gcongr
    have h2 : 72 / 71 * u ≤ 72 / 71 * Real.sqrt u := by gcongr
    have h3 : (KM * 11 ^ 5 * eps ^ 10 + 72 / 71) * Real.sqrt u ≤
        (KM * 11 ^ 5 * eps ^ 10 + 72 / 71) * (κ * eps * τ) := by gcongr
    have h4 : (KM * 11 ^ 5 * eps ^ 10 + 72 / 71) * (κ * eps * τ) ≤
        (KM * 11 ^ 5 + 72 / 71) * κ * eps ^ 11 * τ := by
      have e1 : (KM * 11 ^ 5 * eps ^ 10 + 72 / 71) * (κ * eps * τ) =
          KM * 11 ^ 5 * κ * eps ^ 11 * τ + 72 / 71 * κ * (eps * τ) := by ring
      have e2 : (KM * 11 ^ 5 + 72 / 71) * κ * eps ^ 11 * τ =
          KM * 11 ^ 5 * κ * eps ^ 11 * τ + 72 / 71 * κ * (eps ^ 11 * τ) := by ring
      rw [e1, e2]
      have := heps11 1 (by norm_num)
      rw [pow_one] at this
      gcongr
    have e3 : KM * eps ^ 10 * (11 ^ 5 * Real.sqrt u) + 72 / 71 * Real.sqrt u =
        (KM * 11 ^ 5 * eps ^ 10 + 72 / 71) * Real.sqrt u := by ring
    linarith
  have hA11 : eps ^ 2 / c₀ ≤ 1 / c₀ * eps ^ 11 := by
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left (heps11 2 (by norm_num)) (by positivity)
  have t1 : D * τ ≤ D * eps ^ 11 * τ := by
    have := mul_le_mul_of_nonneg_left h1e hD0
    exact mul_le_mul_of_nonneg_right (by linarith) hτ0.le
  have t2 : (eps ^ 2 / c₀ + 1) * τ ≤ (1 / c₀ + 1) * eps ^ 11 * τ := by
    have : eps ^ 2 / c₀ + 1 ≤ (1 / c₀ + 1) * eps ^ 11 := by linarith
    exact mul_le_mul_of_nonneg_right this hτ0.le
  have t3 : 72 / 71 * τ ≤ 72 / 71 * eps ^ 11 * τ := by
    have := mul_le_mul_of_nonneg_left h1e (by norm_num : (0 : ℝ) ≤ 72 / 71)
    exact mul_le_mul_of_nonneg_right (by linarith) hτ0.le
  have t4 : 0 ≤ 2 * κ * eps ^ 11 * τ := by positivity
  have e1 : (D + 1 / c₀ + 1 + 72 / 71 + (KM * 11 ^ 5 + 72 / 71 + 2) * κ) * eps ^ 11 * τ =
      D * eps ^ 11 * τ + (1 / c₀ + 1) * eps ^ 11 * τ + 72 / 71 * eps ^ 11 * τ +
        (KM * 11 ^ 5 + 72 / 71) * κ * eps ^ 11 * τ + 2 * κ * eps ^ 11 * τ := by ring
  rw [e1]
  linarith

/-! ## The tree-switch probability -/

/-- **(tree-prob)**: `P(T_X ≠ T_Y) ≤ treeK D vlo · eps¹¹ · τ` when `E (X - Y)² ≤ τ¹²`. -/
theorem treeProb_le {D θ vlo vhi eps τ : ℝ} (hV : IIDSeqE P V) {ν : ProbabilityMeasure ℝ}
    (hν : P.map (fun ω => (V 0 ω).2) = (ν : Measure ℝ)) (hreg : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps)
    (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2)
    (hDi : Integrable (fun ω => ((V 0 ω).1 - (V 0 ω).2) ^ 2) P)
    (hDle : ∫ ω, ((V 0 ω).1 - (V 0 ω).2) ^ 2 ∂P ≤ τ ^ 12) :
    P.real {ω | actLen eps V ω ≠ pasLen eps V ω} ≤ treeK D vlo * eps ^ 11 * τ := by
  have hD0 : 0 ≤ D := hreg.D_nonneg
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hepspos : 0 < eps := by linarith
  have hc₀ : 0 < trC vlo := trC_pos hvlo
  have hKM : 0 ≤ trKM D vlo := trKM_nonneg hD0 hvlo
  have hκ0 : 0 ≤ trKappa vlo := Real.sqrt_nonneg _
  have hκ2 : trKappa vlo ^ 2 = 2 * (1 / trC vlo + 3) := Real.sq_sqrt (by positivity)
  have hτ1 : τ ≤ 1 := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = ⌈eps ^ 2 / trC vlo / τ⌉₊ := ⟨_, rfl⟩
  have hRlo : eps ^ 2 / trC vlo / τ ≤ R := hR ▸ Nat.le_ceil _
  have hRhi : (R : ℝ) < eps ^ 2 / trC vlo / τ + 1 := hR ▸ Nat.ceil_lt_add_one (by positivity)
  obtain ⟨hRτ, hRexp, hu3, h2τ⟩ := tree_params hc₀ heps1 hτ0 hτ hRlo hRhi
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 * ((R : ℝ) + 2 * eps) * τ ^ 3 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hsqrtu : Real.sqrt u ≤ trKappa vlo * eps * τ := by
    rw [show trKappa vlo * eps * τ = Real.sqrt ((trKappa vlo * eps * τ) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [hu, mul_pow, mul_pow, hκ2]
    linarith
  have hK : treeK D vlo = D + 1 / trC vlo + 1 + 72 / 71 +
      (trKM D vlo * 11 ^ 5 + 72 / 71 + 2) * trKappa vlo := rfl
  have hKe : 0 ≤ treeK D vlo * eps ^ 11 * τ := by
    have := treeK_nonneg hD0 hvlo
    positivity
  rcases le_or_gt u (1 / 2) with hu2 | hu2
  · have hB := treeProb_measure_le hV hν hreg hθ hvlo heps hτ0 h2τ hDi hDle hu0 hu2
      (le_of_eq (by rw [hu]; ring))
    have hexp : 72 / 71 * Real.exp (-trC vlo * R / eps ^ 2) ≤ 72 / 71 * τ := by
      gcongr
      calc Real.exp (-trC vlo * R / eps ^ 2) ≤ Real.exp (-(1 / τ)) :=
            Real.exp_le_exp.2 (by rw [neg_mul, neg_div]; linarith)
        _ ≤ τ := by
            rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) hτ0, ← one_div]
            linarith [Real.add_one_le_exp (1 / τ)]
    have harith := treeProb_arith hD0 hc₀ hKM hκ0 heps1 hτ0 hτ1 hu0 (by linarith) hsqrtu hRτ hexp
    rw [← hK] at harith
    simp only [trC] at harith
    exact ENNReal.toReal_le_of_le_ofReal hKe (hB.trans (ENNReal.ofReal_le_ofReal harith))
  · exact measureReal_le_one.trans
      (hK ▸ treeProb_arith_large hD0 hc₀ hKM hκ0 heps1 hτ0 hu2 hsqrtu)

end

end PGM
