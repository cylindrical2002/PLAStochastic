import PLAStochastic.Swing.FirstSegment.RejectionSplit
import PLAStochastic.ForMathlib.Probability.Moments.IntegerGridExpTail
import PLAStochastic.Swing.FirstSegment.MeanAndWeakLimit

/-! # Lemma G.1: uniform moments at the actual first restart

The upper layer is charged in `NativeFirstSelectedTail`, the lower layer is the
reflected upper layer by `NativeFirstReflection`, and `NativeFirstRejectionSplit`
shows the two layers exhaust the first rejection.  This file assembles the
exponential tail of the genuine selected increment and the resulting uniform
moment bound for the first-restart margin.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : ℕ → Ω → ℝ}

/-- Both rejection layers together with a large selected increment. -/
def nativeFirstSelectedTailEvent (Z : ℕ → Ω → ℝ) (E t : ℝ) : Set Ω :=
  ⋃ n, (nativeFirstUpperRejectionEvent Z E n ∪ nativeFirstLowerRejectionEvent Z E n) ∩
    {ω | t < |Z (n+1) ω|}

omit [MeasurableSpace Ω] in
theorem nativeFirstLowerPositiveEvent_eq (Z : ℕ → Ω → ℝ) (E t : ℝ) :
    nativeFirstLowerPositiveEvent Z E t =
      ⋃ n, nativeFirstLowerRejectionEvent Z E n ∩ {ω | Z (n+1) ω < -t} := by
  ext ω
  simp only [nativeFirstLowerPositiveEvent, nativeFirstUpperPositiveEvent, mem_iUnion,
    mem_inter_iff, mem_ofPred_eq]
  constructor <;> rintro ⟨n, hn, hz⟩ <;> refine ⟨n, ?_, ?_⟩
  · rw [nativeFirstLowerRejectionEvent_eq_neg]; exact hn
  · change -Z (n+1) ω > t at hz; linarith
  · rw [nativeFirstLowerRejectionEvent_eq_neg] at hn; exact hn
  · show t < -Z (n+1) ω
    linarith

/-- Either genuine rejection layer with a large selected increment is covered by the
two positive layers and the single Gaussian cone envelope. -/
theorem nativeFirstSelectedTailEvent_cover_ae
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) (t : ℝ) :
    ∀ᵐ ω ∂μ, ω ∈ nativeFirstSelectedTailEvent Z E t →
      ω ∈ ((nativeFirstUpperPositiveEvent Z E t ∪ nativeFirstLowerPositiveEvent Z E t) ∪
        {ω | t < nativeFirstSlopeEnvelope Z ω} : Set Ω) := by
  filter_upwards [nativeFirst_feasible_slope_bound_ae hZ hi hG] with ω he
  intro hω
  obtain ⟨n, hn⟩ := mem_iUnion.mp hω
  rcases hn with ⟨hlayer, hbig⟩
  change t < |Z (n+1) ω| at hbig
  rcases hlayer with hup | hlow
  · have hs := nativeFirstUpperRejectionEvent_spec Z E n hup
    by_cases hpos : t < Z (n+1) ω
    · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨n, hup, hpos⟩))
    · have hneg : Z (n+1) ω < -t := by
        rcases lt_or_ge (Z (n+1) ω) 0 with h | h
        · have ht' : t < -Z (n+1) ω := by rwa [abs_of_neg h] at hbig
          linarith
        · exact absurd (by rwa [abs_of_nonneg h] at hbig) hpos
      refine Or.inr ?_
      have hS : |(nativeFirstPrefixState (cumulativeSamples Z) E n ω).1| ≤
          nativeFirstSlopeEnvelope Z ω := he E hE (n+1) (by omega) hs.1 hs.2.1 _ hs.2.2.1
      have hchain : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).1 < -t :=
        lt_of_le_of_lt hs.2.2.2 (lt_trans hup.2 hneg)
      have habs : t < |(nativeFirstPrefixState (cumulativeSamples Z) E n ω).1| := by
        rcases lt_or_ge t 0 with ht0 | ht0
        · exact lt_of_lt_of_le ht0 (abs_nonneg _)
        · rw [abs_of_neg (by linarith : (nativeFirstPrefixState (cumulativeSamples Z) E n ω).1 < 0)]
          linarith
      exact lt_of_lt_of_le habs hS
  · have hs := nativeFirstLowerRejectionEvent_spec Z E n hlow
    by_cases hneg : Z (n+1) ω < -t
    · refine Or.inl (Or.inr ?_)
      rw [nativeFirstLowerPositiveEvent_eq]
      exact mem_iUnion.mpr ⟨n, hlow, hneg⟩
    · have hpos : t < Z (n+1) ω := by
        rcases lt_or_ge (Z (n+1) ω) 0 with h | h
        · exact absurd (by rw [abs_of_neg h] at hbig; linarith) hneg
        · rwa [abs_of_nonneg h] at hbig
      refine Or.inr ?_
      have hl : |nativeFirstConeLower (cumulativeSamples Z) E n ω| ≤ nativeFirstSlopeEnvelope Z ω :=
        he E hE (n+1) (by omega) hs.1 hs.2.1 _ hs.2.2.1
      have hchain : t < nativeFirstConeLower (cumulativeSamples Z) E n ω :=
        lt_of_lt_of_le (lt_of_lt_of_le hpos hlow.2.le) hs.2.2.2
      exact lt_of_lt_of_le (lt_of_lt_of_le hchain (le_abs_self _)) hl

def nativeFirstSelectedTailConstant : ℝ :=
  2*nativeFirstUpperTailConstant+nativeFirstSlopeEnvelopeTailConstant

theorem nativeFirstSelectedTailConstant_nonneg : 0 ≤ nativeFirstSelectedTailConstant := by
  dsimp [nativeFirstSelectedTailConstant, nativeFirstUpperTailConstant,
    nativeFirstSlopeEnvelopeTailConstant]
  have h₁ : 0 < nativeGaussianEnvelopeTailConstant := nativeGaussianEnvelope_tail_constant_pos
  have h₂ : 0 < gaussianChargingConstant := gaussianChargingConstant_pos
  have h₃ : 0 < gaussianChargingCutoffConstant := gaussianChargingCutoffConstant_pos
  have h₄ : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  nlinarith

/-- The uniform exponential tail of the whole first-rejection layer. -/
theorem measureReal_nativeFirstSelectedTailEvent_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) {t : ℝ} (ht : 2 < t) :
    μ.real (nativeFirstSelectedTailEvent Z E t) ≤
      nativeFirstSelectedTailConstant*Real.exp (-t/25600) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE0 : 0 ≤ E := by linarith
  have hcov := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (nativeFirstSelectedTailEvent_cover_ae hZ hi hG hE0 t))
  have hsplit := measureReal_union_le (μ := μ)
    (nativeFirstUpperPositiveEvent Z E t ∪ nativeFirstLowerPositiveEvent Z E t)
    {ω | t < nativeFirstSlopeEnvelope Z ω}
  have hsplit' := measureReal_union_le (μ := μ)
    (nativeFirstUpperPositiveEvent Z E t) (nativeFirstLowerPositiveEvent Z E t)
  have hu := measureReal_nativeFirstUpperPositiveEvent_le hZ hi hG hE ht
  have hl := measureReal_nativeFirstLowerPositiveEvent_le hZ hi hG hE ht
  have henv := nativeFirstSlopeEnvelope_tail_bound hZ hi hG (t := t) (by linarith)
  have hcomp : Real.exp (-t^2/1600) ≤ Real.exp (-t/25600) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hC : 0 ≤ nativeFirstSlopeEnvelopeTailConstant := by
    dsimp [nativeFirstSlopeEnvelopeTailConstant]
    have h₁ : 0 < nativeGaussianEnvelopeTailConstant := nativeGaussianEnvelope_tail_constant_pos
    have h₄ : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    nlinarith
  have henv' := henv.trans (mul_le_mul_of_nonneg_left hcomp hC)
  change μ.real (nativeFirstSelectedTailEvent Z E t) ≤ _ at hcov
  dsimp [nativeFirstSelectedTailConstant]
  nlinarith [hcov.trans hsplit, hsplit', hu, hl, henv']

/-- The genuine increment selected by the actual first rejection. -/
def nativeFirstSelectedIncrement (Z : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  Z (nativeFirstDuration Z E ω) ω

theorem nativeFirstSelectedIncrement_measurable
    (hZ : ∀ j, Measurable (Z j)) {E : ℝ} (hE : 0 ≤ E) :
    Measurable (nativeFirstSelectedIncrement Z E) := by
  have hpair : Measurable (fun p : ℕ × Ω => Z p.1 p.2) :=
    measurable_from_prod_countable_right (fun n => hZ n)
  exact hpair.comp ((nativeFirstDuration_measurable hZ hE).prodMk measurable_id)

/-- On the actual finite-rejection event a large selected increment lands in the
covered layer. -/
theorem nativeFirstSelected_mem_tailEvent_ae
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) (t : ℝ) :
    ∀ᵐ ω ∂μ, t < |nativeFirstSelectedIncrement Z E ω| →
      ω ∈ nativeFirstSelectedTailEvent Z E t := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hts : StrictMono (fun n : ℕ => (n : ℝ)) := by
    intro a b hab
    change (a : ℝ) < b
    exact_mod_cast hab
  filter_upwards [firstRepairReject_ae_finite_gaussian hZ hi hG (ε := 2*E) (by linarith)]
    with ω hfin
  intro hbig
  have hcone : ∀ j, nativePrefixFeasible (fun n => (n : ℝ))
      (fun n => cumulativeSamples Z n ω) E 0 j (cumulativeSamples Z 0 ω) ↔
        j < firstRepairSpan Z (2*E) ω := fun j =>
    (nativePrefix_trueAnchor_iff _ _ hts E 0 j).trans
      (prefixCone_iff_lt_firstRepairSpan Z (2*E) ω hfin j)
  have hK : 1 < firstRepairSpan Z (2*E) ω :=
    (hcone 1).mp (nativePrefix_singleton _ _ hts hE 0 _)
  obtain ⟨n, hn⟩ : ∃ n, firstRepairSpan Z (2*E) ω = n+2 := ⟨firstRepairSpan Z (2*E) ω-2, by omega⟩
  have hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) (cumulativeSamples Z 0 ω) := (hcone (n+1)).mpr (by omega)
  have hrej : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+2) (cumulativeSamples Z 0 ω) := fun h => by
    have := (hcone (n+2)).mp h
    omega
  have hdur : nativeFirstDuration Z E ω = n+1 := by
    have hd := nativeFirstDuration_eq_span_sub_one Z E hE ω
    rw [hn] at hd
    omega
  have hmem := nativeFirst_rejection_upper_or_lower Z hE n hfit hrej
  refine mem_iUnion.mpr ⟨n, hmem, ?_⟩
  change t < |Z (n+1) ω|
  rwa [nativeFirstSelectedIncrement, hdur] at hbig

/-- Equation (G.1): the actual selected first-rejection increment has a uniform
exponential tail. -/
theorem measureReal_nativeFirstSelectedIncrement_tail
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) {t : ℝ} (ht : 2 < t) :
    μ.real {ω | t < |nativeFirstSelectedIncrement Z E ω|} ≤
      nativeFirstSelectedTailConstant*Real.exp (-t/25600) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE0 : 0 ≤ E := by linarith
  have hsub := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (nativeFirstSelected_mem_tailEvent_ae hZ hi hG hE0 t))
  exact hsub.trans (measureReal_nativeFirstSelectedTailEvent_le hZ hi hG hE ht)

theorem nativeFirstSlopeEnvelopeTailConstant_nonneg :
    0 ≤ nativeFirstSlopeEnvelopeTailConstant := by
  dsimp [nativeFirstSlopeEnvelopeTailConstant]
  have h₁ : 0 < nativeGaussianEnvelopeTailConstant := nativeGaussianEnvelope_tail_constant_pos
  have h₄ : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  nlinarith

/-- The residual of the actual first rejected sample against the selected old line. -/
def nativeFirstNext (Z : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  nativeRestartNext (fun k => Z (1+k)) E (Z 0 ω) ω

/-- The paper's first-restart margin `R_{1,E}=E-|Y_J-Nm|`. -/
def nativeFirstMargin (Z : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  E-|nativeFirstNext Z E ω|

/-- Equation \eqref{eq:firstselectedtail} as displayed.  The paper's range `t ≥ 0`
is covered; the small thresholds are absorbed into the same constant, so no
range restriction is needed at all. -/
theorem measureReal_nativeFirstSelectedIncrement_tail_all
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) (t : ℝ) :
    μ.real {ω | t < |nativeFirstSelectedIncrement Z E ω|} ≤
      nativeFirstSelectedTailConstant*Real.exp (-t/25600) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rcases lt_or_ge 2 t with h | h
  · exact measureReal_nativeFirstSelectedIncrement_tail hZ hi hG hE h
  · have henv : 2*Real.exp 1 ≤ nativeFirstSlopeEnvelopeTailConstant := by
      dsimp [nativeFirstSlopeEnvelopeTailConstant]
      have h₁ : 0 < nativeGaussianEnvelopeTailConstant := nativeGaussianEnvelope_tail_constant_pos
      nlinarith [Real.exp_pos (1 : ℝ)]
    have hup : 0 ≤ nativeFirstUpperTailConstant := by
      dsimp [nativeFirstUpperTailConstant]
      have h₁ : 0 < nativeGaussianEnvelopeTailConstant := nativeGaussianEnvelope_tail_constant_pos
      have h₂ : 0 < gaussianChargingConstant := gaussianChargingConstant_pos
      have h₃ : 0 < gaussianChargingCutoffConstant := gaussianChargingCutoffConstant_pos
      have h₄ : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
      nlinarith
    have hC : 2*Real.exp 1 ≤ nativeFirstSelectedTailConstant := by
      have hdef : nativeFirstSelectedTailConstant =
          2*nativeFirstUpperTailConstant+nativeFirstSlopeEnvelopeTailConstant := rfl
      rw [hdef]
      linarith
    have hexp : Real.exp (-1 : ℝ) ≤ Real.exp (-t/25600) := Real.exp_le_exp.mpr (by linarith)
    have hprod : (1 : ℝ) ≤ 2*Real.exp 1*Real.exp (-1 : ℝ) := by
      rw [mul_assoc, ← Real.exp_add]
      norm_num
    have hone : μ.real {ω | t < |nativeFirstSelectedIncrement Z E ω|} ≤ 1 := measureReal_le_one
    have hCpos : 0 ≤ nativeFirstSelectedTailConstant := by
      nlinarith [Real.exp_pos (1 : ℝ)]
    have hstep : 2*Real.exp 1*Real.exp (-1 : ℝ) ≤
        nativeFirstSelectedTailConstant*Real.exp (-t/25600) :=
      mul_le_mul hC hexp (Real.exp_pos _).le hCpos
    linarith

/-- The genuine first-restart margin is dominated by one `E`-free Gaussian envelope
plus the actual selected increment. -/
theorem nativeFirstMargin_abs_le_ae
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) :
    ∀ᵐ ω ∂μ, |nativeFirstMargin Z E ω| ≤
      nativeFirstSlopeEnvelope Z ω+|nativeFirstSelectedIncrement Z E ω| := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hts : StrictMono (fun n : ℕ => (n : ℝ)) := by
    intro a b hab
    change (a : ℝ) < b
    exact_mod_cast hab
  filter_upwards [firstRepairReject_ae_finite_gaussian hZ hi hG (ε := 2*E) (by linarith),
    nativeFirst_feasible_slope_bound_ae hZ hi hG] with ω hfin he
  set Y : ℕ → Ω → ℝ := fun k => Z (1+k) with hY
  have hcone : ∀ j, nativePrefixFeasible (fun n => (n : ℝ))
      (fun n => cumulativeSamples Z n ω) E 0 j (cumulativeSamples Z 0 ω) ↔
        j < firstRepairSpan Z (2*E) ω := fun j =>
    (nativePrefix_trueAnchor_iff _ _ hts E 0 j).trans
      (prefixCone_iff_lt_firstRepairSpan Z (2*E) ω hfin j)
  have hK : 1 < firstRepairSpan Z (2*E) ω :=
    (hcone 1).mp (nativePrefix_singleton _ _ hts hE 0 _)
  obtain ⟨n, hn⟩ : ∃ n, firstRepairSpan Z (2*E) ω = n+2 := ⟨firstRepairSpan Z (2*E) ω-2, by omega⟩
  have hfit : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+1) 0 := by
    simpa only [cumulativeSamples_zero] using (hcone (n+1)).mpr (by omega)
  have hrej : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples Z j ω)
      E 0 (n+2) 0 := by
    simp only [← cumulativeSamples_zero Z ω]
    intro h
    have := (hcone (n+2)).mp h
    omega
  have hdur : nativeFirstDuration Z E ω = n+1 := by
    have hd := nativeFirstDuration_eq_span_sub_one Z E hE ω
    rw [hn] at hd
    omega
  -- identify the rebased restart length with the actual first duration
  have hfeas : ∀ k, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples Z i ω) E 0 k 0 ↔
        (k : WithTop ℕ) ≤ nativeRestartLength Y E (Z 0 ω) ω := by
    intro k
    simpa [cumulativeSamples, Y] using nativeRestart_feasible_iff Z 0 k E 0 ω
  have hlen : nativeRestartLength Y E (Z 0 ω) ω = ((n+1 : ℕ) : WithTop ℕ) := by
    apply le_antisymm _ ((hfeas (n+1)).mp hfit)
    by_contra hnot
    have hgt : ((n+1 : ℕ) : WithTop ℕ) < nativeRestartLength Y E (Z 0 ω) ω := lt_of_not_ge hnot
    have hnext : ((n+2 : ℕ) : WithTop ℕ) ≤ nativeRestartLength Y E (Z 0 ω) ω := by
      cases heq : nativeRestartLength Y E (Z 0 ω) ω using WithTop.recTopCoe with
      | top => exact le_top
      | coe j =>
        rw [heq] at hgt
        have hj : n+1 < j := WithTop.coe_lt_coe.mp hgt
        exact WithTop.coe_le_coe.mpr (show n+2 ≤ j by omega)
    exact hrej ((hfeas (n+2)).mpr hnext)
  have hf : nativeRestartLength Y E (Z 0 ω) ω ≠ ⊤ := by rw [hlen]; exact WithTop.coe_ne_top
  have hNat : nativeRestartLengthNat Y E (Z 0 ω) ω = n+1 := by
    change (nativeRestartLength Y E (Z 0 ω) ω).untopD 0 = n+1
    rw [hlen]
    rfl
  -- the selected slope is a feasible slope of the original path, hence enveloped
  have hlocal : feasibleSlope (Finset.Icc 1 (n+1)) (fun i => (i : ℝ))
      (fun i => cumulativeSamples Z i ω) 0 0 E (nativeRestartSlope Y E (Z 0 ω) ω) := by
    have hfs := nativeRestartSlope_feasible Y hE (Z 0 ω) ω hf
    rw [hNat] at hfs
    intro i hi
    have heq : nativeCarriedSamples Y (fun _ => Z 0 ω) i ω = cumulativeSamples Z i ω := by
      simpa [Y, cumulativeSamples] using nativeRestart_samples_rebase Z 0 i 0 ω (Finset.mem_Icc.mp hi).1
    simpa only [heq] using hfs i hi
  have hslope : |nativeRestartSlope Y E (Z 0 ω) ω| ≤ nativeFirstSlopeEnvelope Z ω :=
    he E hE (n+1) (by omega) hfit hrej _ hlocal
  have hpos := nativeRestart_margin_pos_le_slope Y hE (Z 0 ω) ω hf
  have hneg := nativeRestart_margin_neg_le_increment Y hE (Z 0 ω) ω hf
  rw [hNat] at hneg
  have hYval : Y (n+1-1) ω = nativeFirstSelectedIncrement Z E ω := by
    simp only [hY, nativeFirstSelectedIncrement, hdur]
    congr 1
    omega
  have hnextEq : nativeRestartNext Y E (Z 0 ω) ω = nativeFirstNext Z E ω := rfl
  rw [hYval, hnextEq] at hneg
  rw [hnextEq] at hpos
  have habs : |nativeFirstMargin Z E ω| =
      max (E-|nativeFirstNext Z E ω|) 0+max (|nativeFirstNext Z E ω|-E) 0 := by
    rcases le_or_gt E |nativeFirstNext Z E ω| with h | h
    · rw [nativeFirstMargin, abs_of_nonpos (by linarith), max_eq_right (by linarith),
        max_eq_left (by linarith)]
      ring
    · rw [nativeFirstMargin, abs_of_nonneg (by linarith), max_eq_left (by linarith),
        max_eq_right (by linarith)]
      ring
  rw [habs]
  exact add_le_add (hpos.trans hslope) hneg

theorem nativeFirstMargin_measurable (hZ : ∀ j, Measurable (Z j)) (E : ℝ) :
    Measurable (nativeFirstMargin Z E) := by
  have h : Measurable (nativeFirstNext Z E) :=
    (nativeRestartNext_measurable (fun k => Z (1+k)) (fun k => hZ (1+k)) E).comp
      ((hZ 0).prodMk measurable_id)
  exact measurable_const.sub h.abs

/-- One `E`-free constant for the dominating tail. -/
def nativeFirstMarginTailConstant : ℝ :=
  (nativeFirstSlopeEnvelopeTailConstant+nativeFirstSelectedTailConstant+1)*Real.exp 1

def nativeFirstMarginMomentBound (k : ℕ) : ℝ :=
  nativeFirstMarginTailConstant*expTailMomentSum (1/51200) k

theorem nativeFirstMarginTailConstant_pos : 0 < nativeFirstMarginTailConstant := by
  have h₁ := nativeFirstSlopeEnvelopeTailConstant_nonneg
  have h₂ := nativeFirstSelectedTailConstant_nonneg
  have h₃ : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
  dsimp [nativeFirstMarginTailConstant]
  nlinarith

/-- The dominating variable has an exponential tail with constants free of `E`. -/
theorem nativeFirstMarginDominant_tail
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) (m : ℕ) :
    μ {ω | (m : ℝ) ≤ nativeFirstSlopeEnvelope Z ω+|nativeFirstSelectedIncrement Z E ω|} ≤
      ENNReal.ofReal (nativeFirstMarginTailConstant*Real.exp (-(1/51200)*(m : ℝ))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set S : Set Ω := {ω | (m : ℝ) ≤ nativeFirstSlopeEnvelope Z ω+
    |nativeFirstSelectedIncrement Z E ω|} with hSdef
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hC1 := nativeFirstSlopeEnvelopeTailConstant_nonneg
  have hC2 := nativeFirstSelectedTailConstant_nonneg
  have hreal : μ.real S ≤ nativeFirstMarginTailConstant*Real.exp (-(1/51200)*(m : ℝ)) := by
    by_cases hm : 7 ≤ m
    · have hmR : (7 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      set t : ℝ := (m : ℝ)/2-1 with htdef
      have ht2 : 2 < t := by rw [htdef]; linarith
      have hcover : S ⊆ {ω | t < nativeFirstSlopeEnvelope Z ω} ∪
          {ω | t < |nativeFirstSelectedIncrement Z E ω|} := by
        intro ω hω
        by_contra hn
        have ha : nativeFirstSlopeEnvelope Z ω ≤ t := le_of_not_gt (fun h => hn (Or.inl h))
        have hb : |nativeFirstSelectedIncrement Z E ω| ≤ t := le_of_not_gt (fun h => hn (Or.inr h))
        have := hω
        rw [hSdef] at this
        simp only [mem_ofPred_eq] at this
        rw [htdef] at ha hb
        linarith
      have henv := nativeFirstSlopeEnvelope_tail_bound hZ hi hG (t := t) (by linarith)
      have hsel := measureReal_nativeFirstSelectedIncrement_tail hZ hi hG hE ht2
      have hcomp : Real.exp (-t^2/1600) ≤ Real.exp (-t/25600) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hstep : Real.exp (-t/25600) ≤ Real.exp 1*Real.exp (-(1/51200)*(m : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [htdef]
        linarith [le_of_lt (by norm_num : (0:ℝ) < 1)]
      have htot := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
      have h1 : μ.real {ω | t < nativeFirstSlopeEnvelope Z ω} ≤
          nativeFirstSlopeEnvelopeTailConstant*Real.exp (-t/25600) :=
        henv.trans (mul_le_mul_of_nonneg_left hcomp hC1)
      dsimp [nativeFirstMarginTailConstant]
      nlinarith [htot, h1, hsel, hstep, Real.exp_pos (-(1/51200)*(m : ℝ))]
    · have hm6 : (m : ℝ) ≤ 6 := by
        have : m ≤ 6 := by omega
        exact_mod_cast this
      have hexp : (1 : ℝ) ≤ Real.exp 1*Real.exp (-(1/51200)*(m : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have hone : μ.real S ≤ 1 := measureReal_le_one
      dsimp [nativeFirstMarginTailConstant]
      nlinarith [Real.exp_pos (-(1/51200)*(m : ℝ))]
  calc
    μ S = ENNReal.ofReal (μ.real S) := by
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

omit [MeasurableSpace Ω] in
theorem nativeFirstSlopeEnvelope_nonneg' (Z : ℕ → Ω → ℝ) (ω : Ω) :
    0 ≤ nativeFirstSlopeEnvelope Z ω := by
  dsimp [nativeFirstSlopeEnvelope]
  have := nativeGaussianEnvelope_nonneg (fun k => Z (1+k)) ω
  have h0 := abs_nonneg (Z 0 ω)
  linarith

/-- Equation (G.2) for natural exponents: a single bound valid for every budget. -/
theorem integral_nativeFirstMargin_pow_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) (k : ℕ) :
    (∫ ω, |nativeFirstMargin Z E ω|^k ∂μ) ≤ nativeFirstMarginMomentBound k := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE0 : 0 ≤ E := by linarith
  set D : Ω → ℝ := fun ω => nativeFirstSlopeEnvelope Z ω+|nativeFirstSelectedIncrement Z E ω| with hD
  have hDm : Measurable D :=
    (nativeFirstSlopeEnvelope_measurable hZ).add
      (nativeFirstSelectedIncrement_measurable hZ hE0).abs
  have hDnn : ∀ᵐ ω ∂μ, 0 ≤ D ω := Eventually.of_forall fun ω => by
    have := nativeFirstSlopeEnvelope_nonneg' Z ω
    have := abs_nonneg (nativeFirstSelectedIncrement Z E ω)
    simp only [hD]; linarith
  have htail := nativeFirstMarginDominant_tail hZ hi hG hE
  have hint : Integrable (fun ω => D ω^k) μ :=
    integrable_pow_of_expTail hDm hDnn nativeFirstMarginTailConstant_pos.le
      (by norm_num : (0 : ℝ) < 1/51200) htail k
  have hmm := nativeFirstMargin_measurable hZ E
  have hdom : ∀ᵐ ω ∂μ, ‖|nativeFirstMargin Z E ω|^k‖ ≤ D ω^k := by
    filter_upwards [nativeFirstMargin_abs_le_ae hZ hi hG hE0] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) hω k
  have hintm : Integrable (fun ω => |nativeFirstMargin Z E ω|^k) μ :=
    hint.mono' (hmm.abs.pow_const k).aestronglyMeasurable hdom
  have hmono : (∫ ω, |nativeFirstMargin Z E ω|^k ∂μ) ≤ ∫ ω, D ω^k ∂μ := by
    apply integral_mono_ae hintm hint
    filter_upwards [nativeFirstMargin_abs_le_ae hZ hi hG hE0] with ω hω
    exact pow_le_pow_left₀ (abs_nonneg _) hω k
  exact hmono.trans (integral_pow_le_of_expTail hDm hDnn nativeFirstMarginTailConstant_pos.le
    (by norm_num : (0 : ℝ) < 1/51200) htail k)

/-- The actual first margin is integrable, with the same `E`-free domination. -/
theorem integrable_nativeFirstMargin_abs
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) :
    Integrable (fun ω => |nativeFirstMargin Z E ω|) μ := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE0 : 0 ≤ E := by linarith
  set D : Ω → ℝ := fun ω => nativeFirstSlopeEnvelope Z ω+|nativeFirstSelectedIncrement Z E ω| with hD
  have hDm : Measurable D :=
    (nativeFirstSlopeEnvelope_measurable hZ).add
      (nativeFirstSelectedIncrement_measurable hZ hE0).abs
  have hDnn : ∀ᵐ ω ∂μ, 0 ≤ D ω := Eventually.of_forall fun ω => by
    have h1 := nativeFirstSlopeEnvelope_nonneg' Z ω
    have h2 := abs_nonneg (nativeFirstSelectedIncrement Z E ω)
    simp only [hD]; linarith
  have hint := integrable_pow_of_expTail hDm hDnn nativeFirstMarginTailConstant_pos.le
    (by norm_num : (0 : ℝ) < 1/51200) (nativeFirstMarginDominant_tail hZ hi hG hE) 1
  have hint1 : Integrable D μ := by simpa using hint
  refine hint1.mono' ((nativeFirstMargin_measurable hZ E).abs.aestronglyMeasurable) ?_
  filter_upwards [nativeFirstMargin_abs_le_ae hZ hi hG hE0] with ω hω
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  exact hω

/-- The positive part of the actual first margin is integrable. -/
theorem integrable_nativeFirstMargin_pos
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) :
    Integrable (fun ω => max (nativeFirstMargin Z E ω) 0) μ := by
  refine (integrable_nativeFirstMargin_abs hZ hi hG hE).mono'
    (((nativeFirstMargin_measurable hZ E).max measurable_const).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- Equation \eqref{eq:firstmarginmoments}: for every fixed real `p ≥ 0` the actual
first-restart margin has a moment bound that does not depend on the budget `E`. -/
theorem integral_nativeFirstMargin_rpow_le
    (hZ : ∀ j, Measurable (Z j)) (hi : iIndepFun Z μ)
    (hG : ∀ j, μ.map (Z j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) {p : ℝ} (hp : 0 ≤ p) :
    (∫ ω, |nativeFirstMargin Z E ω|^p ∂μ) ≤ 1+nativeFirstMarginMomentBound ⌈p⌉₊ := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE0 : 0 ≤ E := by linarith
  set k : ℕ := ⌈p⌉₊ with hk
  have hpk : p ≤ (k : ℝ) := Nat.le_ceil p
  have hmm := nativeFirstMargin_measurable hZ E
  have hstep : ∀ ω, |nativeFirstMargin Z E ω|^p ≤ 1+|nativeFirstMargin Z E ω|^k := by
    intro ω
    set x : ℝ := |nativeFirstMargin Z E ω| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    rcases le_or_gt x 1 with h | h
    · have : x^p ≤ 1 := Real.rpow_le_one hx0 h hp
      have hk0 : 0 ≤ x^k := pow_nonneg hx0 k
      linarith
    · have h1 : (1 : ℝ) ≤ x := h.le
      have : x^p ≤ x^((k : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1 hpk
      rw [Real.rpow_natCast] at this
      have hk0 : 0 ≤ x^k := pow_nonneg hx0 k
      linarith
  have hintk : Integrable (fun ω => |nativeFirstMargin Z E ω|^k) μ := by
    set D : Ω → ℝ := fun ω => nativeFirstSlopeEnvelope Z ω+
      |nativeFirstSelectedIncrement Z E ω| with hD
    have hDm : Measurable D :=
      (nativeFirstSlopeEnvelope_measurable hZ).add
        (nativeFirstSelectedIncrement_measurable hZ hE0).abs
    have hDnn : ∀ᵐ ω ∂μ, 0 ≤ D ω := Eventually.of_forall fun ω => by
      have := nativeFirstSlopeEnvelope_nonneg' Z ω
      have := abs_nonneg (nativeFirstSelectedIncrement Z E ω)
      simp only [hD]; linarith
    have hint : Integrable (fun ω => D ω^k) μ :=
      integrable_pow_of_expTail hDm hDnn nativeFirstMarginTailConstant_pos.le
        (by norm_num : (0 : ℝ) < 1/51200) (nativeFirstMarginDominant_tail hZ hi hG hE) k
    refine hint.mono' (hmm.abs.pow_const k).aestronglyMeasurable ?_
    filter_upwards [nativeFirstMargin_abs_le_ae hZ hi hG hE0] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) hω k
  have hsum : Integrable (fun ω => 1+|nativeFirstMargin Z E ω|^k) μ :=
    (integrable_const (1 : ℝ)).add hintk
  have hintp : Integrable (fun ω => |nativeFirstMargin Z E ω|^p) μ := by
    have hrm : Measurable (fun ω => |nativeFirstMargin Z E ω|^p) :=
      (Real.continuous_rpow_const hp).measurable.comp hmm.abs
    refine hsum.mono' hrm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    exact hstep ω
  calc
    (∫ ω, |nativeFirstMargin Z E ω|^p ∂μ) ≤ ∫ ω, (1+|nativeFirstMargin Z E ω|^k) ∂μ :=
      integral_mono_ae hintp hsum (Eventually.of_forall hstep)
    _ = 1+∫ ω, |nativeFirstMargin Z E ω|^k ∂μ := by
      rw [integral_add (integrable_const 1) hintk, integral_const]
      simp
    _ ≤ 1+nativeFirstMarginMomentBound k := by
      linarith [integral_nativeFirstMargin_pow_le hZ hi hG hE k]

end SwingRepair
