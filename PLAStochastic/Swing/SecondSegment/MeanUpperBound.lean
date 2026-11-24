import PLAStochastic.Swing.SecondSegment.SlopeDecay

/-! # Theorem 3.4: the actual second segment has mean of order `E`

The conditional mean of the second segment is the frozen-carry mean at the
actual first output margin.  The negative side uses Lemma H.1 together with the
logarithmic moment supplied by Lemma H.2; the positive side uses the uniform
`E log(eE)` bound together with the decay of the mean positive margin.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Markov's inequality for the positive part of the actual first margin. -/
theorem measureReal_nativeFirstMargin_gt_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E δ : ℝ} (hE : 1 ≤ 2*E) :
    δ*μ.real {ω | δ < nativeFirstMargin X E ω} ≤
      ∫ ω, max (nativeFirstMargin X E ω) 0 ∂μ := by
  have hprob := hi.isProbabilityMeasure
  set S : Set Ω := {ω | δ < nativeFirstMargin X E ω} with hS
  have hSm : MeasurableSet S :=
    measurableSet_lt measurable_const (nativeFirstMargin_measurable hX E)
  have hposint := integrable_nativeFirstMargin_pos hX hi hG hE
  have hindint : Integrable (S.indicator (fun _ => δ)) μ :=
    (integrable_const δ).indicator hSm
  have hdom : ∀ ω, S.indicator (fun _ => δ) ω ≤ max (nativeFirstMargin X E ω) 0 := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      exact le_max_of_le_left (le_of_lt hω)
    · rw [Set.indicator_of_notMem hω]
      exact le_max_right _ _
  have hmono := integral_mono hindint hposint hdom
  rwa [integral_indicator_const _ hSm, smul_eq_mul, mul_comm] at hmono

/-- The actual first margin is nonnegative only with probability `O(E^{-1/4})`. -/
theorem measureReal_nativeFirstMargin_nonneg_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 16 ≤ E) :
    μ.real {ω | 0 ≤ nativeFirstMargin X E ω} ≤
      (2*nativeFirstMarginConcentrationConstant 1+secondMarginPosConstant)/
        Real.sqrt (Real.sqrt E) := by
  have hprob := hi.isProbabilityMeasure
  have hE0 : (0 : ℝ) < E := by linarith
  have hE2 : (1 : ℝ) ≤ 2*E := by linarith
  set S : ℝ := Real.sqrt (Real.sqrt E) with hSdef
  have hsqE : (0 : ℝ) ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hSpos : 0 < S := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hE0)
  have hS2 : S^2 = Real.sqrt E := Real.sq_sqrt hsqE
  have hS2ge : (4 : ℝ) ≤ Real.sqrt E := by
    have h : Real.sqrt 16 ≤ Real.sqrt E := Real.sqrt_le_sqrt hE
    rwa [show (16 : ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)] at h
  have hSge : (2 : ℝ) ≤ S := by nlinarith [hS2, hSpos]
  set C : ℝ := nativeFirstMarginConcentrationConstant 1 with hC
  have hCnn : 0 ≤ C := nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  have hCppos : 0 < secondMarginPosConstant := by
    have := envelopeSqBound_nonneg
    dsimp [secondMarginPosConstant]
    linarith
  have hcover : {ω | 0 ≤ nativeFirstMargin X E ω} ⊆
      {ω | |nativeFirstMargin X E ω| ≤ 1/S} ∪ {ω | 1/S < nativeFirstMargin X E ω} := by
    intro ω hω
    have hnn : 0 ≤ nativeFirstMargin X E ω := hω
    by_cases hle : nativeFirstMargin X E ω ≤ 1/S
    · refine Or.inl ?_
      show |nativeFirstMargin X E ω| ≤ 1/S
      rw [abs_of_nonneg hnn]
      exact hle
    · exact Or.inr (lt_of_not_ge hle)
  have hsplit := measureReal_union_le (μ := μ) {ω | |nativeFirstMargin X E ω| ≤ 1/S}
    {ω | 1/S < nativeFirstMargin X E ω}
  have hsmall := measureReal_nativeFirstMargin_abs_le hX hi hG hE2 (δ := 1/S) (B := 1)
    (by positivity) (by rw [div_le_one hSpos]; linarith)
  have hmark := measureReal_nativeFirstMargin_gt_le hX hi hG hE2 (δ := 1/S)
  have hpos := integral_nativeFirstMargin_pos_le hX hi hG hE
  have hlarge : μ.real {ω | 1/S < nativeFirstMargin X E ω} ≤ secondMarginPosConstant/S := by
    have hstep : (1/S)*μ.real {ω | 1/S < nativeFirstMargin X E ω} ≤
        secondMarginPosConstant/Real.sqrt E := hmark.trans hpos
    rw [← hS2] at hstep
    have hm := mul_le_mul_of_nonneg_left hstep hSpos.le
    have hid : S*((1/S)*μ.real {ω | 1/S < nativeFirstMargin X E ω}) =
        μ.real {ω | 1/S < nativeFirstMargin X E ω} := by field_simp
    rw [hid] at hm
    have hval : S*(secondMarginPosConstant/S^2) = secondMarginPosConstant/S := by
      field_simp
    rwa [hval] at hm
  have hsmall' : μ.real {ω | |nativeFirstMargin X E ω| ≤ 1/S} ≤ 2*C/S := by
    refine hsmall.trans ?_
    have heq : C*(2*(1/S)) = 2*C/S := by field_simp
    rw [heq]
  calc
    μ.real {ω | 0 ≤ nativeFirstMargin X E ω} ≤ _ := measureReal_mono (μ := μ) hcover
    _ ≤ μ.real {ω | |nativeFirstMargin X E ω| ≤ 1/S}+
        μ.real {ω | 1/S < nativeFirstMargin X E ω} := hsplit
    _ ≤ 2*C/S+secondMarginPosConstant/S := add_le_add hsmall' hlarge
    _ = (2*C+secondMarginPosConstant)/S := by ring

def secondSegmentMeanConstant : ℝ :=
  frozenNegativeCarryLogConstant*(1+2*nativeFirstMarginConcentrationConstant 1)+
    5*frozenUniformMeanConstant*
      (2*nativeFirstMarginConcentrationConstant 1+2*secondMarginPosConstant)

/-- Theorem 3.4 (upper bound): the actual second segment has mean `O(E)`. -/
theorem secondSegment_mean_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 16 ≤ E) :
    (∫ ω, (nativeRecordingDurationNat X E 1 ω : ℝ) ∂μ) ≤ secondSegmentMeanConstant*E := by
  have hprob := hi.isProbabilityMeasure
  have hE0 : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hE2 : (1 : ℝ) ≤ 2*E := by linarith
  set C : ℝ := nativeFirstMarginConcentrationConstant 1 with hC
  have hCnn : 0 ≤ C := nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  have hCppos : 0 < secondMarginPosConstant := by
    have := envelopeSqBound_nonneg
    dsimp [secondMarginPosConstant]
    linarith
  have hC1 := frozenNegativeCarryLogConstant_pos
  have hCu := frozenUniformMeanConstant_pos
  have hlogEnn : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hlogE : Real.log (Real.exp 1*E) = 1+Real.log E := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (by linarith), Real.log_exp]
  set S : ℝ := Real.sqrt (Real.sqrt E) with hSdef
  have hsqE : (0 : ℝ) ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hSpos : 0 < S := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hE0)
  have hS2 : S^2 = Real.sqrt E := Real.sq_sqrt hsqE
  have hS4 : S^4 = E := by
    have h : S^4 = (S^2)^2 := by ring
    rw [h, hS2, Real.sq_sqrt hE0.le]
  have hS2ge : (4 : ℝ) ≤ Real.sqrt E := by
    have h : Real.sqrt 16 ≤ Real.sqrt E := Real.sqrt_le_sqrt hE
    rwa [show (16 : ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)] at h
  have hSge : (2 : ℝ) ≤ S := by nlinarith [hS2, hSpos]
  -- abbreviations used only for readability of the estimates below
  have hindm : MeasurableSet {ω | 0 ≤ nativeFirstMargin X E ω} :=
    measurableSet_le measurable_const (nativeFirstMargin_measurable hX E)
  have hindeq : (fun ω => if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0) =
      {ω | 0 ≤ nativeFirstMargin X E ω}.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : 0 ≤ nativeFirstMargin X E ω
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω | 0 ≤ nativeFirstMargin X E ω} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | 0 ≤ nativeFirstMargin X E ω} from h)]
  have hlogint : Integrable (marginLogWeight X E) μ := integrable_marginLogWeight hX hi hG hE2
  have hposint : Integrable (fun ω => max (nativeFirstMargin X E ω) 0) μ :=
    integrable_nativeFirstMargin_pos hX hi hG hE2
  have hindint : Integrable (fun ω => if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0) μ := by
    rw [hindeq]
    exact (integrable_const (1 : ℝ)).indicator hindm
  have hG1int : Integrable
      (fun ω => frozenNegativeCarryLogConstant*E*(1+marginLogWeight X E ω)) μ :=
    ((integrable_const (1 : ℝ)).add hlogint).const_mul _
  have hG2int : Integrable (fun ω => frozenUniformMeanConstant*E*(1+Real.log E)*
      ((if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0)+
        max (nativeFirstMargin X E ω) 0)) μ :=
    (hindint.add hposint).const_mul _
  have hdom : ∀ ω, nativeRestartMean X μ E (nativeFirstNext X E ω) ≤
      frozenNegativeCarryLogConstant*E*(1+marginLogWeight X E ω)+
        frozenUniformMeanConstant*E*(1+Real.log E)*
          ((if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0)+
            max (nativeFirstMargin X E ω) 0) := by
    intro ω
    have hbridge : nativeRestartMean X μ E (nativeFirstNext X E ω) =
        ∫ ω', frozenPrefixLengthReal X (nativeFirstMargin X E ω) E ω' ∂μ :=
      nativeRestartMean_eq_frozen_margin hX hi hG E (nativeFirstNext X E ω)
    have hlogw : 0 ≤ marginLogWeight X E ω := marginLogWeight_nonneg X E ω
    have hmaxR : 0 ≤ max (nativeFirstMargin X E ω) 0 := le_max_right _ _
    by_cases hneg : nativeFirstMargin X E ω < 0
    · have hc : 0 < -nativeFirstMargin X E ω := by linarith
      have hH1 := frozenPrefixLength_negative_mean_log_bound hX hi hG hc hE
      have habs : |nativeFirstMargin X E ω| = -nativeFirstMargin X E ω := abs_of_neg hneg
      have hweq : marginLogWeight X E ω = max (Real.log (1/(-nativeFirstMargin X E ω))) 0 := by
        rw [marginLogWeight, habs]
      have hind0 : (if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0) = 0 :=
        if_neg (by linarith)
      have hbase : 0 ≤ frozenUniformMeanConstant*E*(1+Real.log E) := by positivity
      have hneq : nativeFirstMargin X E ω = -(-nativeFirstMargin X E ω) := by ring
      have hkey : (∫ ω', frozenPrefixLengthReal X (nativeFirstMargin X E ω) E ω' ∂μ) ≤
          frozenNegativeCarryLogConstant*E*(1+marginLogWeight X E ω) := by
        rw [hweq]
        simpa only [neg_neg] using hH1
      rw [hbridge, hind0]
      nlinarith [hkey, hbase, hmaxR]
    · have hnn : 0 ≤ nativeFirstMargin X E ω := le_of_not_gt hneg
      have hU := frozenPrefixLength_uniform_mean_bound hX hi hG (nativeFirstMargin X E ω) hE1
      rw [hlogE] at hU
      have hind1 : (if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0) = 1 := if_pos hnn
      have hbase : 0 ≤ frozenNegativeCarryLogConstant*E := by positivity
      have hkey : (∫ ω', frozenPrefixLengthReal X (nativeFirstMargin X E ω) E ω' ∂μ) ≤
          frozenUniformMeanConstant*E*(1+Real.log E)*(1+max (nativeFirstMargin X E ω) 0) := by
        have heq : frozenUniformMeanConstant*E*(1+Real.log E)*
            (1+max (nativeFirstMargin X E ω) 0) =
            frozenUniformMeanConstant*E*(1+max (nativeFirstMargin X E ω) 0)*(1+Real.log E) := by
          ring
        rw [heq]
        exact hU
      rw [hbridge, hind1]
      nlinarith [hkey, hbase, hlogw]
  have hhint : Integrable (fun ω => nativeRestartMean X μ E (nativeFirstNext X E ω)) μ := by
    refine (hG1int.add hG2int).mono' ?_ ?_
    · exact ((nativeRestartMean_measurable hX E).comp
        ((nativeRestartNext_measurable (fun k => X (1+k)) (fun k => hX (1+k)) E).comp
          ((hX 0).prodMk measurable_id))).aestronglyMeasurable
    · filter_upwards with ω
      have hnn : 0 ≤ nativeRestartMean X μ E (nativeFirstNext X E ω) := by
        have hb := nativeRestartMean_bounds hX hi hG hE0 (nativeFirstNext X E ω)
        exact le_trans (by norm_num) hb.1
      rw [Real.norm_of_nonneg hnn]
      exact hdom ω
  have hmono : (∫ ω, nativeRestartMean X μ E (nativeFirstNext X E ω) ∂μ) ≤
      ∫ ω, (frozenNegativeCarryLogConstant*E*(1+marginLogWeight X E ω)+
        frozenUniformMeanConstant*E*(1+Real.log E)*
          ((if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0)+
            max (nativeFirstMargin X E ω) 0)) ∂μ :=
    integral_mono hhint (hG1int.add hG2int) hdom
  have hsum := integral_add (μ := μ)
    (f := fun ω => frozenNegativeCarryLogConstant*E*(1+marginLogWeight X E ω))
    (g := fun ω => frozenUniformMeanConstant*E*(1+Real.log E)*
      ((if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0)+
        max (nativeFirstMargin X E ω) 0)) hG1int hG2int
  have hG1val : (∫ ω, frozenNegativeCarryLogConstant*E*(1+marginLogWeight X E ω) ∂μ) =
      frozenNegativeCarryLogConstant*E*(1+∫ ω, marginLogWeight X E ω ∂μ) := by
    rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hlogint, integral_const]
    simp
  have hindval : (∫ ω, (if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0) ∂μ) =
      μ.real {ω | 0 ≤ nativeFirstMargin X E ω} := by
    rw [hindeq, integral_indicator_const _ hindm, smul_eq_mul, mul_one]
  have hG2val : (∫ ω, frozenUniformMeanConstant*E*(1+Real.log E)*
      ((if 0 ≤ nativeFirstMargin X E ω then (1 : ℝ) else 0)+
        max (nativeFirstMargin X E ω) 0) ∂μ) =
      frozenUniformMeanConstant*E*(1+Real.log E)*
        (μ.real {ω | 0 ≤ nativeFirstMargin X E ω}+
          ∫ ω, max (nativeFirstMargin X E ω) 0 ∂μ) := by
    rw [integral_const_mul, integral_add hindint hposint, hindval]
  rw [hsum, hG1val, hG2val] at hmono
  rw [secondSegment_mean_eq hX hi hG hE0]
  have hstart : (∫ ω, (∫ ω', frozenPrefixLengthReal X (nativeFirstMargin X E ω) E ω' ∂μ) ∂μ) =
      ∫ ω, nativeRestartMean X μ E (nativeFirstNext X E ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω =>
      (nativeRestartMean_eq_frozen_margin hX hi hG E (nativeFirstNext X E ω)).symm)
  rw [hstart]
  refine hmono.trans ?_
  -- numerical estimates
  have hlogbound : (∫ ω, marginLogWeight X E ω ∂μ) ≤ 2*C := integral_marginLogWeight_le hX hi hG hE2
  have hnonneg := measureReal_nativeFirstMargin_nonneg_le hX hi hG hE
  have hposbound : (∫ ω, max (nativeFirstMargin X E ω) 0 ∂μ) ≤
      secondMarginPosConstant/Real.sqrt E := integral_nativeFirstMargin_pos_le hX hi hG hE
  have hfirst : frozenNegativeCarryLogConstant*E*(1+∫ ω, marginLogWeight X E ω ∂μ) ≤
      frozenNegativeCarryLogConstant*(1+2*C)*E := by
    have hbase : 0 ≤ frozenNegativeCarryLogConstant*E := by positivity
    nlinarith [hlogbound, hbase]
  have hsecondsum : μ.real {ω | 0 ≤ nativeFirstMargin X E ω}+
      ∫ ω, max (nativeFirstMargin X E ω) 0 ∂μ ≤ (2*C+2*secondMarginPosConstant)/S := by
    have hp : (∫ ω, max (nativeFirstMargin X E ω) 0 ∂μ) ≤ secondMarginPosConstant/S^2 := by
      rw [hS2]
      exact hposbound
    have hsq : secondMarginPosConstant/S^2 ≤ secondMarginPosConstant/S :=
      (div_le_div_iff_of_pos_left hCppos (by positivity) hSpos).mpr (by nlinarith)
    calc
      _ ≤ (2*C+secondMarginPosConstant)/S+secondMarginPosConstant/S :=
        add_le_add hnonneg (hp.trans hsq)
      _ = (2*C+2*secondMarginPosConstant)/S := by ring
  have hlogS : Real.log E ≤ 4*S-4 := by
    have h1 : Real.log E = 4*Real.log S := by
      rw [← hS4, Real.log_pow]
      push_cast
      ring
    have h2 : Real.log S ≤ S-1 := Real.log_le_sub_one_of_pos hSpos
    linarith
  have hratio : (1+Real.log E)/S ≤ 5 := by
    rw [div_le_iff₀ hSpos]
    linarith
  have hsec : frozenUniformMeanConstant*E*(1+Real.log E)*((2*C+2*secondMarginPosConstant)/S) ≤
      5*frozenUniformMeanConstant*(2*C+2*secondMarginPosConstant)*E := by
    have hid : frozenUniformMeanConstant*E*(1+Real.log E)*((2*C+2*secondMarginPosConstant)/S) =
        frozenUniformMeanConstant*E*(2*C+2*secondMarginPosConstant)*((1+Real.log E)/S) := by
      field_simp
    rw [hid]
    have hbase : 0 ≤ frozenUniformMeanConstant*E*(2*C+2*secondMarginPosConstant) := by positivity
    nlinarith [hratio, hbase]
  have hmul : frozenUniformMeanConstant*E*(1+Real.log E)*
      (μ.real {ω | 0 ≤ nativeFirstMargin X E ω}+∫ ω, max (nativeFirstMargin X E ω) 0 ∂μ) ≤
      frozenUniformMeanConstant*E*(1+Real.log E)*((2*C+2*secondMarginPosConstant)/S) :=
    mul_le_mul_of_nonneg_left hsecondsum (by positivity)
  dsimp [secondSegmentMeanConstant]
  linarith

end SwingRepair
