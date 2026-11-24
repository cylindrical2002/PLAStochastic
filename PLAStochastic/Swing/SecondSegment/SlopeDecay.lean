import PLAStochastic.Swing.SecondSegment.MarginLogMoment

/-! # The first selected slope and the positive part of the actual first margin

The positive margin is dominated by the actual first selected slope, whose mean
decays in the budget.  The decay uses the genuine last-accepted-sample cone
bound at an intermediate horizon and the Gaussian probability of failing to
reach that horizon.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The actual slope selected on the first accepted prefix. -/
def nativeFirstSelectedSlope (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  nativeRestartSlope (fun k => X (1+k)) E (X 0 ω) ω

/-- The rebased restart length of the first segment is the actual first duration. -/
theorem nativeFirstRestartLength_eq_duration_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) :
    ∀ᵐ ω ∂μ, nativeRestartLength (fun k => X (1+k)) E (X 0 ω) ω =
      ((nativeFirstDuration X E ω : ℕ) : WithTop ℕ) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hts : StrictMono (fun n : ℕ => (n : ℝ)) := by
    intro a b hab
    change (a : ℝ) < b
    exact_mod_cast hab
  filter_upwards [firstRepairReject_ae_finite_gaussian hX hi hG (ε := 2*E) (by linarith)]
    with ω hfin
  set Y : ℕ → Ω → ℝ := fun k => X (1+k) with hY
  have hcone : ∀ j, nativePrefixFeasible (fun n => (n : ℝ))
      (fun n => cumulativeSamples X n ω) E 0 j (cumulativeSamples X 0 ω) ↔
        j < firstRepairSpan X (2*E) ω := fun j =>
    (nativePrefix_trueAnchor_iff _ _ hts E 0 j).trans
      (prefixCone_iff_lt_firstRepairSpan X (2*E) ω hfin j)
  have hK : 1 < firstRepairSpan X (2*E) ω :=
    (hcone 1).mp (nativePrefix_singleton _ _ hts hE 0 _)
  obtain ⟨n, hn⟩ : ∃ n, firstRepairSpan X (2*E) ω = n+2 := ⟨firstRepairSpan X (2*E) ω-2, by omega⟩
  have hfitz : nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
      E 0 (n+1) 0 := by
    simpa only [cumulativeSamples_zero] using (hcone (n+1)).mpr (by omega)
  have hrejz : ¬ nativePrefixFeasible (fun j => (j : ℝ)) (fun j => cumulativeSamples X j ω)
      E 0 (n+2) 0 := by
    simp only [← cumulativeSamples_zero X ω]
    intro h
    have := (hcone (n+2)).mp h
    omega
  have hfeas : ∀ k, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples X i ω) E 0 k 0 ↔
        (k : WithTop ℕ) ≤ nativeRestartLength Y E (X 0 ω) ω := by
    intro k
    simpa [cumulativeSamples, Y] using nativeRestart_feasible_iff X 0 k E 0 ω
  have hlen : nativeRestartLength Y E (X 0 ω) ω = ((n+1 : ℕ) : WithTop ℕ) := by
    apply le_antisymm _ ((hfeas (n+1)).mp hfitz)
    by_contra hnot
    have hgt : ((n+1 : ℕ) : WithTop ℕ) < nativeRestartLength Y E (X 0 ω) ω := lt_of_not_ge hnot
    have hnext : ((n+2 : ℕ) : WithTop ℕ) ≤ nativeRestartLength Y E (X 0 ω) ω := by
      cases heq : nativeRestartLength Y E (X 0 ω) ω using WithTop.recTopCoe with
      | top => exact le_top
      | coe j =>
        rw [heq] at hgt
        have hj : n+1 < j := WithTop.coe_lt_coe.mp hgt
        exact WithTop.coe_le_coe.mpr (show n+2 ≤ j by omega)
    exact hrejz ((hfeas (n+2)).mpr hnext)
  have hdur : nativeFirstDuration X E ω = n+1 := by
    have hd := nativeFirstDuration_eq_span_sub_one X E hE ω
    rw [hn] at hd
    omega
  rw [hlen, hdur]

/-- The positive part of the actual first margin is dominated by the selected slope. -/
theorem nativeFirstMargin_pos_le_slope_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) :
    ∀ᵐ ω ∂μ, max (nativeFirstMargin X E ω) 0 ≤ |nativeFirstSelectedSlope X E ω| := by
  filter_upwards [nativeFirstRestartLength_eq_duration_ae hX hi hG hE] with ω hω
  have hf : nativeRestartLength (fun k => X (1+k)) E (X 0 ω) ω ≠ ⊤ := by
    rw [hω]; exact WithTop.coe_ne_top
  exact nativeRestart_margin_pos_le_slope (fun k => X (1+k)) hE (X 0 ω) ω hf

/-- On the event that the first accepted prefix reaches `n`, the selected slope
fits the sample at `n`. -/
theorem nativeFirstSelectedSlope_mul_le_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, n ≤ nativeFirstDuration X E ω →
      |nativeFirstSelectedSlope X E ω| * (n : ℝ) ≤ E+|cumulativeSamples X n ω| := by
  filter_upwards [nativeFirstRestartLength_eq_duration_ae hX hi hG hE] with ω hω hdur
  set Y : ℕ → Ω → ℝ := fun k => X (1+k) with hY
  have hf : nativeRestartLength Y E (X 0 ω) ω ≠ ⊤ := by rw [hω]; exact WithTop.coe_ne_top
  have hNat : nativeRestartLengthNat Y E (X 0 ω) ω = nativeFirstDuration X E ω := by
    change (nativeRestartLength Y E (X 0 ω) ω).untopD 0 = _
    rw [hω]
    rfl
  have hfs := nativeRestartSlope_feasible Y hE (X 0 ω) ω hf
  rw [hNat] at hfs
  have hmem : n ∈ Finset.Icc 1 (nativeFirstDuration X E ω) := Finset.mem_Icc.mpr ⟨hn, hdur⟩
  have hval := hfs n hmem
  have heq : nativeCarriedSamples Y (fun _ => X 0 ω) n ω = cumulativeSamples X n ω :=
    nativeCarriedSamples_first_eq X hn ω
  simp only [heq, sub_zero, zero_add] at hval
  have habs := abs_le.mp hval
  have hslope : nativeFirstSelectedSlope X E ω = nativeRestartSlope Y E (X 0 ω) ω := rfl
  rw [hslope]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle := le_abs_self (cumulativeSamples X n ω)
  have hneg := neg_le_abs (cumulativeSamples X n ω)
  rcases le_or_gt 0 (nativeRestartSlope Y E (X 0 ω) ω) with hm | hm
  · rw [abs_of_nonneg hm]
    nlinarith [habs.1, habs.2]
  · rw [abs_of_neg hm]
    nlinarith [habs.1, habs.2]

/-- The actual first selected slope is dominated by the budget-free Gaussian envelope. -/
theorem nativeFirstSelectedSlope_abs_le_envelope_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) :
    ∀ᵐ ω ∂μ, |nativeFirstSelectedSlope X E ω| ≤ nativeFirstSlopeEnvelope X ω := by
  filter_upwards [nativeFirstRestartLength_eq_duration_ae hX hi hG hE,
    nativeFirst_feasible_slope_bound_ae hX hi hG] with ω hω he
  set Y : ℕ → Ω → ℝ := fun k => X (1+k) with hY
  set N : ℕ := nativeFirstDuration X E ω with hN
  have hf : nativeRestartLength Y E (X 0 ω) ω ≠ ⊤ := by rw [hω]; exact WithTop.coe_ne_top
  have hNat : nativeRestartLengthNat Y E (X 0 ω) ω = N := by
    change (nativeRestartLength Y E (X 0 ω) ω).untopD 0 = _
    rw [hω]
    rfl
  have hNpos : 0 < N := by
    have := nativeRestartLengthNat_pos_of_finite Y hE (X 0 ω) ω hf
    rwa [hNat] at this
  have hfeas : ∀ k, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples X i ω) E 0 k 0 ↔
        (k : WithTop ℕ) ≤ nativeRestartLength Y E (X 0 ω) ω := by
    intro k
    simpa [cumulativeSamples, Y] using nativeRestart_feasible_iff X 0 k E 0 ω
  have hfit : nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples X i ω) E 0 N 0 :=
    (hfeas N).mpr (by rw [hω])
  have hrej : ¬ nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples X i ω)
      E 0 (N+1) 0 := by
    intro h
    have hle := (hfeas (N+1)).mp h
    rw [hω] at hle
    have : N+1 ≤ N := WithTop.coe_le_coe.mp hle
    omega
  have hlocal : feasibleSlope (Finset.Icc 1 N) (fun i => (i : ℝ))
      (fun i => cumulativeSamples X i ω) 0 0 E (nativeRestartSlope Y E (X 0 ω) ω) := by
    have hfs := nativeRestartSlope_feasible Y hE (X 0 ω) ω hf
    rw [hNat] at hfs
    intro i hi
    have heq : nativeCarriedSamples Y (fun _ => X 0 ω) i ω = cumulativeSamples X i ω :=
      nativeCarriedSamples_first_eq X (Finset.mem_Icc.mp hi).1 ω
    simpa only [heq] using hfs i hi
  exact he E hE N hNpos hfit hrej _ hlocal

/-- Failing to reach a horizon forces a large Gaussian excursion below it. -/
theorem nativeFirstDuration_lt_cover_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) (n : ℕ) :
    ∀ᵐ ω ∂μ, nativeFirstDuration X E ω < n →
      ω ∈ ⋃ j ∈ Finset.Icc 1 n, {ω | E ≤ |cumulativeSamples X j ω|} := by
  filter_upwards [nativeFirstRestartLength_eq_duration_ae hX hi hG hE] with ω hω hlt
  set Y : ℕ → Ω → ℝ := fun k => X (1+k) with hY
  have hfeas : ∀ k, nativePrefixFeasible (fun i => (i : ℝ))
      (fun i => cumulativeSamples X i ω) E 0 k 0 ↔
        (k : WithTop ℕ) ≤ nativeRestartLength Y E (X 0 ω) ω := by
    intro k
    simpa [cumulativeSamples, Y] using nativeRestart_feasible_iff X 0 k E 0 ω
  have hrej : ¬ nativePrefixFeasible (fun i => (i : ℝ)) (fun i => cumulativeSamples X i ω)
      E 0 n 0 := by
    intro h
    have hle := (hfeas n).mp h
    rw [hω] at hle
    have : n ≤ nativeFirstDuration X E ω := WithTop.coe_le_coe.mp hle
    omega
  by_contra hcon
  apply hrej
  refine ⟨0, fun j hj => ?_⟩
  have hnot : ¬ (E ≤ |cumulativeSamples X j ω|) := by
    intro hbad
    exact hcon (mem_biUnion hj hbad)
  simp only [Nat.cast_zero, sub_zero, zero_mul, sub_zero, zero_add]
  push Not at hnot
  simpa only [sub_zero, zero_mul, sub_zero] using hnot.le

theorem measureReal_nativeFirstDuration_lt_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E) {n : ℕ} (hn : 1 ≤ n) :
    μ.real {ω | nativeFirstDuration X E ω < n} ≤
      2*(n : ℝ)*Real.exp (-E^2/(2*(n : ℝ))) := by
  have hprob := hi.isProbabilityMeasure
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hcov := ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (nativeFirstDuration_lt_cover_ae hX hi hG hE n))
  refine hcov.trans ?_
  have hsum := measureReal_biUnion_finset_le (μ := μ) (Finset.Icc 1 n)
    (fun j => {ω | E ≤ |cumulativeSamples X j ω|})
  refine hsum.trans ?_
  have hterm : ∀ j ∈ Finset.Icc 1 n, μ.real {ω | E ≤ |cumulativeSamples X j ω|} ≤
      2*Real.exp (-E^2/(2*(n : ℝ))) := by
    intro j hj
    have hjn := (Finset.mem_Icc.mp hj).2
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hjr : (0 : ℝ) < j := by exact_mod_cast hj1
    have hjnr : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    refine (cumulativeSamples_abs_tail_bound hX hi hG j hE).trans ?_
    have hmono : Real.exp (-E^2/(2*(j : ℝ))) ≤ Real.exp (-E^2/(2*(n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hd : E^2/(2*(n : ℝ)) ≤ E^2/(2*(j : ℝ)) := by
        gcongr
      rw [neg_div, neg_div]
      linarith
    linarith
  calc
    (∑ j ∈ Finset.Icc 1 n, μ.real {ω | E ≤ |cumulativeSamples X j ω|})
        ≤ ∑ _j ∈ Finset.Icc 1 n, 2*Real.exp (-E^2/(2*(n : ℝ))) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc 1 n).card : ℝ)*(2*Real.exp (-E^2/(2*(n : ℝ)))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2*(n : ℝ)*Real.exp (-E^2/(2*(n : ℝ))) := by
      have hcard : ((Finset.Icc 1 n).card : ℝ) ≤ (n : ℝ) := by
        rw [Nat.card_Icc]
        have : n+1-1 = n := by omega
        rw [this]
      nlinarith [Real.exp_pos (-E^2/(2*(n : ℝ)))]

/-! ## Moments of the envelope and of the Gaussian endpoint -/

theorem exp_ge_pow_six {u : ℝ} (hu : 0 ≤ u) : u^6/46656 ≤ Real.exp u := by
  have h := Real.add_one_le_exp (u/6)
  have hpos : (0 : ℝ) ≤ u/6 := by linarith
  have h1 : (u/6)^6 ≤ (u/6+1)^6 := pow_le_pow_left₀ hpos (by linarith) 6
  have h2 : (u/6+1)^6 ≤ (Real.exp (u/6))^6 := pow_le_pow_left₀ (by linarith) h 6
  have h3 : (Real.exp (u/6))^6 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h3] at h2
  have h4 : (u/6)^6 = u^6/46656 := by ring
  linarith [h4 ▸ h1]

theorem gaussianReal_integral_abs_le_sqrt {N : ℕ} (hN : 0 < N) :
    (∫ y : ℝ, |y| ∂gaussianReal 0 (N : ℝ≥0)) ≤ Real.sqrt (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsq : Real.sqrt (N : ℝ)^2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have h1 : Integrable (fun y : ℝ => |y|) (gaussianReal 0 (N : ℝ≥0)) :=
    (memLp_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)) 1).integrable (by norm_num) |>.abs
  have h2 : Integrable (fun y : ℝ => y^2) (gaussianReal 0 (N : ℝ≥0)) :=
    (memLp_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)) 2).integrable_sq
  have hvar : (∫ y : ℝ, y^2 ∂gaussianReal 0 (N : ℝ≥0)) = (N : ℝ) := by
    have hv := variance_of_integral_eq_zero (X := (id : ℝ → ℝ))
      (μ := gaussianReal 0 (N : ℝ≥0)) measurable_id.aemeasurable
      (by simpa only [id_eq] using integral_id_gaussianReal (μ := 0) (v := (N : ℝ≥0)))
    simpa only [variance_id_gaussianReal, NNReal.coe_natCast, id_eq] using hv.symm
  calc
    _ ≤ ∫ y : ℝ, (y^2+(N : ℝ))/(2*Real.sqrt (N : ℝ)) ∂gaussianReal 0 (N : ℝ≥0) := by
      apply integral_mono_ae h1 ((h2.add (integrable_const _)).div_const _)
      refine ae_of_all _ (fun y => ?_)
      dsimp only [Pi.add_apply]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|y|-Real.sqrt (N : ℝ)), sq_abs y, hsq]
    _ = Real.sqrt (N : ℝ) := by
      have huniv : (gaussianReal 0 (N : ℝ≥0)).real Set.univ = 1 := by simp
      rw [integral_div, integral_add h2 (integrable_const _), hvar, integral_const,
        huniv, smul_eq_mul, one_mul]
      field_simp
      nlinarith [hsq]

theorem integral_abs_cumulativeSamples_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {n : ℕ} (hn : 0 < n) :
    (∫ ω, |cumulativeSamples X n ω| ∂μ) ≤ Real.sqrt (n : ℝ) := by
  have hprob := hi.isProbabilityMeasure
  have hl := gaussianEndpoint_hasLaw hX hi hG n
  have hmeas : Measurable (cumulativeSamples X n) :=
    Finset.measurable_sum (Finset.range n) (fun k _ => hX k)
  have hmap : (∫ ω, |cumulativeSamples X n ω| ∂μ) = ∫ y : ℝ, |y| ∂gaussianReal 0 (n : ℝ≥0) := by
    rw [← hl.map_eq]
    exact (integral_map hmeas.aemeasurable
      (Measurable.aestronglyMeasurable (f := fun y : ℝ => |y|) measurable_id.abs)).symm
  rw [hmap]
  exact gaussianReal_integral_abs_le_sqrt hn

/-! ## The square moment of the Gaussian slope envelope -/

def envelopeTailConstant : ℝ := nativeFirstSlopeEnvelopeTailConstant*Real.exp 1

theorem envelopeTailConstant_ge_one : 1 ≤ envelopeTailConstant := by
  have h1 : 2*Real.exp 1 ≤ nativeFirstSlopeEnvelopeTailConstant := by
    dsimp [nativeFirstSlopeEnvelopeTailConstant]
    have h := nativeGaussianEnvelope_tail_constant_pos
    nlinarith [Real.exp_pos (1 : ℝ)]
  have h2 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  dsimp [envelopeTailConstant]
  nlinarith

theorem nativeFirstSlopeEnvelope_natTail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    μ {ω | (n : ℝ) ≤ nativeFirstSlopeEnvelope X ω} ≤
      ENNReal.ofReal (envelopeTailConstant*Real.exp (-(1/1600)*(n : ℝ))) := by
  have hprob := hi.isProbabilityMeasure
  have hC := nativeFirstSlopeEnvelopeTailConstant_nonneg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hb : (1 : ℝ) ≤ envelopeTailConstant*Real.exp (-(1/1600)*((0 : ℕ) : ℝ)) := by
      simpa using envelopeTailConstant_ge_one
    calc
      μ {ω | ((0 : ℕ) : ℝ) ≤ nativeFirstSlopeEnvelope X ω} ≤ 1 := prob_le_one
      _ ≤ _ := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
        exact ENNReal.ofReal_le_ofReal hb
  · have hnr : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsub : {ω | (n : ℝ) ≤ nativeFirstSlopeEnvelope X ω} ⊆
        {ω | (n : ℝ)-1 < nativeFirstSlopeEnvelope X ω} := fun ω hω => by
      have : (n : ℝ) ≤ nativeFirstSlopeEnvelope X ω := hω
      change (n : ℝ)-1 < nativeFirstSlopeEnvelope X ω
      linarith
    have htail := nativeFirstSlopeEnvelope_tail_bound hX hi hG
      (t := (n : ℝ)-1) (by linarith)
    have hstep : nativeFirstSlopeEnvelopeTailConstant*Real.exp (-((n : ℝ)-1)^2/1600) ≤
        envelopeTailConstant*Real.exp (-(1/1600)*(n : ℝ)) := by
      have hexp : Real.exp (-((n : ℝ)-1)^2/1600) ≤ Real.exp 1*Real.exp (-(1/1600)*(n : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg ((n : ℝ)-2)]
      dsimp [envelopeTailConstant]
      nlinarith [Real.exp_pos (-((n : ℝ)-1)^2/1600), Real.exp_pos (-(1/1600)*(n : ℝ))]
    have hreal : μ.real {ω | (n : ℝ) ≤ nativeFirstSlopeEnvelope X ω} ≤
        envelopeTailConstant*Real.exp (-(1/1600)*(n : ℝ)) :=
      ((measureReal_mono hsub).trans htail).trans hstep
    calc
      μ {ω | (n : ℝ) ≤ nativeFirstSlopeEnvelope X ω}
          = ENNReal.ofReal (μ.real {ω | (n : ℝ) ≤ nativeFirstSlopeEnvelope X ω}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

def envelopeSqBound : ℝ := envelopeTailConstant*expTailMomentSum (1/1600) 2

theorem integral_envelope_sq_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    (∫ ω, nativeFirstSlopeEnvelope X ω^2 ∂μ) ≤ envelopeSqBound :=
  integral_pow_le_of_expTail (nativeFirstSlopeEnvelope_measurable hX)
    (Eventually.of_forall (nativeFirstSlopeEnvelope_nonneg' X))
    (by linarith [envelopeTailConstant_ge_one]) (by norm_num : (0 : ℝ) < 1/1600)
    (nativeFirstSlopeEnvelope_natTail hX hi hG) 2

theorem integrable_envelope_sq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Integrable (fun ω => nativeFirstSlopeEnvelope X ω^2) μ :=
  integrable_pow_of_expTail (nativeFirstSlopeEnvelope_measurable hX)
    (Eventually.of_forall (nativeFirstSlopeEnvelope_nonneg' X))
    (by linarith [envelopeTailConstant_ge_one]) (by norm_num : (0 : ℝ) < 1/1600)
    (nativeFirstSlopeEnvelope_natTail hX hi hG) 2

theorem envelopeSqBound_nonneg : 0 ≤ envelopeSqBound := by
  have h := envelopeTailConstant_ge_one
  have h2 := expTailMomentSum_nonneg (1/1600) 2
  dsimp [envelopeSqBound]
  nlinarith

/-! ## The mean positive margin decays in the budget -/

def secondMarginPosConstant : ℝ := 2+764411904+envelopeSqBound

theorem secondMarginPosConstant_nonneg : 0 ≤ secondMarginPosConstant := by
  have := envelopeSqBound_nonneg
  dsimp [secondMarginPosConstant]
  linarith

/-- Equation `eq:secondpositiveexpectation`: the mean positive margin is `O(E^{-1/2})`. -/
theorem integral_nativeFirstMargin_pos_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 16 ≤ E) :
    (∫ ω, max (nativeFirstMargin X E ω) 0 ∂μ) ≤ secondMarginPosConstant/Real.sqrt E := by
  have hprob := hi.isProbabilityMeasure
  have hE0 : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  set T : ℝ := Real.sqrt E with hT
  have hTpos : 0 < T := Real.sqrt_pos.mpr hE0
  have hTsq : T^2 = E := Real.sq_sqrt hE0.le
  have hT4 : (4 : ℝ) ≤ T := by
    have h : Real.sqrt 16 ≤ Real.sqrt E := Real.sqrt_le_sqrt hE
    rwa [show (16 : ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)] at h
  have hTE : T ≤ E := by nlinarith
  set nstar : ℕ := ⌈E*T⌉₊ with hnstar
  have hETpos : (0 : ℝ) < E*T := by positivity
  have hnpos : 0 < nstar := Nat.ceil_pos.mpr hETpos
  have hnr : (0 : ℝ) < (nstar : ℝ) := by exact_mod_cast hnpos
  have hnlow : E*T ≤ (nstar : ℝ) := Nat.le_ceil _
  have hnhigh : (nstar : ℝ) < E*T+1 := Nat.ceil_lt_add_one hETpos.le
  have hnhigh2 : (nstar : ℝ) ≤ 2*(E*T) := by nlinarith
  set A : Set Ω := {ω | nativeFirstDuration X E ω < nstar} with hA
  have hAmeas : MeasurableSet A :=
    measurableSet_lt (nativeFirstDuration_measurable hX hE0.le) measurable_const
  set env : Ω → ℝ := nativeFirstSlopeEnvelope X with hEnv
  have hEnvSq := integrable_envelope_sq hX hi hG
  have hYint : Integrable (fun ω => |cumulativeSamples X nstar ω|) μ := by
    have hl := gaussianEndpoint_hasLaw hX hi hG nstar
    have hm : Measurable (cumulativeSamples X nstar) :=
      Finset.measurable_sum (Finset.range nstar) (fun k _ => hX k)
    have hmap : Integrable (fun y : ℝ => |y|) (μ.map (cumulativeSamples X nstar)) := by
      rw [hl.map_eq]
      exact (memLp_id_gaussianReal (μ := 0) (v := (nstar : ℝ≥0)) 1).integrable (by norm_num) |>.abs
    exact (integrable_map_measure
      (Measurable.aestronglyMeasurable (f := fun y : ℝ => |y|) measurable_id.abs)
      hm.aemeasurable).mp hmap
  set F1 : Ω → ℝ := fun ω => (E+|cumulativeSamples X nstar ω|)/(nstar : ℝ) with hF1
  set F2 : Ω → ℝ := fun ω => if nativeFirstDuration X E ω < nstar then T else 0 with hF2
  have hF2eq : F2 = A.indicator (fun _ => T) := by
    rw [hF2]
    funext ω
    by_cases h : nativeFirstDuration X E ω < nstar
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ A from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ A from h)]
  set F3 : Ω → ℝ := fun ω => env ω^2/T with hF3
  set F : Ω → ℝ := fun ω => F1 ω+F2 ω+F3 ω with hF
  have hF1int : Integrable F1 μ := ((integrable_const E).add hYint).div_const _
  have hF2int : Integrable F2 μ := by
    rw [hF2eq]
    exact (integrable_const T).indicator hAmeas
  have hF3int : Integrable F3 μ := hEnvSq.div_const T
  have hFint : Integrable F μ := (hF1int.add hF2int).add hF3int
  have hdom : ∀ᵐ ω ∂μ, max (nativeFirstMargin X E ω) 0 ≤ F ω := by
    filter_upwards [nativeFirstMargin_pos_le_slope_ae hX hi hG hE0.le,
      nativeFirstSelectedSlope_mul_le_ae hX hi hG hE0.le (n := nstar) hnpos,
      nativeFirstSelectedSlope_abs_le_envelope_ae hX hi hG hE0.le] with ω hpos hfit henv
    have hYnn : (0 : ℝ) ≤ |cumulativeSamples X nstar ω| := abs_nonneg _
    have hfirst : (0 : ℝ) ≤ (E+|cumulativeSamples X nstar ω|)/(nstar : ℝ) := by positivity
    have hsq : (0 : ℝ) ≤ env ω^2/T := by positivity
    by_cases hlt : nativeFirstDuration X E ω < nstar
    · have hind : F2 ω = T := by
        rw [hF2]
        exact if_pos hlt
      have hbound : env ω ≤ T+env ω^2/T := by
        rw [← sub_nonneg]
        have heq : T+env ω^2/T-env ω = (T^2-T*env ω+env ω^2)/T := by field_simp; ring
        rw [heq]
        apply div_nonneg _ hTpos.le
        nlinarith [sq_nonneg (2*T-env ω), sq_nonneg (env ω)]
      show max (nativeFirstMargin X E ω) 0 ≤ F1 ω+F2 ω+F3 ω
      rw [hind]
      show max (nativeFirstMargin X E ω) 0 ≤
        (E+|cumulativeSamples X nstar ω|)/(nstar : ℝ)+T+env ω^2/T
      linarith [hpos.trans henv]
    · have hge : nstar ≤ nativeFirstDuration X E ω := by omega
      have hm := hfit hge
      have hslope : |nativeFirstSelectedSlope X E ω| ≤
          (E+|cumulativeSamples X nstar ω|)/(nstar : ℝ) := by
        rw [le_div_iff₀ hnr]
        linarith [hm]
      have hind : F2 ω = 0 := by
        rw [hF2]
        exact if_neg hlt
      show max (nativeFirstMargin X E ω) 0 ≤ F1 ω+F2 ω+F3 ω
      rw [hind]
      show max (nativeFirstMargin X E ω) 0 ≤
        (E+|cumulativeSamples X nstar ω|)/(nstar : ℝ)+0+env ω^2/T
      linarith [hpos.trans hslope]
  have hposint : Integrable (fun ω => max (nativeFirstMargin X E ω) 0) μ := by
    refine hFint.mono'
      (((nativeFirstMargin_measurable hX E).max measurable_const).aestronglyMeasurable) ?_
    filter_upwards [hdom] with ω hω
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact hω
  have hmono : (∫ ω, max (nativeFirstMargin X E ω) 0 ∂μ) ≤ ∫ ω, F ω ∂μ :=
    integral_mono_ae hposint hFint hdom
  have hFval : (∫ ω, F ω ∂μ) = (E+∫ ω, |cumulativeSamples X nstar ω| ∂μ)/(nstar : ℝ)+
      T*μ.real A+(∫ ω, env ω^2 ∂μ)/T := by
    have e1 : (∫ ω, F ω ∂μ) = (∫ ω, (F1 ω+F2 ω) ∂μ)+∫ ω, F3 ω ∂μ :=
      integral_add (hF1int.add hF2int) hF3int
    have e2 : (∫ ω, (F1 ω+F2 ω) ∂μ) = (∫ ω, F1 ω ∂μ)+∫ ω, F2 ω ∂μ :=
      integral_add hF1int hF2int
    have e3 : (∫ ω, F1 ω ∂μ) = (E+∫ ω, |cumulativeSamples X nstar ω| ∂μ)/(nstar : ℝ) := by
      rw [hF1, integral_div, integral_add (integrable_const E) hYint, integral_const]
      simp
    have e4 : (∫ ω, F2 ω ∂μ) = T*μ.real A := by
      rw [hF2eq, integral_indicator_const _ hAmeas, smul_eq_mul, mul_comm]
    have e5 : (∫ ω, F3 ω ∂μ) = (∫ ω, env ω^2 ∂μ)/T := by rw [hF3, integral_div]
    rw [e1, e2, e3, e4, e5]
  rw [hFval] at hmono
  refine hmono.trans ?_
  have hY := integral_abs_cumulativeSamples_le hX hi hG hnpos
  have hsqrtn : Real.sqrt (nstar : ℝ) ≤ (nstar : ℝ)/T := by
    have hsq : Real.sqrt (nstar : ℝ)^2 = (nstar : ℝ) := Real.sq_sqrt hnr.le
    have hge : T^2 ≤ (nstar : ℝ) := by nlinarith
    have hTle : T ≤ Real.sqrt (nstar : ℝ) := by nlinarith [Real.sqrt_nonneg (nstar : ℝ)]
    rw [le_div_iff₀ hTpos]
    nlinarith [Real.sqrt_nonneg (nstar : ℝ)]
  have hterm1 : (E+∫ ω, |cumulativeSamples X nstar ω| ∂μ)/(nstar : ℝ) ≤ 2/T := by
    rw [div_le_iff₀ hnr]
    have hsplit : (2/T)*(nstar : ℝ) = (nstar : ℝ)/T+(nstar : ℝ)/T := by field_simp; ring
    rw [hsplit]
    have hEover : E ≤ (nstar : ℝ)/T := by
      rw [le_div_iff₀ hTpos]
      linarith
    linarith [hY.trans hsqrtn]
  have hterm3 : (∫ ω, env ω^2 ∂μ)/T ≤ envelopeSqBound/T := by
    have h := integral_envelope_sq_le hX hi hG
    exact div_le_div_of_nonneg_right (c := T) h hTpos.le
  have htail := measureReal_nativeFirstDuration_lt_le hX hi hG hE0.le hnpos
  have hexp0 : (0 : ℝ) < Real.exp (-E^2/(2*(nstar : ℝ))) := Real.exp_pos _
  have hexpb : Real.exp (-E^2/(2*(nstar : ℝ)))*E^3 ≤ 4096*46656 := by
    have hcut : T/4 ≤ E^2/(2*(nstar : ℝ)) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2*(nstar : ℝ))]
      have h2 : T*(nstar : ℝ) ≤ T*(2*(E*T)) := mul_le_mul_of_nonneg_left hnhigh2 hTpos.le
      have h3 : T*(2*(E*T)) = 2*E^2 := by
        have hr : T*(2*(E*T)) = 2*E*T^2 := by ring
        rw [hr, hTsq]
        ring
      rw [h3] at h2
      linarith
    have hmono2 : Real.exp (-E^2/(2*(nstar : ℝ))) ≤ Real.exp (-(T/4)) := by
      apply Real.exp_le_exp.mpr
      have hneg : -E^2/(2*(nstar : ℝ)) = -(E^2/(2*(nstar : ℝ))) := by ring
      rw [hneg]
      linarith
    have hpow := exp_ge_pow_six (u := T/4) (by linarith)
    have hE3 : (T/4)^6 = E^3/4096 := by
      have h6 : (T/4)^6 = (T^2)^3/4096 := by ring
      rw [h6, hTsq]
    rw [hE3] at hpow
    have hid : Real.exp (-(T/4))*Real.exp (T/4) = 1 := by rw [← Real.exp_add]; simp
    have hE3pos : (0 : ℝ) < E^3 := by positivity
    have hstep1 : Real.exp (-(T/4))*(E^3/4096/46656) ≤ Real.exp (-(T/4))*Real.exp (T/4) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    rw [hid] at hstep1
    have hrw : Real.exp (-(T/4))*(E^3/4096/46656) =
        (Real.exp (-(T/4))*E^3)/(4096*46656) := by ring
    rw [hrw, div_le_one (by norm_num : (0 : ℝ) < 4096*46656)] at hstep1
    have hfin : Real.exp (-E^2/(2*(nstar : ℝ)))*E^3 ≤ Real.exp (-(T/4))*E^3 :=
      mul_le_mul_of_nonneg_right hmono2 hE3pos.le
    linarith
  have hterm2 : T*μ.real A ≤ 764411904/T := by
    have h1 : T*μ.real A ≤ T*(2*(nstar : ℝ)*Real.exp (-E^2/(2*(nstar : ℝ)))) :=
      mul_le_mul_of_nonneg_left htail hTpos.le
    have hb : T*(2*(nstar : ℝ)) ≤ 4*E^2 := by
      have hmul := mul_le_mul_of_nonneg_left hnhigh2 (show (0 : ℝ) ≤ 2*T by linarith)
      nlinarith [hmul, hTsq]
    have h2 : T*(2*(nstar : ℝ)*Real.exp (-E^2/(2*(nstar : ℝ)))) ≤
        4*E^2*Real.exp (-E^2/(2*(nstar : ℝ))) := by
      have hm := mul_le_mul_of_nonneg_right hb hexp0.le
      nlinarith [hm]
    have h3 : 4*E^2*Real.exp (-E^2/(2*(nstar : ℝ))) ≤ 764411904/E := by
      rw [le_div_iff₀ hE0]
      nlinarith [hexpb]
    have h4 : (764411904 : ℝ)/E ≤ 764411904/T :=
      (div_le_div_iff_of_pos_left (by norm_num) hE0 hTpos).mpr hTE
    linarith
  have hsum : 2/T+764411904/T+envelopeSqBound/T = secondMarginPosConstant/T := by
    dsimp [secondMarginPosConstant]
    ring
  calc
    _ ≤ 2/T+764411904/T+envelopeSqBound/T := by linarith
    _ = secondMarginPosConstant/T := hsum

end SwingRepair
