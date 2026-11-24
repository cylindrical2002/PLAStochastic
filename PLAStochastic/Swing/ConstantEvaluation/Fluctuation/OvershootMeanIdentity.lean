import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.LadderDuality
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.SparreAndersenDrifted

/-! # The overshoot mean identity `β(a) = a/2 - 1/(2a) + 𝔼M_a` (roadmap 1.1(a), 1.3)

Let `Y = X_0 + a + I' = inf_{n≥1} S_n`.  The duality lemma gives, with `p = P(S_i > 0 ∀ i ≥ 1)`
and `ν = Law(H_a)`,

  `p 𝔼H_a = 𝔼Y₊`,  `p 𝔼H_a² = 𝔼Y₊²`.

Since `min(0, Y) = inf_{n≥0} S_n` has the law of `-M_a` and `I'` has the law of `-M_a`
as well (both are functionals of an i.i.d. standard Gaussian sequence), with `X_0`
independent of `I'`,

  `𝔼Y₊ = 𝔼Y - 𝔼 min(0,Y) = a`,   `𝔼Y₊² = 𝔼Y² - 𝔼 min(0,Y)² = 1 + a² - 2a 𝔼M_a`.

The equilibrium overshoot has mean `𝔼H_a²/(2𝔼H_a) = 𝔼Y₊²/(2𝔼Y₊)`, so

  `β(a) = a - 𝔼O_a = a/2 - 1/(2a) + 𝔼M_a`.

This closes `OvershootMeanIdentity X μ` and hence `OvershootMeanLipschitz X μ (3/4)`
unconditionally (`overshootMeanLipschitz_gaussian`).
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The dual variable `Y` and the two maxima -/

/-- `Y = X_0 + a + I' = inf_{n ≥ 1} S_n`. -/
def ladderDualVariable (X : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℝ :=
  X 0 ω + a + shiftInf X a ω

omit [MeasurableSpace Ω] in
theorem negDriftWalk_neg_eq (a : ℝ) (n : ℕ) (ω : Ω) :
    negDriftWalk (fun k ω => -X k ω) a n ω = -gaussianDriftWalk X 0 a n ω := by
  simp only [negDriftWalk_eq, gaussianDriftWalk, cumulativeSamples, Finset.sum_neg_distrib,
    zero_add]
  ring

omit [MeasurableSpace Ω] in
/-- `sup_{n≥0}(-S_n) = max(0, -Y)` whenever the shifted maximum is attained. -/
theorem driftMaximum_neg_eq_max {a : ℝ} {ω : Ω}
    (h : DriftMaxAttained (fun k ω => -X (1 + k) ω) a ω) :
    driftMaximum (fun k ω => -X k ω) a ω = max 0 (-ladderDualVariable X a ω) := by
  set Ms := driftMaximum (fun k ω => -X (1 + k) ω) a ω with hMs
  set c : ℝ := -(X 0 ω + a) with hc
  have hY : -ladderDualVariable X a ω = c + Ms := by
    simp only [ladderDualVariable, shiftInf, hc, hMs]
    ring
  have hF0 : negDriftWalk (fun k ω => -X k ω) a 0 ω = 0 := negDriftWalk_zero _ _ _
  have hFsucc : ∀ m, negDriftWalk (fun k ω => -X k ω) a (m + 1) ω =
      c + negDriftWalk (fun k ω => -X (1 + k) ω) a m ω := by
    intro m
    rw [negDriftWalk_neg_eq, negDriftWalk_neg_shift, gaussianDriftWalk_succ_eq_shiftWalk, hc]
    ring
  have hle : ∀ n, negDriftWalk (fun k ω => -X k ω) a n ω ≤ max 0 (c + Ms) := by
    intro n
    cases n with
    | zero => rw [hF0]; exact le_max_left _ _
    | succ m =>
      rw [hFsucc]
      have hGm : negDriftWalk (fun k ω => -X (1 + k) ω) a m ω ≤ Ms := le_driftMaximum h m
      exact le_trans (by linarith) (le_max_right 0 (c + Ms))
  have hbdd : BddAbove (Set.range fun n => negDriftWalk (fun k ω => -X k ω) a n ω) :=
    ⟨_, forall_mem_range.mpr hle⟩
  rw [hY]
  unfold driftMaximum
  apply le_antisymm (ciSup_le hle)
  apply max_le
  · rw [← hF0]
    exact le_ciSup hbdd 0
  · have hMs' : Ms = negDriftWalk (fun k ω => -X (1 + k) ω) a (driftArgmax
        (fun k ω => -X (1 + k) ω) a ω) ω := driftMaximum_eq_argmax h
    rw [hMs', ← hFsucc]
    exact le_ciSup hbdd _

omit [MeasurableSpace Ω] in
theorem max_eq_add_max_neg (y : ℝ) : max y 0 = y + max 0 (-y) := by
  rcases le_or_gt 0 y with h | h
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  · rw [max_eq_right h.le, max_eq_right (by linarith)]; ring

omit [MeasurableSpace Ω] in
theorem max_sq_eq_sq_sub (y : ℝ) : (max y 0) ^ 2 = y ^ 2 - (max 0 (-y)) ^ 2 := by
  rcases le_or_gt 0 y with h | h
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring
  · rw [max_eq_right h.le, max_eq_right (by linarith)]; ring

/-! ### Independence of `X_0` and the shifted maximum -/

omit [MeasurableSpace Ω] in
theorem driftMaximum_neg_shift_measurable_in (a : ℝ) :
    Measurable[incrementIndexSpace X (Ioi 0)] (driftMaximum (fun k ω => -X (1 + k) ω) a) := by
  let : MeasurableSpace Ω := incrementIndexSpace X (Ioi 0)
  unfold driftMaximum
  refine Measurable.iSup fun j => ?_
  have : negDriftWalk (fun k ω => -X (1 + k) ω) a j = fun ω => -shiftWalk X a j ω := by
    funext ω; exact negDriftWalk_neg_shift a j ω
  rw [this]
  exact (shiftWalk_measurable_in (S := Ioi 0) (fun k _ => by simp) a).neg

theorem indepFun_X0_driftMaximum_neg_shift (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (a : ℝ) : IndepFun (X 0) (driftMaximum (fun k ω => -X (1 + k) ω) a) μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [IndepFun_iff_Indep]
  have hdis : Disjoint ({0} : Set ℕ) (Ioi 0) := by
    rw [Set.disjoint_left]
    intro k hk hk'
    simp only [mem_singleton_iff] at hk
    simp only [mem_Ioi] at hk'
    omega
  have hind : Indep (incrementIndexSpace X {0}) (incrementIndexSpace X (Ioi 0)) μ :=
    indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hdis
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hind ?_) ?_
  · exact measurable_iff_comap_le.mp (driftMaximum_neg_shift_measurable_in a)
  · exact measurable_iff_comap_le.mp (incrementIndexSpace_eval (X := X) (S := {0}) rfl)

/-! ### Moments of `Y₊` -/

theorem memLp_two_X0 (hX : ∀ n, Measurable (X n)) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    MemLp (X 0) 2 μ :=
  (iid_standardGaussian_hasGaussianLaw hX hG 0).memLp_two

theorem integral_X0_sq (hX : ∀ n, Measurable (X n)) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∫ ω, X 0 ω ^ 2 ∂μ = 1 := by
  have hl : HasLaw (X 0) (gaussianReal 0 1) μ := ⟨(hX 0).aemeasurable, hG 0⟩
  have := hl.integral_comp (f := fun z : ℝ => z ^ 2) (by fun_prop)
  simp only [Function.comp_def] at this
  rw [this, integral_sq_standardGaussian]

/-- The moments of `Y₊`: `𝔼Y₊ = a` and `𝔼Y₊² = 1 + a² - 2a 𝔼M_a`. -/
theorem ladderDualVariable_posPart_moments (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => max (ladderDualVariable X a ω) 0) μ ∧
    Integrable (fun ω => (max (ladderDualVariable X a ω) 0) ^ 2) μ ∧
    ∫ ω, max (ladderDualVariable X a ω) 0 ∂μ = a ∧
    ∫ ω, (max (ladderDualVariable X a ω) 0) ^ 2 ∂μ =
      1 + a ^ 2 - 2 * a * ∫ ω, driftMaximum X a ω ∂μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  obtain ⟨hXs, his, hGs⟩ := iidGaussian_shift hX hi hG 1
  obtain ⟨hXns, hins, hGns⟩ := iidGaussian_neg hXs his hGs
  set Mf : Ω → ℝ := driftMaximum (fun k ω => -X k ω) a with hMf
  set Ms : Ω → ℝ := driftMaximum (fun k ω => -X (1 + k) ω) a with hMs
  set Y : Ω → ℝ := ladderDualVariable X a with hYdef
  have hYeq : Y = fun ω => X 0 ω + a - Ms ω := by
    funext ω; simp only [hYdef, ladderDualVariable, shiftInf, hMs]; ring
  -- integrability
  have hX0 : MemLp (X 0) 2 μ := memLp_two_X0 hX hG
  have hX0i : Integrable (X 0) μ := hX0.integrable one_le_two
  have hX0sq : Integrable (fun ω => X 0 ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hX 0).aestronglyMeasurable).mp hX0
  have hX0a : Integrable (fun ω => X 0 ω + a) μ := hX0i.add (integrable_const a)
  have hMsL2 : MemLp Ms 2 μ := memLp_two_driftMaximum hXns hins hGns ha
  have hMsi : Integrable Ms μ := integrable_driftMaximum hXns hins hGns ha
  have hMssq : Integrable (fun ω => Ms ω ^ 2) μ := integrable_driftMaximum_sq hXns hins hGns ha
  have hMfi : Integrable Mf μ := integrable_driftMaximum hXn hin hGn ha
  have hMfsq : Integrable (fun ω => Mf ω ^ 2) μ := integrable_driftMaximum_sq hXn hin hGn ha
  have hXMs : Integrable (fun ω => X 0 ω * Ms ω) μ := hX0.integrable_mul hMsL2
  have hYi : Integrable Y μ := by
    rw [hYeq]; exact ((hX0i.add (integrable_const a))).sub hMsi
  have hYL2 : MemLp Y 2 μ := by
    rw [hYeq]; exact (hX0.add (memLp_const a)).sub hMsL2
  have hYsq : Integrable (fun ω => Y ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq hYL2.1).mp hYL2
  -- the same law for the three maxima
  have hEf : ∫ ω, Mf ω ∂μ = ∫ ω, driftMaximum X a ω ∂μ := by
    simpa using integral_driftMaximum_eq hXn hin hGn hX hi hG a (φ := fun x => x) measurable_id
  have hEs : ∫ ω, Ms ω ∂μ = ∫ ω, driftMaximum X a ω ∂μ := by
    simpa using integral_driftMaximum_eq hXns hins hGns hX hi hG a (φ := fun x => x) measurable_id
  have hEfsq : ∫ ω, Mf ω ^ 2 ∂μ = ∫ ω, Ms ω ^ 2 ∂μ :=
    integral_driftMaximum_eq hXn hin hGn hXns hins hGns a (φ := fun x => x ^ 2) (by fun_prop)
  -- pathwise identities
  have hae : ∀ᵐ ω ∂μ, Mf ω = max 0 (-Y ω) := by
    filter_upwards [driftMaxAttained_ae hXns hins hGns ha] with ω hω
    exact driftMaximum_neg_eq_max hω
  have hpos_eq : (fun ω => max (Y ω) 0) =ᵐ[μ] fun ω => Y ω + Mf ω := by
    filter_upwards [hae] with ω hω
    rw [hω, max_eq_add_max_neg]
  have hpossq_eq : (fun ω => (max (Y ω) 0) ^ 2) =ᵐ[μ] fun ω => Y ω ^ 2 - Mf ω ^ 2 := by
    filter_upwards [hae] with ω hω
    rw [hω, max_sq_eq_sq_sub]
  -- Gaussian moments and independence
  have hEX0 : ∫ ω, X 0 ω ∂μ = 0 := (iid_standardGaussian_mean_variance hX hG 0).1
  have hEX0sq : ∫ ω, X 0 ω ^ 2 ∂μ = 1 := integral_X0_sq hX hG
  have hEXMs : ∫ ω, X 0 ω * Ms ω ∂μ = 0 := by
    have h := (indepFun_X0_driftMaximum_neg_shift hX hi a).integral_mul_eq_mul_integral
      (hX 0).aestronglyMeasurable (driftMaximum_measurable hXns a).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, hEX0, zero_mul]
  -- first moment
  have hX0a : Integrable (fun ω => X 0 ω + a) μ := hX0i.add (integrable_const a)
  have hEY : ∫ ω, Y ω ∂μ = a - ∫ ω, driftMaximum X a ω ∂μ := by
    calc ∫ ω, Y ω ∂μ = ∫ ω, (X 0 ω + a) ∂μ - ∫ ω, Ms ω ∂μ := by
          rw [hYeq]; exact integral_sub hX0a hMsi
      _ = (∫ ω, X 0 ω ∂μ + ∫ ω, (a : ℝ) ∂μ) - ∫ ω, Ms ω ∂μ := by
          rw [integral_add hX0i (integrable_const a)]
      _ = a - ∫ ω, driftMaximum X a ω ∂μ := by
          rw [hEX0, integral_const, hEs]
          simp
  have hEYsq : ∫ ω, Y ω ^ 2 ∂μ =
      1 + a ^ 2 - 2 * a * (∫ ω, driftMaximum X a ω ∂μ) + ∫ ω, Ms ω ^ 2 ∂μ := by
    have hexp : (fun ω => Y ω ^ 2) = fun ω =>
        (X 0 ω ^ 2 + 2 * a * X 0 ω + a ^ 2 - 2 * (X 0 ω * Ms ω)) - 2 * a * Ms ω + Ms ω ^ 2 := by
      funext ω; rw [hYeq]; ring
    rw [hexp, integral_add _ hMssq, integral_sub _ (hMsi.const_mul _),
      integral_sub _ (hXMs.const_mul _), integral_add _ (integrable_const _),
      integral_add hX0sq (hX0i.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, hEX0, hEX0sq, hEXMs, hEs, integral_const]
    · simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero, sub_zero]
    · exact hX0sq.add (hX0i.const_mul _)
    · exact (hX0sq.add (hX0i.const_mul _)).add (integrable_const _)
    · exact ((hX0sq.add (hX0i.const_mul _)).add (integrable_const _)).sub (hXMs.const_mul _)
    · exact (((hX0sq.add (hX0i.const_mul _)).add (integrable_const _)).sub
        (hXMs.const_mul _)).sub (hMsi.const_mul _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hYi.add hMfi).congr hpos_eq.symm
  · exact (hYsq.sub hMfsq).congr hpossq_eq.symm
  · rw [integral_congr_ae hpos_eq, integral_add hYi hMfi, hEY, hEf]
    ring
  · rw [integral_congr_ae hpossq_eq, integral_sub hYsq hMfsq, hEYsq, hEfsq]
    ring

/-! ### The duality lemma in real form -/

theorem indicator_Ioi_ofReal (y : ℝ) :
    (Ioi (0 : ℝ)).indicator (fun h : ℝ => ENNReal.ofReal h) y = ENNReal.ofReal (max y 0) := by
  by_cases hy : 0 < y
  · rw [Set.indicator_of_mem (show y ∈ Ioi 0 from hy), max_eq_left hy.le]
  · rw [Set.indicator_of_notMem (show y ∉ Ioi 0 from hy), max_eq_right (not_lt.mp hy),
      ENNReal.ofReal_zero]

theorem indicator_Ioi_ofReal_sq (y : ℝ) :
    (Ioi (0 : ℝ)).indicator (fun h : ℝ => ENNReal.ofReal (h ^ 2)) y =
      ENNReal.ofReal ((max y 0) ^ 2) := by
  by_cases hy : 0 < y
  · rw [Set.indicator_of_mem (show y ∈ Ioi 0 from hy), max_eq_left hy.le]
  · rw [Set.indicator_of_notMem (show y ∉ Ioi 0 from hy), max_eq_right (not_lt.mp hy)]
    simp

/-- `p 𝔼H = 𝔼Y₊` and `p 𝔼H² = 𝔼Y₊²`, with `p = μ(posWalkSet)` as a real number. -/
theorem ladder_duality_moments (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    (μ (posWalkSet X a)).toReal * ∫ x, x ∂gaussianAscendingLadderLaw X μ a =
        ∫ ω, max (ladderDualVariable X a ω) 0 ∂μ ∧
      (μ (posWalkSet X a)).toReal * ∫ x, x ^ 2 ∂gaussianAscendingLadderLaw X μ a =
        ∫ ω, (max (ladderDualVariable X a ω) 0) ^ 2 ∂μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  obtain ⟨hYi, hYsqi, -, -⟩ := ladderDualVariable_posPart_moments hX hi hG ha
  have hHm : Measurable (gaussianAscendingLadderHeight X a) :=
    gaussianAscendingLadderHeight_measurable hX a
  have hHnn : ∀ ω, 0 ≤ gaussianAscendingLadderHeight X a ω :=
    gaussianAscendingLadderHeight_nonneg a
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianAscendingLadderLaw X μ a) :=
    gaussianAscendingLadderLaw_sq_integrable hX hi hG ha le_rfl le_rfl
  have hνprob : IsProbabilityMeasure (gaussianAscendingLadderLaw X μ a) :=
    gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hid : Integrable (fun x : ℝ => x) (gaussianAscendingLadderLaw X μ a) :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq).integrable one_le_two
  have hHi : Integrable (gaussianAscendingLadderHeight X a) μ :=
    (integrable_map_measure aestronglyMeasurable_id hHm.aemeasurable).mp hid
  have hHsqi : Integrable (fun ω => gaussianAscendingLadderHeight X a ω ^ 2) μ :=
    (integrable_map_measure (by fun_prop) hHm.aemeasurable).mp hsq
  have hpfin : μ (posWalkSet X a) ≠ ⊤ := measure_ne_top _ _
  constructor
  · have h := ladder_duality hX hi hG ha (f := fun h => ENNReal.ofReal h) ENNReal.measurable_ofReal
    simp_rw [indicator_Ioi_ofReal] at h
    change μ (posWalkSet X a) * ∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X a ω) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (max (ladderDualVariable X a ω) 0) ∂μ at h
    rw [← ofReal_integral_eq_lintegral_ofReal hHi (ae_of_all _ hHnn),
      ← ofReal_integral_eq_lintegral_ofReal hYi (ae_of_all _ fun ω => le_max_right _ _)] at h
    have hint : ∫ ω, gaussianAscendingLadderHeight X a ω ∂μ =
        ∫ x, x ∂gaussianAscendingLadderLaw X μ a := by
      rw [gaussianAscendingLadderLaw, integral_map (f := fun x : ℝ => x) hHm.aemeasurable
        aestronglyMeasurable_id]
    rw [hint] at h
    have hnn1 : 0 ≤ ∫ x, x ∂gaussianAscendingLadderLaw X μ a :=
      integral_nonneg_of_ae (gaussianAscendingLadderLaw_nonneg_ae hX a)
    have hnn2 : 0 ≤ ∫ ω, max (ladderDualVariable X a ω) 0 ∂μ :=
      integral_nonneg fun ω => le_max_right _ _
    have := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn1, ENNReal.toReal_ofReal hnn2] at this
  · have h := ladder_duality hX hi hG ha (f := fun h => ENNReal.ofReal (h ^ 2)) (by fun_prop)
    simp_rw [indicator_Ioi_ofReal_sq] at h
    change μ (posWalkSet X a) *
        ∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X a ω ^ 2) ∂μ =
      ∫⁻ ω, ENNReal.ofReal ((max (ladderDualVariable X a ω) 0) ^ 2) ∂μ at h
    rw [← ofReal_integral_eq_lintegral_ofReal hHsqi (ae_of_all _ fun ω => sq_nonneg _),
      ← ofReal_integral_eq_lintegral_ofReal hYsqi (ae_of_all _ fun ω => sq_nonneg _)] at h
    have hint : ∫ ω, gaussianAscendingLadderHeight X a ω ^ 2 ∂μ =
        ∫ x, x ^ 2 ∂gaussianAscendingLadderLaw X μ a := by
      rw [gaussianAscendingLadderLaw, integral_map hHm.aemeasurable (by fun_prop)]
    rw [hint] at h
    have hnn1 : 0 ≤ ∫ x, x ^ 2 ∂gaussianAscendingLadderLaw X μ a :=
      integral_nonneg fun x => sq_nonneg _
    have hnn2 : 0 ≤ ∫ ω, (max (ladderDualVariable X a ω) 0) ^ 2 ∂μ :=
      integral_nonneg fun ω => sq_nonneg _
    have := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn1, ENNReal.toReal_ofReal hnn2] at this

/-! ### The mean of the equilibrium overshoot law -/

/-- `∫⁻ o dO = (𝔼_ν x)⁻¹ ∫⁻ x²/2 dν`. -/
theorem lintegral_equilibriumOvershootLaw_id (ν : Measure ℝ) [SFinite ν]
    (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x) :
    ∫⁻ o, ENNReal.ofReal o ∂equilibriumOvershootLaw ν =
      (ladderMeanENN ν)⁻¹ * ∫⁻ x, ENNReal.ofReal (x ^ 2 / 2) ∂ν := by
  have hdens : Measurable fun o : ℝ => ν (Ioi o) / ladderMeanENN ν :=
    (measurable_ladderTail ν).div_const _
  rw [equilibriumOvershootLaw, lintegral_withDensity_eq_lintegral_mul _ hdens
    ENNReal.measurable_ofReal]
  have hIci : (volume.restrict (Ici (0 : ℝ))) = volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  rw [hIci]
  have hrew : (fun o : ℝ => ν (Ioi o) / ladderMeanENN ν * ENNReal.ofReal o) =
      fun o : ℝ => (ladderMeanENN ν)⁻¹ * (ν {x : ℝ | o < x} * ENNReal.ofReal o) := by
    funext o
    rw [div_eq_mul_inv]
    have : Ioi o = {x : ℝ | o < x} := rfl
    rw [this]
    ring
  have hf : Measurable fun o : ℝ => ν {x : ℝ | o < x} * ENNReal.ofReal o :=
    (measurable_ladderTail ν).mul ENNReal.measurable_ofReal
  simp_rw [Pi.mul_apply]
  rw [show (fun o : ℝ => ν (Ioi o) / ladderMeanENN ν * ENNReal.ofReal o) =
      fun o : ℝ => (ladderMeanENN ν)⁻¹ * (ν {x : ℝ | o < x} * ENNReal.ofReal o) from hrew,
    lintegral_const_mul _ hf]
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul ν (f := fun x : ℝ => x)
    (g := fun t : ℝ => t) hnn aemeasurable_id (fun t _ => continuous_id.intervalIntegrable 0 t)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => le_of_lt ht)
  rw [← hlayer]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [integral_id]
  simp

/-- `𝔼O = 𝔼_ν x² / (2 𝔼_ν x)` for the equilibrium overshoot law of a nonnegative
inter-arrival law with finite second moment and positive mean. -/
theorem integral_equilibriumOvershootLaw_id (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x) (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hmean : 0 < ∫ x, x ∂ν) :
    ∫ o, o ∂equilibriumOvershootLaw ν = (∫ x, x ^ 2 ∂ν) / (2 * ∫ x, x ∂ν) := by
  have hid : Integrable (fun x : ℝ => x) ν :=
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq).integrable one_le_two
  have hmeanENN : ladderMeanENN ν = ENNReal.ofReal (∫ x, x ∂ν) := by
    rw [ladderMeanENN, ofReal_integral_eq_lintegral_ofReal hid hnn]
  have hsqENN : ∫⁻ x, ENNReal.ofReal (x ^ 2 / 2) ∂ν = ENNReal.ofReal ((∫ x, x ^ 2 ∂ν) / 2) := by
    rw [← integral_div, ofReal_integral_eq_lintegral_ofReal (hsq.div_const 2)
      (ae_of_all _ fun x => by positivity)]
  have hOnn : 0 ≤ᵐ[equilibriumOvershootLaw ν] fun o : ℝ => o := by
    have h0 : equilibriumOvershootLaw ν (Iio 0) = 0 := by
      rw [equilibriumOvershootLaw_apply _ measurableSet_Iio]
      have : Iio (0 : ℝ) ∩ Ici 0 = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_empty_iff_false, iff_false, not_and,
          not_le]
        intro h; exact h
      rw [this, Measure.restrict_empty, lintegral_zero_measure]
    rw [Filter.EventuallyLE, ae_iff]
    convert h0 using 2
    ext o
    simp [not_le]
  rw [integral_eq_lintegral_of_nonneg_ae hOnn aestronglyMeasurable_id,
    lintegral_equilibriumOvershootLaw_id ν hnn, hmeanENN, hsqENN, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hmean.le,
    ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-! ### The identity -/

theorem overshootMean_eq_sub (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    overshootMean X μ a =
      a - ∫ o, o ∂equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set O := equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a) with hO
  have hOprob : IsProbabilityMeasure O := gaussianAscendingLadderEquilibrium_isProbability hX hi hG ha
  have hOid : Integrable (fun o : ℝ => o) O := by
    have := swingOvershootMeasure_integrable_id hX hi hG ha
    rw [swingOvershootMeasure, integrable_map_measure (g := fun r : ℝ => r) aestronglyMeasurable_id
      (measurable_const_sub_self a).aemeasurable] at this
    have h2 := (integrable_const a).sub this
    refine h2.congr (ae_of_all _ fun o => ?_)
    simp
  rw [overshootMean, swingOvershootMeasure,
    integral_map (f := fun r : ℝ => r) (measurable_const_sub_self a).aemeasurable
      aestronglyMeasurable_id]
  rw [integral_sub (integrable_const a) hOid, integral_const]
  simp

/-- **The overshoot mean identity** `β(a) = a/2 - 1/(2a) + 𝔼M_a`, unconditionally. -/
theorem overshootMeanIdentity_gaussian (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) : OvershootMeanIdentity X μ := by
  intro a ha
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  refine ⟨integrable_driftMaximum hX hi hG ha, ?_⟩
  set ν := gaussianAscendingLadderLaw X μ a with hν
  have hνprob : IsProbabilityMeasure ν := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hnn : 0 ≤ᵐ[ν] fun x : ℝ => x := gaussianAscendingLadderLaw_nonneg_ae hX a
  have hsq : Integrable (fun x : ℝ => x ^ 2) ν :=
    gaussianAscendingLadderLaw_sq_integrable hX hi hG ha le_rfl le_rfl
  obtain ⟨-, -, hEY, hEYsq⟩ := ladderDualVariable_posPart_moments hX hi hG ha
  obtain ⟨hd1, hd2⟩ := ladder_duality_moments hX hi hG ha
  rw [hEY] at hd1
  rw [hEYsq] at hd2
  set p := (μ (posWalkSet X a)).toReal with hp
  set m₁ := ∫ x, x ∂ν with hm₁
  set m₂ := ∫ x, x ^ 2 ∂ν with hm₂
  set EM := ∫ ω, driftMaximum X a ω ∂μ with hEM
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hm₁nn : 0 ≤ m₁ := integral_nonneg_of_ae hnn
  have hm₁pos : 0 < m₁ := by
    by_contra hcon
    push Not at hcon
    have : p * m₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 hcon
    linarith
  have hppos : 0 < p := by
    by_contra hcon
    push Not at hcon
    have hp' : p = 0 := le_antisymm hcon hp0
    rw [hp', zero_mul] at hd1
    linarith
  rw [overshootMean_eq_sub hX hi hG ha, integral_equilibriumOvershootLaw_id ν hnn hsq hm₁pos]
  rw [← hm₁, ← hm₂]
  -- m₂ / (2 m₁) = (p m₂) / (2 (p m₁)) = (1 + a² - 2a EM) / (2a)
  have hkey : m₂ / (2 * m₁) = (1 + a ^ 2 - 2 * a * EM) / (2 * a) := by
    calc m₂ / (2 * m₁) = (p * m₂) / (2 * (p * m₁)) := by
          field_simp
      _ = (1 + a ^ 2 - 2 * a * EM) / (2 * a) := by rw [hd1, hd2]
  rw [hkey]
  field_simp
  ring

/-- **`OvershootMeanLipschitz X μ (3/4)` unconditionally**: `β(c) - β(a) ≤ (3/4)(c - a)`
for `0 < a ≤ c`. -/
theorem overshootMeanLipschitz_gaussian (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) : OvershootMeanLipschitz X μ (3 / 4) :=
  overshootMeanLipschitz_of_identity hX hi hG (overshootMeanIdentity_gaussian hX hi hG)

/-- The two-sided bound `(1/2)(c - a) ≤ β(c) - β(a) ≤ (3/4)(c - a)`, unconditionally. -/
theorem overshootMean_bounds_gaussian (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    1 / 2 * (c - a) ≤ overshootMean X μ c - overshootMean X μ a ∧
      overshootMean X μ c - overshootMean X μ a ≤ 3 / 4 * (c - a) :=
  overshootMean_bounds_of_identity_sparreAndersen hX hi hG (overshootMeanIdentity_gaussian hX hi hG)
    (sparreAndersenArgmax_gaussian hX hi hG) ha hac

end SwingRepair
