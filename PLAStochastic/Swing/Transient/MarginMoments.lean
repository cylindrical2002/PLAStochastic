import PLAStochastic.Swing.StationaryScale.MarginMomentsNat
import PLAStochastic.Swing.StationaryScale.SegmentMeanScale
import PLAStochastic.Swing.Restart.Chain.MarkovLaw
import PLAStochastic.Swing.SecondSegment.FrozenMeanBridge

/-! # Uniform margin moments along the actual transient stream

`app:transientconvergence`, first subsection (`eq:transient-fullmoments`).  The
actual carried state after `k` recorded segments has law
`σ_{k,E} = μ ∘ (nativeRestartRecordingState X E k)⁻¹`, and
`σ_{k+1,E} = P_E σ_{k,E}` for the measurable constrained-SSE restart kernel
`P_E`.  Lemma G.1 bounds every moment of the first margin `R_{1,E} = E - |σ_1|`
uniformly in the budget.  This file propagates such bounds through one
transition of `P_E` *without* any stationarity of the input law: the
fixed-state tail bounds of Appendix `app:margins` (`StationaryPiETail`,
`StationaryBadBranch`) are integrated against an arbitrary input probability
law, and the complementary-branch probability is estimated by Markov's
inequality on the input margin instead of by invariance.  Induction on the
segment index then gives, for every fixed `j ≥ 1` and `k ≥ 1`, a bound on
`∫ |E - |y||^k dσ_{j,E}` valid for every budget above the Theorem 4.2
threshold.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The actual state laws -/

/-- The law of the actual carried state after `k` recorded segments. -/
def nativeTransientLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) (k : ℕ) : Measure ℝ :=
  μ.map (nativeRestartRecordingState X E k)

theorem nativeTransientLaw_isProbability [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (E : ℝ) (k : ℕ) :
    IsProbabilityMeasure (nativeTransientLaw X μ E k) :=
  Measure.isProbabilityMeasure_map (nativeRestartRecordingState_measurable hX E k).aemeasurable

theorem nativeTransientLaw_succ
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    nativeTransientLaw X μ E (k+1) = nativeRestartKernel X μ E ∘ₘ nativeTransientLaw X μ E k :=
  nativeRestartRecordingState_law_succ hX hi hG hE k

theorem nativeTransientLaw_one
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    nativeTransientLaw X μ E 1 = μ.map (nativeFirstNext X E) :=
  Measure.map_congr (nativeRestartRecordingState_one_ae hX hi hG hE)

/-- `E N_{k+1} = ∫ g_E dσ_{k,E}`: the mean of the `(k+1)`-st actual segment is the
conditional restart mean averaged over the state law after `k` segments. -/
theorem nativeRecordingDurationNat_mean_transientLaw
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (k : ℕ) :
    (∫ ω, (nativeRecordingDurationNat X E k ω : ℝ) ∂μ) =
      ∫ x, nativeRestartMean X μ E x ∂nativeTransientLaw X μ E k :=
  nativeRecordingDurationNat_mean hX hi hG hE k

/-! ### The output law of one transition, in product form -/

theorem nativeRestartKernel_eq_map [SFinite μ] (hX : ∀ n, Measurable (X n)) (E x : ℝ) :
    nativeRestartKernel X μ E x = μ.map (fun ω => nativeRestartNext X E x ω) := by
  have hnext : Measurable (fun ω => nativeRestartNext X E x ω) :=
    (nativeRestartNext_measurable X hX E).comp ((measurable_const (a := x)).prodMk measurable_id)
  ext s hs
  rw [nativeRestartKernel_apply hX E x hs, Measure.map_apply hnext hs]
  rfl

theorem nativeRestart_output_apply [SFinite μ] (hX : ∀ n, Measurable (X n)) (E : ℝ)
    {σ : Measure ℝ} [SFinite σ] {B : Set ℝ} (hB : MeasurableSet B) :
    (nativeRestartKernel X μ E ∘ₘ σ) B =
      (σ.prod μ) ((fun p : ℝ × Ω => nativeRestartNext X E p.1 p.2) ⁻¹' B) := by
  rw [nativeRestartKernel_comp_eq_map_prod hX E,
    Measure.map_apply (nativeRestartNext_measurable X hX E) hB]

theorem nativeRestart_output_isProbability [IsProbabilityMeasure μ] (hX : ∀ n, Measurable (X n))
    (E : ℝ) {σ : Measure ℝ} [IsProbabilityMeasure σ] :
    IsProbabilityMeasure (nativeRestartKernel X μ E ∘ₘ σ) := by
  have := nativeRestartKernel_isMarkov (μ := μ) hX E
  infer_instance

/-! ### Output negative-margin tails for an arbitrary input law -/

theorem measurableSet_excess_gt (E t : ℝ) :
    MeasurableSet {y : ℝ | t < nativeRestartExcess E y} := by
  unfold nativeRestartExcess
  exact measurableSet_lt measurable_const ((measurable_id.abs.sub_const E).max measurable_const)

/-- `eq:transient-refinedtail`, first alternative: Gaussian tail plus the
complementary branch of the input law. -/
theorem nativeRestart_output_excess_tail_refined [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {t : ℝ} (ht : 0 ≤ t) :
    (nativeRestartKernel X μ E ∘ₘ σ) {y | t < nativeRestartExcess E y} ≤
      ENNReal.ofReal (Real.exp (-t^2/2)) + (σ.prod μ) (nativeRestartFavorableSet X E)ᶜ := by
  rw [nativeRestart_output_apply hX E (measurableSet_excess_gt E t),
    nativeRestartNextExcess_preimage]
  have hsplit : {p : ℝ × Ω | t < nativeRestartNextExcess X E p} ⊆
      (nativeRestartFavorableSet X E ∩ {p | t < nativeRestartNextExcess X E p}) ∪
        (nativeRestartFavorableSet X E)ᶜ := by
    intro p hp
    by_cases hg : p ∈ nativeRestartFavorableSet X E
    · exact Or.inl ⟨hg, hp⟩
    · exact Or.inr hg
  calc
    (σ.prod μ) {p : ℝ × Ω | t < nativeRestartNextExcess X E p}
        ≤ (σ.prod μ) ((nativeRestartFavorableSet X E ∩
            {p | t < nativeRestartNextExcess X E p}) ∪
              (nativeRestartFavorableSet X E)ᶜ) := measure_mono hsplit
    _ ≤ (σ.prod μ) (nativeRestartFavorableSet X E ∩
            {p | t < nativeRestartNextExcess X E p}) +
          (σ.prod μ) (nativeRestartFavorableSet X E)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t^2/2)) +
          (σ.prod μ) (nativeRestartFavorableSet X E)ᶜ :=
      add_le_add (measure_prod_nativeRestart_favorable_tail hX hi hG hE.le ht) le_rfl

/-- `eq:transient-refinedtail`, second alternative: the stopped-sum tail costs
only the mean segment length of the input law. -/
theorem nativeRestart_output_excess_tail_raw [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {t : ℝ} (ht : 0 ≤ t) :
    (nativeRestartKernel X μ E ∘ₘ σ) {y | t < nativeRestartExcess E y} ≤
      ENNReal.ofReal ((∫ x, nativeRestartMean X μ E x ∂σ)*(2*Real.exp (-t^2/2))) := by
  rw [nativeRestart_output_apply hX E (measurableSet_excess_gt E t),
    nativeRestartNextExcess_preimage]
  exact measure_prod_nativeRestart_raw_tail hX hi hG hE ht

/-! ### The complementary branch through Markov's inequality on the input -/

theorem nativeRestartMarginPos_le_abs (E y : ℝ) : nativeRestartMarginPos E y ≤ |E-abs y| :=
  max_le (le_abs_self _) (abs_nonneg _)

theorem nativeRestartExcess_le_abs (E y : ℝ) : nativeRestartExcess E y ≤ |E-abs y| := by
  unfold nativeRestartExcess
  refine max_le ?_ (abs_nonneg _)
  rw [abs_sub_comm]
  exact le_abs_self _

/-- Markov's inequality for the input margin at level `E/40`. -/
theorem measure_margin_gt_le_of_moment {σ : Measure ℝ} [IsProbabilityMeasure σ] {E : ℝ}
    (hE : 0 < E) (hint : Integrable (fun y : ℝ => |E-abs y|) σ) {f : ℝ → ℝ}
    (hf : ∀ y, f y ≤ |E-abs y|) :
    σ {y : ℝ | E/40 < f y} ≤ ENNReal.ofReal (40*(∫ y, |E-abs y| ∂σ)/E) := by
  have hsub : {y : ℝ | E/40 < f y} ⊆ {y : ℝ | E/40 ≤ |E-abs y|} := by
    intro y hy
    exact le_of_lt (lt_of_lt_of_le hy (hf y))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := σ)
    (f := fun y : ℝ => |E-abs y|) (ae_of_all _ fun y => abs_nonneg _) hint (E/40)
  have h40 : (0 : ℝ) < E/40 := by positivity
  have hreal : σ.real {y : ℝ | E/40 ≤ |E-abs y|} ≤ 40*(∫ y, |E-abs y| ∂σ)/E := by
    rw [le_div_iff₀ hE]
    have := hmarkov
    nlinarith
  calc σ {y : ℝ | E/40 < f y} ≤ σ {y : ℝ | E/40 ≤ |E-abs y|} := measure_mono hsub
    _ = ENNReal.ofReal (σ.real {y : ℝ | E/40 ≤ |E-abs y|}) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (40*(∫ y, |E-abs y| ∂σ)/E) := ENNReal.ofReal_le_ofReal hreal

/-- `eq:transient-badbranch` for an arbitrary input law: the complementary
branch costs the input first margin moment over `E` plus the input mean
segment length over `E²`. -/
theorem nativeRestart_output_bad_branch_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hint : Integrable (fun y : ℝ => |E-abs y|) σ) :
    (σ.prod μ) (nativeRestartFavorableSet X E)ᶜ ≤
      ENNReal.ofReal (80*(∫ y, |E-abs y| ∂σ)/E +
        1600*(∫ x, nativeRestartMean X μ E x ∂σ)/E^2) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hM0 : 0 ≤ ∫ y, |E-abs y| ∂σ := integral_nonneg fun y => abs_nonneg _
  have hC0 : 0 ≤ ∫ x, nativeRestartMean X μ E x ∂σ := by
    have := one_le_stationary_mean hX hi hG hE (π := σ)
    linarith
  have h1 := measure_margin_gt_le_of_moment hE hint (nativeRestartMarginPos_le_abs E)
  have h2 := measure_margin_gt_le_of_moment hE hint (nativeRestartExcess_le_abs E)
  refine (measure_prod_nativeRestart_bad_branch hX hi hG hE).trans ?_
  have hsq : (∫ x, nativeRestartMean X μ E x ∂σ)/(E/40)^2 =
      1600*(∫ x, nativeRestartMean X μ E x ∂σ)/E^2 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hsq]
  calc σ {y : ℝ | E/40 < nativeRestartMarginPos E y} +
        σ {y : ℝ | E/40 < nativeRestartExcess E y} +
        ENNReal.ofReal (1600*(∫ x, nativeRestartMean X μ E x ∂σ)/E^2)
      ≤ ENNReal.ofReal (40*(∫ y, |E-abs y| ∂σ)/E) + ENNReal.ofReal (40*(∫ y, |E-abs y| ∂σ)/E) +
        ENNReal.ofReal (1600*(∫ x, nativeRestartMean X μ E x ∂σ)/E^2) :=
      add_le_add (add_le_add h1 h2) le_rfl
    _ = ENNReal.ofReal (80*(∫ y, |E-abs y| ∂σ)/E +
        1600*(∫ x, nativeRestartMean X μ E x ∂σ)/E^2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-! ### The integer-grid tail split of the output negative margin -/

theorem nativeRestart_output_excess_tail_split [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryMarginThreshold ≤ E)
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {β : ℝ}
    (hβ : (σ.prod μ) (nativeRestartFavorableSet X E)ᶜ ≤ ENNReal.ofReal β)
    {n₀ : ℕ} (hn0pos : 1 ≤ n₀) (hn0ge : 8*Real.log E ≤ (n₀ : ℝ)) (n : ℕ) :
    (nativeRestartKernel X μ E ∘ₘ σ) {y | (n : ℝ) < nativeRestartExcess E y} ≤
      ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) +
        (if n < n₀ then ENNReal.ofReal β else 0) +
        (if n < n₀ then 0 else
          ENNReal.ofReal (2*(∫ x, nativeRestartMean X μ E x ∂σ)*Real.exp 1*(1/E^2)*
            Real.exp (-(n : ℝ)))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hE
  have hEpos : (0 : ℝ) < E := by linarith
  have hn0R : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn0pos
  have hlogexp : Real.exp (-(2*Real.log E)) = 1/E^2 := by
    have hEe : Real.exp (Real.log E) = E := Real.exp_log hEpos
    rw [Real.exp_neg, two_mul, Real.exp_add, hEe, one_div]
    congr 1
    ring
  have hexpn0 : Real.exp (-(n₀ : ℝ)^2/4) ≤ 1/E^2 := by
    rw [← hlogexp]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hn0' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hn : n < n₀
  · rw [if_pos hn, if_pos hn, add_zero]
    refine (nativeRestart_output_excess_tail_refined hX hi hG hEpos hn0').trans ?_
    exact add_le_add (ENNReal.ofReal_le_ofReal (exp_neg_sq_half_le n)) hβ
  · rw [if_neg hn, if_neg hn, add_zero]
    refine le_trans ?_ le_add_self
    refine (nativeRestart_output_excess_tail_raw hX hi hG hEpos hn0').trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hC0 : 0 ≤ ∫ x, nativeRestartMean X μ E x ∂σ := by
      have := one_le_stationary_mean hX hi hG hEpos (π := σ)
      linarith
    have hdom := exp_neg_sq_half_le_of_ge (le_of_not_gt hn)
    have hstep : Real.exp (-(n : ℝ)^2/2) ≤ Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ)) := by
      refine hdom.trans ?_
      have h1 : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
      have h2 : 0 ≤ Real.exp (-(n : ℝ)) := (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left hexpn0 h1
      nlinarith
    nlinarith [Real.exp_pos (-(n : ℝ)), Real.exp_pos (-(n : ℝ)^2/2)]

/-! ### Summing the grid tails -/

/-- The abstract `k`-th moment bound from an integer-grid tail split of the form
`e^{1/2} e^{-n} + β 𝟙_{n < n₀} + c e^{-n} 𝟙_{n ≥ n₀}`. -/
theorem lintegral_ofReal_pow_le_of_tail_split {S : Type*} [MeasurableSpace S] (ρ : Measure S)
    {M : S → ℝ} (hM : Measurable M) (hnn : ∀ s, 0 ≤ M s) {k : ℕ} (hk : 1 ≤ k)
    {n₀ : ℕ} {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hT : ∀ n : ℕ, ρ {s | (n : ℝ) < M s} ≤
      ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) +
        (if n < n₀ then ENNReal.ofReal β else 0) +
        (if n < n₀ then 0 else ENNReal.ofReal (c*Real.exp (-(n : ℝ))))) :
    (∫⁻ s, ENNReal.ofReal (M s^k) ∂ρ) ≤
      ENNReal.ofReal (Real.exp (1/2)*expTailMomentSum 1 k + (n₀ : ℝ)^(k+1)*β +
        c*expTailMomentSum 1 k) := by
  have hSum1 : ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
      ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) =
      ENNReal.ofReal (Real.exp (1/2)*expTailMomentSum 1 k) := by
    rw [← tsum_ofReal_pow_exp_neg (K := Real.exp (1/2)) (Real.exp_pos _).le k]
    refine tsum_congr fun n => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hSum3 : ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
      (if n < n₀ then 0 else ENNReal.ofReal (c*Real.exp (-(n : ℝ)))) ≤
      ENNReal.ofReal (c*expTailMomentSum 1 k) := by
    rw [← tsum_ofReal_pow_exp_neg (K := c) hc k]
    refine ENNReal.tsum_le_tsum fun n => ?_
    by_cases hn : n < n₀
    · rw [if_pos hn, mul_zero]
      exact zero_le
    · rw [if_neg hn, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      apply le_of_eq
      ring
  have hSum2 : ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
      (if n < n₀ then ENNReal.ofReal β else 0) ≤
      ENNReal.ofReal ((n₀ : ℝ)^(k+1)*β) := by
    have hterm : ∀ n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
        (if n < n₀ then ENNReal.ofReal β else 0) ≤
        (if n < n₀ then ENNReal.ofReal ((n₀ : ℝ)^k*β) else 0) := by
      intro n
      by_cases hn : n < n₀
      · rw [if_pos hn, if_pos hn, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : ((n : ℝ)+1) ≤ (n₀ : ℝ) := by exact_mod_cast hn
        have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ)+1) h1 k
        exact mul_le_mul_of_nonneg_right hpow hβ
      · rw [if_neg hn, if_neg hn, mul_zero]
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [tsum_eq_sum (s := Finset.range n₀) (fun b hb => by
      rw [if_neg (by simpa using hb)])]
    rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast n₀, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_succ]
    apply le_of_eq
    ring
  calc
    (∫⁻ s, ENNReal.ofReal (M s^k) ∂ρ)
        ≤ ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*ρ {s | (n : ℝ) < M s} :=
      lintegral_ofReal_pow_le_tsum ρ hM hnn hk
    _ ≤ ∑' n : ℕ, (ENNReal.ofReal (((n : ℝ)+1)^k)*
            ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) +
          ENNReal.ofReal (((n : ℝ)+1)^k)*
            (if n < n₀ then ENNReal.ofReal β else 0) +
          ENNReal.ofReal (((n : ℝ)+1)^k)*
            (if n < n₀ then 0 else ENNReal.ofReal (c*Real.exp (-(n : ℝ))))) := by
      refine ENNReal.tsum_le_tsum fun n => ?_
      have hstep := mul_le_mul' (le_refl (ENNReal.ofReal (((n : ℝ)+1)^k))) (hT n)
      rw [mul_add, mul_add] at hstep
      exact hstep
    _ = (∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
            ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ)))) +
          (∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
            (if n < n₀ then ENNReal.ofReal β else 0)) +
          (∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
            (if n < n₀ then 0 else ENNReal.ofReal (c*Real.exp (-(n : ℝ))))) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal (Real.exp (1/2)*expTailMomentSum 1 k) +
          ENNReal.ofReal ((n₀ : ℝ)^(k+1)*β) +
          ENNReal.ofReal (c*expTailMomentSum 1 k) := by
      rw [hSum1]
      exact add_le_add (add_le_add le_rfl hSum2) hSum3
    _ = ENNReal.ofReal (Real.exp (1/2)*expTailMomentSum 1 k + (n₀ : ℝ)^(k+1)*β +
          c*expTailMomentSum 1 k) := by
      have hn1 : (0 : ℝ) ≤ Real.exp (1/2)*expTailMomentSum 1 k := by
        have := expTailMomentSum_nonneg 1 k
        positivity
      have hn2 : (0 : ℝ) ≤ (n₀ : ℝ)^(k+1)*β := by positivity
      have hn3 : (0 : ℝ) ≤ c*expTailMomentSum 1 k := by
        have := expTailMomentSum_nonneg 1 k
        positivity
      rw [← ENNReal.ofReal_add hn1 hn2, ← ENNReal.ofReal_add (by linarith) hn3]

/-! ### The output negative-margin moment -/

/-- The `k`-th output negative-margin moment bound, depending only on the
order `k` and on a bound `M₁` for the input first absolute margin moment. -/
def transientExcessMomentBound (k : ℕ) (M₁ : ℝ) : ℝ :=
  Real.exp (1/2)*expTailMomentSum 1 k
    + (10 : ℝ)^(k+1)*(((k : ℝ)+2))^(k+2)*(80*M₁+3200*frozenUniformMeanConstant*(1+M₁))
    + 4*frozenUniformMeanConstant*(1+M₁)*Real.exp 1*expTailMomentSum 1 k

theorem transientExcessMomentBound_nonneg (k : ℕ) {M₁ : ℝ} (hM : 0 ≤ M₁) :
    0 ≤ transientExcessMomentBound k M₁ := by
  have h1 := expTailMomentSum_nonneg 1 k
  have h2 := frozenUniformMeanConstant_pos
  unfold transientExcessMomentBound
  positivity

/-- The input mean segment length is at most `2K(1+M₁) E log E`. -/
theorem nativeRestart_mean_le_of_margin_moment [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hEone : Real.exp 1 ≤ E)
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hint : Integrable (fun y : ℝ => |E-abs y|) σ) {M₁ : ℝ}
    (hM1 : (∫ y, |E-abs y| ∂σ) ≤ M₁) :
    (∫ x, nativeRestartMean X μ E x ∂σ) ≤
      2*frozenUniformMeanConstant*(1+M₁)*E*Real.log E := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE1 : (1 : ℝ) ≤ E := by
    have : (1 : ℝ) ≤ Real.exp 1 := by norm_num
    linarith
  have hEpos : (0 : ℝ) < E := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log E := (Real.le_log_iff_exp_le hEpos).mpr hEone
  have hlogeE : Real.log (Real.exp 1*E) = 1+Real.log E := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hEpos), Real.log_exp]
  have hK := frozenUniformMeanConstant_pos
  have hmean := stationary_mean_le_marginPos hX hi hG hE1 (π := σ)
  rw [hlogeE] at hmean
  have hmp_int : Integrable (nativeRestartMarginPos E) σ :=
    hint.mono' (measurable_nativeRestartMarginPos E).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact nativeRestartMarginPos_le_abs E y)
  have hP : (∫ x, nativeRestartMarginPos E x ∂σ) ≤ M₁ :=
    (integral_mono hmp_int hint (nativeRestartMarginPos_le_abs E)).trans hM1
  have hP0 : 0 ≤ ∫ x, nativeRestartMarginPos E x ∂σ :=
    integral_nonneg fun x => le_max_right _ _
  have hM0 : 0 ≤ M₁ := hP0.trans hP
  calc (∫ x, nativeRestartMean X μ E x ∂σ)
      ≤ frozenUniformMeanConstant*E*(1+Real.log E)*(1+∫ x, nativeRestartMarginPos E x ∂σ) :=
        hmean
    _ ≤ frozenUniformMeanConstant*E*(2*Real.log E)*(1+M₁) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        · linarith
        · linarith
        · positivity
    _ = 2*frozenUniformMeanConstant*(1+M₁)*E*Real.log E := by ring

theorem nativeRestart_output_excess_pow_lintegral_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {σ : Measure ℝ} [IsProbabilityMeasure σ]
    (hint : Integrable (fun y : ℝ => |E-abs y|) σ) {M₁ : ℝ}
    (hM1 : (∫ y, |E-abs y| ∂σ) ≤ M₁) {k : ℕ} (hk : 1 ≤ k) :
    (∫⁻ y, ENNReal.ofReal (nativeRestartExcess E y^k) ∂(nativeRestartKernel X μ E ∘ₘ σ)) ≤
      ENNReal.ofReal (transientExcessMomentBound k M₁) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEone : Real.exp 1 ≤ E :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hE2 : (0 : ℝ) < E^2 := by positivity
  set K := frozenUniformMeanConstant with hKdef
  have hKpos : 0 < K := frozenUniformMeanConstant_pos
  set L := Real.log E with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    exact (Real.le_log_iff_exp_le hEpos).mpr hEone
  have hLE : L ≤ E := by
    have hEe : Real.exp L = E := by rw [hLdef, Real.exp_log hEpos]
    have := Real.add_one_le_exp L
    linarith [hEe ▸ this]
  set C := ∫ x, nativeRestartMean X μ E x ∂σ with hCdef
  have hC1 : 1 ≤ C := one_le_stationary_mean hX hi hG hEpos
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hM0 : 0 ≤ M₁ := (integral_nonneg fun y => abs_nonneg _).trans hM1
  have hCscale : C ≤ 2*K*(1+M₁)*E*L := by
    rw [hKdef, hCdef, hLdef]
    exact nativeRestart_mean_le_of_margin_moment hX hi hG hEone hint hM1
  set n₀ : ℕ := ⌈8*L⌉₊+1 with hn0def
  have hn0pos : 1 ≤ n₀ := by omega
  have hn0ge : 8*L ≤ (n₀ : ℝ) := by
    have h := Nat.le_ceil (8*L)
    have h1 : ((⌈8*L⌉₊ : ℕ) : ℝ) ≤ (n₀ : ℝ) := by
      rw [hn0def]
      push_cast
      linarith
    linarith
  have hn0le : ((n₀ : ℕ) : ℝ) ≤ 10*L := by
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 8*L)
    rw [hn0def]
    push_cast
    linarith
  -- the complementary branch
  set β : ℝ := 80*(∫ y, |E-abs y| ∂σ)/E + 1600*C/E^2 with hβdef
  have hI0 : 0 ≤ ∫ y, |E-abs y| ∂σ := integral_nonneg fun y => abs_nonneg _
  have hβ0 : 0 ≤ β := by
    positivity
  have hβle : (σ.prod μ) (nativeRestartFavorableSet X E)ᶜ ≤ ENNReal.ofReal β :=
    nativeRestart_output_bad_branch_le hX hi hG hEpos hint
  set c : ℝ := 2*C*Real.exp 1*(1/E^2) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hT := nativeRestart_output_excess_tail_split hX hi hG hEm hβle hn0pos
    (by rw [← hLdef]; exact hn0ge)
  have hsplit : ∀ n : ℕ,
      (nativeRestartKernel X μ E ∘ₘ σ) {y | (n : ℝ) < nativeRestartExcess E y} ≤
        ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) +
          (if n < n₀ then ENNReal.ofReal β else 0) +
          (if n < n₀ then 0 else ENNReal.ofReal (c*Real.exp (-(n : ℝ)))) := by
    intro n
    have h := hT n
    simpa [hcdef, hCdef] using h
  refine (lintegral_ofReal_pow_le_of_tail_split _ (measurable_nativeRestartExcess E)
    (fun y => le_max_right _ _) hk hβ0 hc0 hsplit).trans (ENNReal.ofReal_le_ofReal ?_)
  -- numerical comparison of the three terms
  have hS0 : 0 ≤ expTailMomentSum 1 k := expTailMomentSum_nonneg 1 k
  have hLpow : L^(k+2) ≤ (((k : ℝ)+2))^(k+2)*E := by
    have h := stationary_log_pow_le (m := k+2) (by omega) hE1
    rw [← hLdef] at h
    have hcast : (((k+2 : ℕ)) : ℝ) = (k : ℝ)+2 := by push_cast; ring
    rw [hcast] at h
    exact h
  have hβbound : β ≤ (80*M₁+3200*K*(1+M₁))*L/E := by
    rw [hβdef]
    have h1 : 80*(∫ y, |E-abs y| ∂σ)/E ≤ 80*M₁*L/E := by
      rw [div_le_div_iff_of_pos_right hEpos]
      nlinarith
    have h2 : 1600*C/E^2 ≤ 3200*K*(1+M₁)*L/E := by
      rw [div_le_div_iff₀ hE2 hEpos]
      nlinarith
    calc 80*(∫ y, |E-abs y| ∂σ)/E + 1600*C/E^2 ≤ 80*M₁*L/E + 3200*K*(1+M₁)*L/E :=
          add_le_add h1 h2
      _ = (80*M₁+3200*K*(1+M₁))*L/E := by ring
  have hbranch : (n₀ : ℝ)^(k+1)*β ≤
      (10 : ℝ)^(k+1)*(((k : ℝ)+2))^(k+2)*(80*M₁+3200*K*(1+M₁)) := by
    have hA0 : (0 : ℝ) ≤ 80*M₁+3200*K*(1+M₁) := by positivity
    have h1 : (n₀ : ℝ)^(k+1) ≤ (10*L)^(k+1) :=
      pow_le_pow_left₀ (by positivity) hn0le (k+1)
    have h3 : (n₀ : ℝ)^(k+1)*β ≤ (10*L)^(k+1)*((80*M₁+3200*K*(1+M₁))*L/E) :=
      mul_le_mul h1 hβbound hβ0 (by positivity)
    have h4 : (10*L)^(k+1)*((80*M₁+3200*K*(1+M₁))*L/E) =
        (10 : ℝ)^(k+1)*(80*M₁+3200*K*(1+M₁))*(L^(k+2)/E) := by
      rw [mul_pow, pow_succ L (k+1), pow_succ L k]
      field_simp
    have h5 : L^(k+2)/E ≤ (((k : ℝ)+2))^(k+2) := by
      rw [div_le_iff₀ hEpos]
      linarith [hLpow]
    calc (n₀ : ℝ)^(k+1)*β ≤ (10*L)^(k+1)*((80*M₁+3200*K*(1+M₁))*L/E) := h3
      _ = (10 : ℝ)^(k+1)*(80*M₁+3200*K*(1+M₁))*(L^(k+2)/E) := h4
      _ ≤ (10 : ℝ)^(k+1)*(80*M₁+3200*K*(1+M₁))*(((k : ℝ)+2))^(k+2) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = (10 : ℝ)^(k+1)*(((k : ℝ)+2))^(k+2)*(80*M₁+3200*K*(1+M₁)) := by ring
  have hthird : c*expTailMomentSum 1 k ≤ 4*K*(1+M₁)*Real.exp 1*expTailMomentSum 1 k := by
    have hCC : c ≤ 4*K*(1+M₁)*Real.exp 1 := by
      rw [hcdef]
      have hstep : C*(1/E^2) ≤ 2*K*(1+M₁) := by
        rw [mul_one_div, div_le_iff₀ hE2]
        nlinarith
      nlinarith [Real.exp_pos (1 : ℝ)]
    exact mul_le_mul_of_nonneg_right hCC hS0
  rw [transientExcessMomentBound, ← hKdef]
  linarith

/-! ### The output positive margin -/

theorem measurable_nativeRestartMarginPos_pow (E : ℝ) (k : ℕ) :
    Measurable (fun y : ℝ => nativeRestartMarginPos E y^k) :=
  (measurable_nativeRestartMarginPos E).pow_const k

/-- The envelope moment constant `G_k = E[G^k]` bound. -/
def transientEnvelopeMomentBound (k : ℕ) : ℝ :=
  nativeGaussianEnvelopeExpTailConstant*expTailMomentSum 1 k

theorem transientEnvelopeMomentBound_nonneg (k : ℕ) : 0 ≤ transientEnvelopeMomentBound k :=
  mul_nonneg nativeGaussianEnvelopeExpTailConstant_nonneg (expTailMomentSum_nonneg _ _)

/-- `eq:stationarymarginpositive` integrated against an arbitrary input law:
the output positive margin's `k`-th moment is controlled by the input negative
margin's `k`-th moment and the envelope moment. -/
theorem nativeRestart_output_marginPos_pow_lintegral_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {k : ℕ}
    (hint : Integrable (fun y : ℝ => nativeRestartExcess E y^k) σ) :
    (∫⁻ y, ENNReal.ofReal (nativeRestartMarginPos E y^k) ∂(nativeRestartKernel X μ E ∘ₘ σ)) ≤
      ENNReal.ofReal ((25 : ℝ)^k*(1+(∫ y, nativeRestartExcess E y^k ∂σ)+
        transientEnvelopeMomentBound k)) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hP : IsMarkovKernel (nativeRestartKernel X μ E) := nativeRestartKernel_isMarkov hX E
  have hf : Measurable (fun y : ℝ => ENNReal.ofReal (nativeRestartMarginPos E y^k)) :=
    (measurable_nativeRestartMarginPos_pow E k).ennreal_ofReal
  have henv_int : Integrable (fun ω => nativeGaussianEnvelope X ω^k) μ :=
    nativeGaussianEnvelope_integrable_pow hX hi hG k
  have henv_le : (∫ ω, nativeGaussianEnvelope X ω^k ∂μ) ≤ transientEnvelopeMomentBound k :=
    nativeGaussianEnvelope_integral_pow_le hX hi hG k
  have henv0 : 0 ≤ ∫ ω, nativeGaussianEnvelope X ω^k ∂μ :=
    integral_nonneg fun ω => pow_nonneg (nativeGaussianEnvelope_nonneg X ω) k
  have hexc0 : ∀ y, 0 ≤ nativeRestartExcess E y^k := fun y => pow_nonneg (le_max_right _ _) k
  -- the inner (fixed-state) bound
  have hinner : ∀ x : ℝ,
      (∫⁻ y, ENNReal.ofReal (nativeRestartMarginPos E y^k) ∂(nativeRestartKernel X μ E x)) ≤
        ENNReal.ofReal ((25 : ℝ)^k*(1+nativeRestartExcess E x^k+
          ∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) := by
    intro x
    have hnext : Measurable (fun ω => nativeRestartNext X E x ω) :=
      (nativeRestartNext_measurable X hX E).comp
        ((measurable_const (a := x)).prodMk measurable_id)
    rw [nativeRestartKernel_eq_map hX E x, lintegral_map hf hnext]
    have hbound : ∀ᵐ ω ∂μ,
        ENNReal.ofReal (nativeRestartMarginPos E (nativeRestartNext X E x ω)^k) ≤
          ENNReal.ofReal ((25 : ℝ)^k*(1+nativeRestartExcess E x^k+nativeGaussianEnvelope X ω^k)) := by
      filter_upwards [nativeRestartLength_ae_finite hX hi hG hE x,
        nativeGaussianEnvelope_bounds_ae hX hi hG] with ω hfin hW
      exact ENNReal.ofReal_le_ofReal (nativeRestart_marginPos_pow_next_le X hE.le x ω hW hfin k)
    refine (lintegral_mono_ae hbound).trans (le_of_eq ?_)
    have hg_int : Integrable
        (fun ω => (25 : ℝ)^k*(1+nativeRestartExcess E x^k+nativeGaussianEnvelope X ω^k)) μ :=
      (((integrable_const _).add henv_int).const_mul _)
    have hg_nn : 0 ≤ᵐ[μ]
        (fun ω => (25 : ℝ)^k*(1+nativeRestartExcess E x^k+nativeGaussianEnvelope X ω^k)) :=
      ae_of_all _ fun ω => by
        have := hexc0 x
        have := pow_nonneg (nativeGaussianEnvelope_nonneg X ω) k
        positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hg_int hg_nn]
    congr 1
    rw [integral_const_mul, integral_add (integrable_const _) henv_int, integral_const]
    simp
  -- integrate the inner bound against the input law
  have hmeas_inner : Measurable fun x : ℝ =>
      ∫⁻ y, ENNReal.ofReal (nativeRestartMarginPos E y^k) ∂(nativeRestartKernel X μ E x) :=
    hf.lintegral_kernel
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal (nativeRestartMarginPos E y^k)
          ∂(nativeRestartKernel X μ E x) ∂σ)
      ≤ ∫⁻ x, ENNReal.ofReal ((25 : ℝ)^k*(1+nativeRestartExcess E x^k+
          ∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) ∂σ := lintegral_mono hinner
    _ = ENNReal.ofReal ((25 : ℝ)^k*(1+(∫ y, nativeRestartExcess E y^k ∂σ)+
          ∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) := by
        have hg_int : Integrable (fun x : ℝ => (25 : ℝ)^k*(1+nativeRestartExcess E x^k+
            ∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) σ :=
          (((integrable_const _).add hint).add (integrable_const _)).const_mul _
        have hg_nn : 0 ≤ᵐ[σ] (fun x : ℝ => (25 : ℝ)^k*(1+nativeRestartExcess E x^k+
            ∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) :=
          ae_of_all _ fun x => by
            have := hexc0 x
            positivity
        rw [← ofReal_integral_eq_lintegral_ofReal hg_int hg_nn]
        congr 1
        rw [integral_const_mul]
        congr 1
        have h1 : Integrable (fun x : ℝ => 1+nativeRestartExcess E x^k) σ :=
          (integrable_const _).add hint
        rw [integral_add h1 (integrable_const _), integral_add (integrable_const _) hint,
          integral_const, integral_const]
        simp
    _ ≤ ENNReal.ofReal ((25 : ℝ)^k*(1+(∫ y, nativeRestartExcess E y^k ∂σ)+
          transientEnvelopeMomentBound k)) := by
        apply ENNReal.ofReal_le_ofReal
        have : 0 ≤ ∫ y, nativeRestartExcess E y^k ∂σ := integral_nonneg fun y => hexc0 y
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 25) k]

/-! ### One transition -/

/-- The one-step moment bound: order `k`, from an input first-moment bound `M₁`
and an input `k`-th moment bound `Mk`. -/
def transientStepBound (k : ℕ) (M₁ Mk : ℝ) : ℝ :=
  (25 : ℝ)^k*(1+Mk+transientEnvelopeMomentBound k) + transientExcessMomentBound k M₁

theorem transientStepBound_nonneg (k : ℕ) {M₁ Mk : ℝ} (h1 : 0 ≤ M₁) (hk : 0 ≤ Mk) :
    0 ≤ transientStepBound k M₁ Mk := by
  have := transientEnvelopeMomentBound_nonneg k
  have := transientExcessMomentBound_nonneg k h1
  unfold transientStepBound
  positivity

theorem integrable_abs_of_pow {σ : Measure ℝ} [IsProbabilityMeasure σ] {E : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hint : Integrable (fun y : ℝ => |E-abs y|^k) σ) :
    Integrable (fun y : ℝ => |E-abs y|) σ := by
  refine ((integrable_const (1 : ℝ)).add hint).mono'
    ((measurable_const.sub measurable_id.abs).abs).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_abs, Pi.add_apply]
  show |E-abs y| ≤ 1 + |E-abs y|^k
  by_cases h : |E-abs y| ≤ 1
  · linarith [pow_nonneg (abs_nonneg (E-|y|)) k]
  · have h' := not_le.mp h
    have := le_self_pow₀ h'.le (by omega : k ≠ 0)
    linarith

/-- **One transition of the moment propagation.**  For any input probability law
with a bounded `k`-th absolute margin moment, the output law has a bounded
`k`-th absolute margin moment, with a bound depending only on `k`, the input
first-moment bound and the input `k`-th moment bound. -/
theorem nativeRestart_output_margin_pow_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {σ : Measure ℝ} [IsProbabilityMeasure σ] {k : ℕ} (hk : 1 ≤ k)
    {M₁ Mk : ℝ} (hint1 : Integrable (fun y : ℝ => |E-abs y|) σ)
    (hM1 : (∫ y, |E-abs y| ∂σ) ≤ M₁)
    (hintk : Integrable (fun y : ℝ => |E-abs y|^k) σ)
    (hMk : (∫ y, |E-abs y|^k ∂σ) ≤ Mk) :
    Integrable (fun y : ℝ => |E-abs y|^k) (nativeRestartKernel X μ E ∘ₘ σ) ∧
      (∫ y, |E-abs y|^k ∂(nativeRestartKernel X μ E ∘ₘ σ)) ≤ transientStepBound k M₁ Mk := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  set σ' := nativeRestartKernel X μ E ∘ₘ σ with hσ'
  have : IsProbabilityMeasure σ' := nativeRestart_output_isProbability hX E
  have hM0 : 0 ≤ M₁ := (integral_nonneg fun y => abs_nonneg _).trans hM1
  -- input negative-margin moment
  have hexc_meas : Measurable (fun y : ℝ => nativeRestartExcess E y^k) :=
    measurable_nativeRestartExcess_pow E k
  have hexc_int : Integrable (fun y : ℝ => nativeRestartExcess E y^k) σ :=
    hintk.mono' hexc_meas.aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right _ _) k)]
      exact pow_le_pow_left₀ (le_max_right _ _) (nativeRestartExcess_le_abs E y) k)
  have hexc_le : (∫ y, nativeRestartExcess E y^k ∂σ) ≤ Mk :=
    (integral_mono hexc_int hintk fun y =>
      pow_le_pow_left₀ (le_max_right _ _) (nativeRestartExcess_le_abs E y) k).trans hMk
  -- output pieces
  have hmp_nn : ∀ y : ℝ, 0 ≤ nativeRestartMarginPos E y^k := fun y => pow_nonneg (le_max_right _ _) k
  have hex_nn : ∀ y : ℝ, 0 ≤ nativeRestartExcess E y^k := fun y => pow_nonneg (le_max_right _ _) k
  have hmp_upper : ∀ y : ℝ, nativeRestartMarginPos E y^k ≤ E^k := fun y =>
    pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith [abs_nonneg y]) hEpos.le) k
  have hmp_int : Integrable (fun y : ℝ => nativeRestartMarginPos E y^k) σ' :=
    Doeblin.integrable_bounded_reward σ' (measurable_nativeRestartMarginPos_pow E k) hmp_nn hmp_upper
  have hmp_lint := nativeRestart_output_marginPos_pow_lintegral_le hX hi hG hEpos (σ := σ) hexc_int
  have hex_lint := nativeRestart_output_excess_pow_lintegral_le hX hi hG hE hint1 hM1 hk
  rw [← hσ'] at hmp_lint hex_lint
  have hex_int : Integrable (fun y : ℝ => nativeRestartExcess E y^k) σ' := by
    refine ⟨hexc_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hex_nn)]
    exact lt_of_le_of_lt hex_lint ENNReal.ofReal_lt_top
  have hmp_le : (∫ y, nativeRestartMarginPos E y^k ∂σ') ≤
      (25 : ℝ)^k*(1+Mk+transientEnvelopeMomentBound k) := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hmp_nn)
      (measurable_nativeRestartMarginPos_pow E k).aestronglyMeasurable]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmp_lint
    have hnn : 0 ≤ (25 : ℝ)^k*(1+(∫ y, nativeRestartExcess E y^k ∂σ)+
        transientEnvelopeMomentBound k) := by
      have : 0 ≤ ∫ y, nativeRestartExcess E y^k ∂σ := integral_nonneg fun y => hex_nn y
      have := transientEnvelopeMomentBound_nonneg k
      positivity
    rw [ENNReal.toReal_ofReal hnn] at h
    refine h.trans ?_
    have := transientEnvelopeMomentBound_nonneg k
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 25) k]
  have hex_le : (∫ y, nativeRestartExcess E y^k ∂σ') ≤ transientExcessMomentBound k M₁ := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hex_nn) hexc_meas.aestronglyMeasurable]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hex_lint
    rwa [ENNReal.toReal_ofReal (transientExcessMomentBound_nonneg k hM0)] at h
  have hsplit : ∀ y : ℝ, |E-abs y|^k = nativeRestartMarginPos E y^k + nativeRestartExcess E y^k :=
    fun y => abs_margin_pow_eq E y hk
  have hint_out : Integrable (fun y : ℝ => |E-abs y|^k) σ' :=
    (hmp_int.add hex_int).congr (ae_of_all _ fun y => (hsplit y).symm)
  refine ⟨hint_out, ?_⟩
  have heq : (∫ y, |E-abs y|^k ∂σ') =
      (∫ y, nativeRestartMarginPos E y^k ∂σ') + ∫ y, nativeRestartExcess E y^k ∂σ' := by
    rw [← integral_add hmp_int hex_int]
    exact integral_congr_ae (ae_of_all _ hsplit)
  rw [heq, transientStepBound]
  exact add_le_add hmp_le hex_le

/-! ### Lemma G.1 as the base case -/

theorem integrable_nativeFirstMargin_pow
    (hZ : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) (k : ℕ) :
    Integrable (fun ω => |nativeFirstMargin X E ω|^k) μ := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hE0 : 0 ≤ E := by linarith
  set D : Ω → ℝ := fun ω => nativeFirstSlopeEnvelope X ω+|nativeFirstSelectedIncrement X E ω|
    with hD
  have hDm : Measurable D :=
    (nativeFirstSlopeEnvelope_measurable hZ).add
      (nativeFirstSelectedIncrement_measurable hZ hE0).abs
  have hDnn : ∀ᵐ ω ∂μ, 0 ≤ D ω := Eventually.of_forall fun ω => by
    have := nativeFirstSlopeEnvelope_nonneg' X ω
    have := abs_nonneg (nativeFirstSelectedIncrement X E ω)
    simp only [hD]; linarith
  have htail := nativeFirstMarginDominant_tail hZ hi hG hE
  have hint : Integrable (fun ω => D ω^k) μ :=
    integrable_pow_of_expTail hDm hDnn nativeFirstMarginTailConstant_pos.le
      (by norm_num : (0 : ℝ) < 1/51200) htail k
  have hmm := nativeFirstMargin_measurable hZ E
  have hdom : ∀ᵐ ω ∂μ, ‖|nativeFirstMargin X E ω|^k‖ ≤ D ω^k := by
    filter_upwards [nativeFirstMargin_abs_le_ae hZ hi hG hE0] with ω hω
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (abs_nonneg _) hω k
  exact hint.mono' (hmm.abs.pow_const k).aestronglyMeasurable hdom

/-- Lemma G.1 read on the state law after the first segment. -/
theorem nativeTransientLaw_one_margin_pow_le
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) (k : ℕ) :
    Integrable (fun y : ℝ => |E-abs y|^k) (nativeTransientLaw X μ E 1) ∧
      (∫ y, |E-abs y|^k ∂(nativeTransientLaw X μ E 1)) ≤ nativeFirstMarginMomentBound k := by
  have hEpos : 0 < E := by linarith
  have hnext : Measurable (nativeFirstNext X E) :=
    (nativeRestartNext_measurable (fun k => X (1+k)) (fun k => hX (1+k)) E).comp
      ((hX 0).prodMk measurable_id)
  have hf : Measurable (fun y : ℝ => |E-abs y|^k) :=
    ((measurable_const.sub measurable_id.abs).abs).pow_const k
  rw [nativeTransientLaw_one hX hi hG hEpos]
  have hcomp : (fun y : ℝ => |E-abs y|^k) ∘ nativeFirstNext X E =
      fun ω => |nativeFirstMargin X E ω|^k := by
    funext ω
    rfl
  constructor
  · rw [integrable_map_measure hf.aestronglyMeasurable hnext.aemeasurable, hcomp]
    exact integrable_nativeFirstMargin_pow hX hi hG hE k
  · rw [integral_map hnext.aemeasurable hf.aestronglyMeasurable]
    have := integral_nativeFirstMargin_pow_le hX hi hG hE k
    simpa [nativeFirstMargin] using this

/-! ### `eq:transient-fullmoments` -/

/-- The explicit moment bound for the state law after `j+1` segments, order `k`. -/
def transientMarginMomentBound : ℕ → ℕ → ℝ
  | 0, k => nativeFirstMarginMomentBound k
  | j+1, k => transientStepBound k (transientMarginMomentBound j 1) (transientMarginMomentBound j k)

theorem transientMarginMomentBound_nonneg (j k : ℕ) : 0 ≤ transientMarginMomentBound j k := by
  induction j generalizing k with
  | zero => exact nativeFirstMarginMomentBound_nonneg k
  | succ j ih =>
    exact transientStepBound_nonneg k (ih 1) (ih k)

/-- **`eq:transient-fullmoments`.**  Every fixed absolute moment of the actual
margin after any fixed number `j+1 ≥ 1` of segments is bounded uniformly in the
budget, for all budgets above the Theorem 4.2 threshold. -/
theorem nativeTransientLaw_margin_pow_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (j : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun y : ℝ => |E-abs y|^k) (nativeTransientLaw X μ E (j+1)) ∧
      (∫ y, |E-abs y|^k ∂(nativeTransientLaw X μ E (j+1))) ≤ transientMarginMomentBound j k := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  have hE2 : 1 ≤ 2*E := by linarith
  induction j generalizing k with
  | zero => exact nativeTransientLaw_one_margin_pow_le hX hi hG hE2 k
  | succ j ih =>
    have : IsProbabilityMeasure (nativeTransientLaw X μ E (j+1)) :=
      nativeTransientLaw_isProbability hX E (j+1)
    obtain ⟨hint1, hM1⟩ := ih (k := 1) le_rfl
    obtain ⟨hintk, hMk⟩ := ih hk
    simp only [pow_one] at hint1 hM1
    rw [nativeTransientLaw_succ hX hi hG hEpos (j+1)]
    exact nativeRestart_output_margin_pow_le hX hi hG hE hk hint1 hM1 hintk hMk

end SwingRepair
