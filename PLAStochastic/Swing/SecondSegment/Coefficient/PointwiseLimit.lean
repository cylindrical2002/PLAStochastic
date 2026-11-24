import PLAStochastic.Swing.SecondSegment.Coefficient.Kernel
import PLAStochastic.Swing.FrozenCarry.NegativeCarry.LogBound
import PLAStochastic.ForMathlib.MeasureTheory.Integral.GeometricTailUniformIntegrability
import PLAStochastic.ForMathlib.Probability.Moments.IntegerGridExpTail

/-! # Mean convergence of the frozen negative-carry length at a fixed margin

`second-coefficient.md`, C2.3–C2.4 at one fixed negative margin `r = -c`.
Beyond the linear cutoff `n ≥ 4E/c` the frozen prefix has a Gaussian geometric
tail (`frozenPrefixLength_negative_geometric_tail`).  The excess over that cutoff
therefore has a budget-free exponential tail, which bounds the second moment of
`L_E(-c)/E` uniformly in `E ≥ 1`.  Vitali's theorem upgrades the pathwise limit
`L_E(-c)/E → 2/frozenSlopeMagnitude` to convergence of means, and the reflection
identity of `Kernel` identifies the limit as `ℓ(-c)`.  Passing Lemma H.1 to the
limit gives `ℓ(-c) ≤ C(1 + log₊(1/c))` (C2.7).
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

theorem frozenPrefixLengthReal_measurable (hX : ∀ n, Measurable (X n)) (w E : ℝ) :
    Measurable (frozenPrefixLengthReal X w E) :=
  measurable_from_nat.comp ((frozenPrefixLength_measurable hX w E).untopD 0)

omit [MeasurableSpace Ω] in
theorem frozenPrefixLengthReal_nonneg (X : ℕ → Ω → ℝ) (w E : ℝ) (ω : Ω) :
    0 ≤ frozenPrefixLengthReal X w E ω := Nat.cast_nonneg _

/-! ### A budget-free tail for the excess over the linear cutoff -/

/-- The explicit uniform second-moment constant of `L_E(-c)/E`. -/
def frozenNegativeSqBound (c : ℝ) : ℝ :=
  2*(4/c+1)^2 + 2*(2/Real.exp (-(c^2)/8) * expTailMomentSum (c^2/8) 2)

theorem frozenNegativeSqBound_nonneg (c : ℝ) : 0 ≤ frozenNegativeSqBound c := by
  have := expTailMomentSum_nonneg (c^2/8) 2
  have := Real.exp_pos (-(c^2)/8)
  unfold frozenNegativeSqBound
  positivity

/-- The excess `(L_E(-c) - ⌈4E/c⌉)_+` has the tail `(2/q) e^{-(c²/8)k}`. -/
theorem frozenPrefixLength_negative_excess_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c E : ℝ} (hc : 0 < c) (hE : 0 < E) (k : ℕ) :
    μ {ω | (k : ℝ) ≤ max (frozenPrefixLengthReal X (-c) E ω - ⌈4*E/c⌉₊) 0} ≤
      ENNReal.ofReal (2/Real.exp (-(c^2)/8) * Real.exp (-(c^2/8)*(k : ℝ))) := by
  have := hi.isProbabilityMeasure
  set N : ℕ := ⌈4*E/c⌉₊ with hNdef
  set q : ℝ := Real.exp (-(c^2)/8) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg c])
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hNc : 4*E ≤ c*(N : ℝ) := by
    have h := Nat.le_ceil (4*E/c)
    rw [← hNdef] at h
    have := (div_le_iff₀ hc).mp h
    linarith
  cases k with
  | zero =>
    refine prob_le_one.trans (ENNReal.one_le_ofReal.mpr ?_)
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    rw [le_div_iff₀ hq0]
    linarith
  | succ m =>
    have hsub : {ω | ((m+1 : ℕ) : ℝ) ≤ max (frozenPrefixLengthReal X (-c) E ω - N) 0} ⊆
        {ω | ((N+m+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X (-c) E ω} := by
      intro ω hω
      have hω' : ((m+1 : ℕ) : ℝ) ≤ max (frozenPrefixLengthReal X (-c) E ω - N) 0 := hω
      have hpos : (0 : ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
      have hge : ((m+1 : ℕ) : ℝ) ≤ frozenPrefixLengthReal X (-c) E ω - N := by
        rcases le_total (frozenPrefixLengthReal X (-c) E ω - N) 0 with h | h
        · rw [max_eq_right h] at hω'
          linarith
        · rwa [max_eq_left h] at hω'
      have hlt : N+m < (frozenPrefixLength X (-c) E ω).untopD 0 := by
        have h2 : ((N+m+1 : ℕ) : ℝ) ≤ (((frozenPrefixLength X (-c) E ω).untopD 0 : ℕ) : ℝ) := by
          have : frozenPrefixLengthReal X (-c) E ω =
              (((frozenPrefixLength X (-c) E ω).untopD 0 : ℕ) : ℝ) := rfl
          push_cast at hge ⊢
          linarith
        have h3 : N+m+1 ≤ (frozenPrefixLength X (-c) E ω).untopD 0 := by exact_mod_cast h2
        omega
      exact frozenPrefixLength_nat_tail_subset X (-c) E (N+m) hlt
    have hn : 0 < N+m := by omega
    have hcut : 4*E ≤ c*((N+m : ℕ) : ℝ) := by
      have : (N : ℝ) ≤ ((N+m : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N m
      nlinarith
    have htail := frozenPrefixLength_negative_geometric_tail hX hi hG hc hn hcut
    have hpow : q^(N+m) ≤ q^m := pow_le_pow_of_le_one hq0.le hq1 (by omega)
    have hval : 2*q^m = 2/q * Real.exp (-(c^2/8)*((m+1 : ℕ) : ℝ)) := by
      have he : Real.exp (-(c^2/8)*((m+1 : ℕ) : ℝ)) = q^(m+1) := by
        rw [hqdef, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [he, pow_succ]
      field_simp
    have hreal : μ.real {ω | ((N+m+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X (-c) E ω} ≤
        2/q * Real.exp (-(c^2/8)*((m+1 : ℕ) : ℝ)) := by
      rw [← hval]
      have h2 : 2*q^(N+m) ≤ 2*q^m := by linarith
      exact htail.trans h2
    calc μ {ω | ((m+1 : ℕ) : ℝ) ≤ max (frozenPrefixLengthReal X (-c) E ω - N) 0}
        ≤ μ {ω | ((N+m+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X (-c) E ω} := measure_mono hsub
      _ = ENNReal.ofReal (μ.real {ω | ((N+m+1 : ℕ) : WithTop ℕ) ≤
            frozenPrefixLength X (-c) E ω}) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- C2.4 at a fixed margin: `E[(L_E(-c)/E)²]` is bounded uniformly in `E ≥ 1`. -/
theorem frozenPrefixLength_negative_sq_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c E : ℝ} (hc : 0 < c) (hE : 1 ≤ E) :
    (∫⁻ ω, ENNReal.ofReal ((frozenPrefixLengthReal X (-c) E ω / E)^2) ∂μ) ≤
      ENNReal.ofReal (frozenNegativeSqBound c) := by
  have := hi.isProbabilityMeasure
  have hE0 : 0 < E := by linarith
  set N : ℕ := ⌈4*E/c⌉₊ with hNdef
  set q : ℝ := Real.exp (-(c^2)/8) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  set D : Ω → ℝ := fun ω => max (frozenPrefixLengthReal X (-c) E ω - N) 0 with hDdef
  have hDm : Measurable D :=
    ((frozenPrefixLengthReal_measurable hX (-c) E).sub_const _).max measurable_const
  have hDnn : ∀ ω, 0 ≤ D ω := fun ω => le_max_right _ _
  have hDsq : (∫⁻ ω, ENNReal.ofReal (D ω^2) ∂μ) ≤
      ENNReal.ofReal (2/q * expTailMomentSum (c^2/8) 2) :=
    lintegral_pow_le_of_expTail hDm (ae_of_all _ hDnn) (by positivity) (by positivity)
      (fun k => frozenPrefixLength_negative_excess_tail hX hi hG hc hE0 k) 2
  set a : ℝ := 4/c+1 with hadef
  have hNle : (N : ℝ) ≤ 4*E/c + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hpt : ∀ ω, (frozenPrefixLengthReal X (-c) E ω / E)^2 ≤ 2*a^2 + 2*D ω^2 := by
    intro ω
    have hL0 := frozenPrefixLengthReal_nonneg X (-c) E ω
    have hLD : frozenPrefixLengthReal X (-c) E ω ≤ N + D ω := by
      have := le_max_left (frozenPrefixLengthReal X (-c) E ω - N) 0
      simp only [hDdef]
      linarith
    have hratio : frozenPrefixLengthReal X (-c) E ω / E ≤ a + D ω := by
      rw [div_le_iff₀ hE0]
      have h1 : (N : ℝ) ≤ (4/c + 1)*E := by
        have : 4*E/c = 4/c*E := by ring
        nlinarith
      have h2 : D ω ≤ D ω * E := le_mul_of_one_le_right (hDnn ω) hE
      nlinarith
    have hr0 : 0 ≤ frozenPrefixLengthReal X (-c) E ω / E := div_nonneg hL0 hE0.le
    nlinarith [sq_nonneg (a - D ω), hDnn ω]
  calc (∫⁻ ω, ENNReal.ofReal ((frozenPrefixLengthReal X (-c) E ω / E)^2) ∂μ)
      ≤ ∫⁻ ω, (ENNReal.ofReal (2*a^2) + ENNReal.ofReal 2 * ENNReal.ofReal (D ω^2)) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (2*a^2) + ENNReal.ofReal 2 * ∫⁻ ω, ENNReal.ofReal (D ω^2) ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (hDm.pow_const 2).ennreal_ofReal]
    _ ≤ ENNReal.ofReal (2*a^2) + ENNReal.ofReal 2 *
          ENNReal.ofReal (2/q * expTailMomentSum (c^2/8) 2) := by gcongr
    _ = ENNReal.ofReal (frozenNegativeSqBound c) := by
        have := expTailMomentSum_nonneg (c^2/8) 2
        rw [← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        rfl

/-! ### Convergence of means -/

/-- C2.3 in mean at a fixed negative margin: `g_E(-c)/E → ℓ(-c)`. -/
theorem frozenPrefixLength_negative_mean_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun E => (∫ ω, frozenPrefixLengthReal X (-c) E ω ∂μ) / E) atTop
      (𝓝 (secondSegmentLimitKernel X μ (-c))) := by
  have := hi.isProbabilityMeasure
  rw [← integral_two_div_frozenSlopeMagnitude hX hi hG (-c)]
  refine tendsto_of_seq_tendsto fun Es hEs => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hEs.eventually (eventually_ge_atTop (1 : ℝ)))
  set F : ℕ → ℝ := fun n => Es (n+N) with hFdef
  have hF : Tendsto F atTop atTop := hEs.comp (tendsto_add_atTop_nat N)
  have hF1 : ∀ n, 1 ≤ F n := fun n => hN (n+N) (by omega)
  set f : ℕ → Ω → ℝ := fun n ω => frozenPrefixLengthReal X (-c) (F n) ω / F n with hfdef
  have hfm : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((frozenPrefixLengthReal_measurable hX _ _).div_const _).aestronglyMeasurable
  have hu : UniformIntegrable f 1 μ :=
    BrownianAffine.uniformIntegrable_of_uniform_second_moment hfm
      (frozenNegativeSqBound_nonneg c)
      (fun n => frozenPrefixLength_negative_sq_lintegral_le hX hi hG hc (hF1 n))
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop
      (𝓝 (2 / frozenSlopeMagnitude X (-c) ω)) := by
    filter_upwards [frozenPrefixLength_tendsto_ae hX hi hG (-c)] with ω hω
    exact hω.2.2.comp hF
  have hy := hu.integrable_of_ae_tendsto hconv
  have hlim : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop
      (𝓝 (∫ ω, 2 / frozenSlopeMagnitude X (-c) ω ∂μ)) :=
    tendsto_integral_of_L1' _ hy.aestronglyMeasurable
      (Eventually.of_forall fun n => (hu.memLp n).integrable le_rfl)
      (tendsto_Lp_finite_of_tendsto_ae le_rfl (by norm_num) hfm
        (hu.memLp_of_ae_tendsto hconv) hu.2.1 hconv)
  have hlim' : Tendsto (fun n => (∫ ω, frozenPrefixLengthReal X (-c) (Es (n+N)) ω ∂μ) /
      Es (n+N)) atTop (𝓝 (∫ ω, 2 / frozenSlopeMagnitude X (-c) ω ∂μ)) := by
    simpa only [hfdef, hFdef, integral_div] using hlim
  exact (tendsto_add_atTop_iff_nat N).mp hlim'

/-- The same statement indexed by the margin itself. -/
theorem frozenMean_div_tendsto_kernel
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r < 0) :
    Tendsto (fun E => (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) / E) atTop
      (𝓝 (secondSegmentLimitKernel X μ r)) := by
  have h := frozenPrefixLength_negative_mean_tendsto hX hi hG (c := -r) (by linarith)
  simpa only [neg_neg] using h

/-- C2.7 in the limit: `ℓ(-c) ≤ C(1 + log₊(1/c))` with Lemma H.1's constant. -/
theorem secondSegmentLimitKernel_neg_le_log
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {c : ℝ} (hc : 0 < c) :
    secondSegmentLimitKernel X μ (-c) ≤
      frozenNegativeCarryLogConstant * (1 + max (Real.log (1/c)) 0) := by
  refine le_of_tendsto (frozenPrefixLength_negative_mean_tendsto hX hi hG hc) ?_
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with E hE
  have h := frozenPrefixLength_negative_mean_log_bound hX hi hG hc hE
  rw [div_le_iff₀ (by linarith)]
  calc (∫ ω, frozenPrefixLengthReal X (-c) E ω ∂μ)
      ≤ frozenNegativeCarryLogConstant*E*(1+max (Real.log (1/c)) 0) := h
    _ = frozenNegativeCarryLogConstant * (1 + max (Real.log (1/c)) 0) * E := by ring

end SwingRepair
