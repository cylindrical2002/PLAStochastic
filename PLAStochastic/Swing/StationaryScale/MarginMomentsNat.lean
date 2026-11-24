import PLAStochastic.Swing.StationaryScale.SegmentMeanScale

/-! # Uniform stationary margin moments of every fixed order

`eq:stationarymarginmoments`.  Once the mean scale `C_E ≤ C E log E` is known,
the refined tail is integrated against the weight `(n+1)^k`: the complementary
branch contributes a polylogarithmic factor beaten by `E`, and the stopped-sum
alternative keeps its `E^{-2}` factor.  All bounds are uniform in the tolerance.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The logarithm is beaten by every fixed power comparison with the scale. -/
theorem stationary_log_pow_le {m : ℕ} (hm : 1 ≤ m) {E : ℝ} (hE1 : 1 ≤ E) :
    (Real.log E)^m ≤ ((m : ℝ))^m*E := by
  have hEpos : (0 : ℝ) < E := by linarith
  have hL0 : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : (Real.exp (Real.log E/(m : ℝ)))^m = E := by
    rw [← Real.exp_nat_mul, show ((m : ℕ) : ℝ)*(Real.log E/(m : ℝ)) = Real.log E by
      field_simp]
    exact Real.exp_log hEpos
  have hb : Real.log E/(m : ℝ) ≤ Real.exp (Real.log E/(m : ℝ)) := by
    have := Real.add_one_le_exp (Real.log E/(m : ℝ))
    linarith
  have hpow : (Real.log E/(m : ℝ))^m ≤ (Real.exp (Real.log E/(m : ℝ)))^m :=
    pow_le_pow_left₀ (by positivity) hb m
  rw [hexp, div_pow, div_le_iff₀ (by positivity)] at hpow
  linarith

/-- Weighted discrete layer cake for a nonnegative observable. -/
theorem lintegral_ofReal_pow_le_tsum {S : Type*} [MeasurableSpace S] (π : Measure S)
    {M : S → ℝ} (hM : Measurable M) (hnn : ∀ s, 0 ≤ M s) {k : ℕ} (hk : 1 ≤ k) :
    (∫⁻ s, ENNReal.ofReal (M s^k) ∂π) ≤
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*π {s | (n : ℝ) < M s} := by
  have hMeas : ∀ n : ℕ, MeasurableSet {s | (n : ℝ) < M s} :=
    fun n => measurableSet_lt measurable_const hM
  have hpoint : ∀ s, ENNReal.ofReal (M s^k) ≤
      ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
        Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s := by
    intro s
    by_cases h0 : M s = 0
    · rw [h0, zero_pow (by omega : k ≠ 0), ENNReal.ofReal_zero]
      exact zero_le
    · have hpos : 0 < M s := lt_of_le_of_ne (hnn s) (Ne.symm h0)
      have hK1 : 0 < ⌈M s⌉₊ := Nat.ceil_pos.mpr hpos
      have hmem : s ∈ {s' | ((⌈M s⌉₊-1 : ℕ) : ℝ) < M s'} :=
        show ((⌈M s⌉₊-1 : ℕ) : ℝ) < M s from Nat.lt_ceil.mp (by omega)
      have hcast : ((⌈M s⌉₊-1 : ℕ) : ℝ)+1 = ((⌈M s⌉₊ : ℕ) : ℝ) := by
        have : ((⌈M s⌉₊-1 : ℕ) : ℝ) = ((⌈M s⌉₊ : ℕ) : ℝ)-1 := by
          rw [Nat.cast_sub hK1, Nat.cast_one]
        rw [this]
        ring
      have hle : M s ≤ ((⌈M s⌉₊-1 : ℕ) : ℝ)+1 := by
        rw [hcast]
        exact Nat.le_ceil _
      calc
        ENNReal.ofReal (M s^k) ≤ ENNReal.ofReal ((((⌈M s⌉₊-1 : ℕ) : ℝ)+1)^k) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hnn s) hle k)
        _ = ENNReal.ofReal ((((⌈M s⌉₊-1 : ℕ) : ℝ)+1)^k)*
              Set.indicator {s' | ((⌈M s⌉₊-1 : ℕ) : ℝ) < M s'}
                (fun _ => (1 : ℝ≥0∞)) s := by
          rw [Set.indicator_of_mem hmem, mul_one]
        _ ≤ _ := ENNReal.le_tsum (⌈M s⌉₊-1)
  calc
    (∫⁻ s, ENNReal.ofReal (M s^k) ∂π)
        ≤ ∫⁻ s, ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
            Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s ∂π :=
      lintegral_mono hpoint
    _ = ∑' n : ℕ, ∫⁻ s, ENNReal.ofReal (((n : ℝ)+1)^k)*
          Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s ∂π :=
      lintegral_tsum (fun n =>
        ((measurable_const.indicator (hMeas n)).const_mul _).aemeasurable)
    _ = ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*π {s | (n : ℝ) < M s} := by
      refine tsum_congr fun n => ?_
      rw [lintegral_const_mul _ (measurable_const.indicator (hMeas n)),
        lintegral_indicator (hMeas n)]
      simp

/-! ### The weighted geometric series -/

theorem summable_pow_exp_neg (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ)+1)^k*Real.exp (-(n : ℝ))) := by
  refine (summable_expTailMoment (c := 1) (by norm_num) k).congr fun n => ?_
  congr 2
  ring

theorem tsum_ofReal_pow_exp_neg {K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    ∑' n : ℕ, ENNReal.ofReal (K*(((n : ℝ)+1)^k*Real.exp (-(n : ℝ)))) =
      ENNReal.ofReal (K*expTailMomentSum 1 k) := by
  have hsum : Summable (fun n : ℕ => K*(((n : ℝ)+1)^k*Real.exp (-(n : ℝ)))) :=
    (summable_pow_exp_neg k).mul_left K
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum, tsum_mul_left]
  congr 2
  unfold expTailMomentSum
  refine tsum_congr fun n => ?_
  congr 2
  ring

/-! ### The `k`-th stationary moment of the negative margin -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def stationaryExcessMomentBound (k : ℕ) : ℝ :=
  Real.exp (1/2)*expTailMomentSum 1 k
    + (10 : ℝ)^(k+1)*(((k : ℝ)+2))^(k+2)*stationaryBadBranchConstant*stationaryScaleConstant
    + 2*stationaryScaleConstant*Real.exp 1*expTailMomentSum 1 k

theorem stationaryExcessMomentBound_nonneg (k : ℕ) : 0 ≤ stationaryExcessMomentBound k := by
  have h1 := expTailMomentSum_nonneg 1 k
  have h2 := stationaryBadBranchConstant_pos
  have h3 : (0 : ℝ) ≤ stationaryScaleConstant := by
    rw [stationaryScaleConstant]
    have := frozenUniformMeanConstant_pos
    have := stationaryMarginMomentConstant_nonneg
    have := stationaryEnvelopeMeanBound_nonneg
    positivity
  unfold stationaryExcessMomentBound
  positivity

theorem stationary_excess_pow_lintegral_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {k : ℕ} (hk : 1 ≤ k) :
    (∫⁻ y, ENNReal.ofReal (nativeRestartExcess E y^k) ∂π) ≤
      ENNReal.ofReal (stationaryExcessMomentBound k) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEone : Real.exp 1 ≤ E :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hE2 : (0 : ℝ) < E^2 := by positivity
  set Kb := stationaryBadBranchConstant with hKbdef
  have hKbpos : 0 < Kb := stationaryBadBranchConstant_pos
  set SC := stationaryScaleConstant with hSCdef
  have hSC0 : (0 : ℝ) ≤ SC := by
    rw [hSCdef, stationaryScaleConstant]
    have := frozenUniformMeanConstant_pos
    have := stationaryMarginMomentConstant_nonneg
    have := stationaryEnvelopeMeanBound_nonneg
    positivity
  set L := Real.log E with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    exact (Real.le_log_iff_exp_le hEpos).mpr hEone
  have hLE : L ≤ E := by
    have hEe : Real.exp L = E := by rw [hLdef, Real.exp_log hEpos]
    have := Real.add_one_le_exp L
    linarith [hEe ▸ this]
  set C := ∫ x, nativeRestartMean X μ E x ∂π with hCdef
  have hC1 : 1 ≤ C := one_le_stationary_mean hX hi hG hEpos
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hCscale : C ≤ SC*E*L := by
    rw [hSCdef, hCdef, hLdef]
    exact nativeRestart_stationary_mean_scale hX hi hG hE hπ
  set n₀ : ℕ := ⌈8*L⌉₊+1 with hn0def
  have hn0pos : 1 ≤ n₀ := by omega
  have hn0R : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn0pos
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
  have hT := stationary_excess_tail_split hX hi hG hEm hπ hn0pos (by rw [← hLdef]; exact hn0ge)
  -- the three weighted sums
  have hSum1 : ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
      ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) =
      ENNReal.ofReal (Real.exp (1/2)*expTailMomentSum 1 k) := by
    rw [← tsum_ofReal_pow_exp_neg (K := Real.exp (1/2)) (Real.exp_pos _).le k]
    refine tsum_congr fun n => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hSum3 : ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
      (if n < n₀ then 0 else
        ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ)))) ≤
      ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*expTailMomentSum 1 k) := by
    rw [← tsum_ofReal_pow_exp_neg (K := 2*C*Real.exp 1*(1/E^2)) (by positivity) k]
    refine ENNReal.tsum_le_tsum fun n => ?_
    by_cases hn : n < n₀
    · rw [if_pos hn, mul_zero]
      exact zero_le
    · rw [if_neg hn, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      apply le_of_eq
      ring
  have hSum2 : ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
      (if n < n₀ then ENNReal.ofReal (Kb*C/E^2) else 0) ≤
      ENNReal.ofReal ((n₀ : ℝ)^(k+1)*(Kb*C/E^2)) := by
    have hfac0 : (0 : ℝ) ≤ Kb*C/E^2 := by positivity
    have hterm : ∀ n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
        (if n < n₀ then ENNReal.ofReal (Kb*C/E^2) else 0) ≤
        (if n < n₀ then ENNReal.ofReal ((n₀ : ℝ)^k*(Kb*C/E^2)) else 0) := by
      intro n
      by_cases hn : n < n₀
      · rw [if_pos hn, if_pos hn, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : ((n : ℝ)+1) ≤ (n₀ : ℝ) := by exact_mod_cast hn
        have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ)+1) h1 k
        exact mul_le_mul_of_nonneg_right hpow hfac0
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
  -- the numerical bound on the branch term
  have hLpow : L^(k+2) ≤ (((k : ℝ)+2))^(k+2)*E := by
    have h := stationary_log_pow_le (m := k+2) (by omega) hE1
    rw [← hLdef] at h
    have hcast : (((k+2 : ℕ)) : ℝ) = (k : ℝ)+2 := by push_cast; ring
    rw [hcast] at h
    exact h
  have hbranch : (n₀ : ℝ)^(k+1)*(Kb*C/E^2) ≤
      (10 : ℝ)^(k+1)*(((k : ℝ)+2))^(k+2)*Kb*SC := by
    have hCE : C/E^2 ≤ SC*L/E := by
      rw [div_le_div_iff₀ hE2 hEpos]
      nlinarith
    have h1 : (n₀ : ℝ)^(k+1) ≤ (10*L)^(k+1) :=
      pow_le_pow_left₀ (by positivity) hn0le (k+1)
    have h2 : Kb*(C/E^2) ≤ Kb*(SC*L/E) := mul_le_mul_of_nonneg_left hCE hKbpos.le
    have h3 : (n₀ : ℝ)^(k+1)*(Kb*(C/E^2)) ≤ (10*L)^(k+1)*(Kb*(SC*L/E)) := by
      apply mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : (10*L)^(k+1)*(Kb*(SC*L/E)) =
        (10 : ℝ)^(k+1)*Kb*SC*(L^(k+2)/E) := by
      rw [mul_pow, pow_succ L k]
      field_simp
      ring
    have h5 : L^(k+2)/E ≤ (((k : ℝ)+2))^(k+2) := by
      rw [div_le_iff₀ hEpos]
      linarith [hLpow]
    have h6 : (10 : ℝ)^(k+1)*Kb*SC*(L^(k+2)/E) ≤
        (10 : ℝ)^(k+1)*Kb*SC*(((k : ℝ)+2))^(k+2) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    calc (n₀ : ℝ)^(k+1)*(Kb*C/E^2) = (n₀ : ℝ)^(k+1)*(Kb*(C/E^2)) := by ring
      _ ≤ (10*L)^(k+1)*(Kb*(SC*L/E)) := h3
      _ = (10 : ℝ)^(k+1)*Kb*SC*(L^(k+2)/E) := h4
      _ ≤ (10 : ℝ)^(k+1)*Kb*SC*(((k : ℝ)+2))^(k+2) := h6
      _ = (10 : ℝ)^(k+1)*(((k : ℝ)+2))^(k+2)*Kb*SC := by ring
  have hthird : 2*C*Real.exp 1*(1/E^2)*expTailMomentSum 1 k ≤
      2*SC*Real.exp 1*expTailMomentSum 1 k := by
    have hT0 : 0 ≤ expTailMomentSum 1 k := expTailMomentSum_nonneg 1 k
    have hCC : 2*C*Real.exp 1*(1/E^2) ≤ 2*SC*Real.exp 1 := by
      have hstep : C*(1/E^2) ≤ SC := by
        rw [mul_one_div, div_le_iff₀ hE2]
        nlinarith
      nlinarith [Real.exp_pos (1 : ℝ)]
    nlinarith [Real.exp_pos (1 : ℝ)]
  calc
    (∫⁻ y, ENNReal.ofReal (nativeRestartExcess E y^k) ∂π)
        ≤ ∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
            π {y | (n : ℝ) < nativeRestartExcess E y} :=
      lintegral_ofReal_pow_le_tsum π (measurable_nativeRestartExcess E)
        (fun y => le_max_right _ _) hk
    _ ≤ ∑' n : ℕ, (ENNReal.ofReal (((n : ℝ)+1)^k)*
            ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) +
          ENNReal.ofReal (((n : ℝ)+1)^k)*
            (if n < n₀ then ENNReal.ofReal (Kb*C/E^2) else 0) +
          ENNReal.ofReal (((n : ℝ)+1)^k)*
            (if n < n₀ then 0 else
              ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ))))) := by
      refine ENNReal.tsum_le_tsum fun n => ?_
      have hstep := mul_le_mul' (le_refl (ENNReal.ofReal (((n : ℝ)+1)^k))) (hT n)
      rw [mul_add, mul_add] at hstep
      exact hstep
    _ = (∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
            ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ)))) +
          (∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
            (if n < n₀ then ENNReal.ofReal (Kb*C/E^2) else 0)) +
          (∑' n : ℕ, ENNReal.ofReal (((n : ℝ)+1)^k)*
            (if n < n₀ then 0 else
              ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ))))) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal (Real.exp (1/2)*expTailMomentSum 1 k) +
          ENNReal.ofReal ((n₀ : ℝ)^(k+1)*(Kb*C/E^2)) +
          ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*expTailMomentSum 1 k) := by
      rw [hSum1]
      exact add_le_add (add_le_add le_rfl hSum2) hSum3
    _ ≤ ENNReal.ofReal (stationaryExcessMomentBound k) := by
      have hn1 : (0 : ℝ) ≤ Real.exp (1/2)*expTailMomentSum 1 k := by
        have := expTailMomentSum_nonneg 1 k
        positivity
      have hn2 : (0 : ℝ) ≤ (n₀ : ℝ)^(k+1)*(Kb*C/E^2) := by positivity
      have hn3 : (0 : ℝ) ≤ 2*C*Real.exp 1*(1/E^2)*expTailMomentSum 1 k := by
        have := expTailMomentSum_nonneg 1 k
        positivity
      rw [← ENNReal.ofReal_add hn1 hn2, ← ENNReal.ofReal_add (by linarith) hn3]
      apply ENNReal.ofReal_le_ofReal
      rw [stationaryExcessMomentBound, ← hKbdef, ← hSCdef]
      linarith

/-! ### The `k`-th stationary moment of the positive margin -/

theorem max_pow_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    (max 1 (max a b))^k ≤ 1+a^k+b^k := by
  have hak : 0 ≤ a^k := pow_nonneg ha k
  have hbk : 0 ≤ b^k := pow_nonneg hb k
  have hM : max 1 (max a b) = 1 ∨ max 1 (max a b) = a ∨ max 1 (max a b) = b := by
    rcases max_cases (1 : ℝ) (max a b) with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · rcases max_cases a b with ⟨h2, _⟩ | ⟨h2, _⟩
      · exact Or.inr (Or.inl (h.trans h2))
      · exact Or.inr (Or.inr (h.trans h2))
  rcases hM with h | h | h <;> rw [h]
  · rw [one_pow]; linarith
  · linarith
  · linarith

omit mΩ in
/-- Pathwise `k`-th power form of the positive-margin control. -/
theorem nativeRestart_marginPos_pow_next_le (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤ nativeGaussianEnvelope X ω*((n : ℝ)+1))
    (hf : nativeRestartLength X E x ω ≠ ⊤) (k : ℕ) :
    nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ≤
      (25 : ℝ)^k*(1+nativeRestartExcess E x^k+nativeGaussianEnvelope X ω^k) := by
  have ha : 0 ≤ nativeRestartExcess E x := le_max_right _ _
  have hb : 0 ≤ nativeGaussianEnvelope X ω := nativeGaussianEnvelope_nonneg X ω
  have hm : 0 ≤ nativeRestartMarginPos E (nativeRestartNext X E x ω) := le_max_right _ _
  have hbound := nativeRestart_marginPos_next_le X hE x ω hW hf
  set M := max 1 (max (nativeRestartExcess E x) (nativeGaussianEnvelope X ω)) with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMa : nativeRestartExcess E x ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMb : nativeGaussianEnvelope X ω ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hle : nativeRestartMarginPos E (nativeRestartNext X E x ω) ≤ 25*M := by linarith
  calc nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ≤ (25*M)^k :=
        pow_le_pow_left₀ hm hle k
    _ = (25 : ℝ)^k*M^k := by rw [mul_pow]
    _ ≤ (25 : ℝ)^k*(1+nativeRestartExcess E x^k+nativeGaussianEnvelope X ω^k) :=
        mul_le_mul_of_nonneg_left (max_pow_le_add ha hb k) (by positivity)

def stationaryMarginPosMomentBound (k : ℕ) : ℝ :=
  (25 : ℝ)^k*(1+stationaryExcessMomentBound k+
    nativeGaussianEnvelopeExpTailConstant*expTailMomentSum 1 k)

theorem measurable_nativeRestartExcess_pow (E : ℝ) (k : ℕ) :
    Measurable (fun y : ℝ => nativeRestartExcess E y^k) :=
  (measurable_nativeRestartExcess E).pow_const k

theorem stationary_excess_pow_integrable [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun y => nativeRestartExcess E y^k) π := by
  have hnn : 0 ≤ᵐ[π] fun y => nativeRestartExcess E y^k :=
    Filter.Eventually.of_forall fun y => pow_nonneg (le_max_right _ _) k
  refine ⟨(measurable_nativeRestartExcess_pow E k).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn]
  exact lt_of_le_of_lt (stationary_excess_pow_lintegral_le hX hi hG hE hπ hk)
    ENNReal.ofReal_lt_top

theorem stationary_excess_pow_integral_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {k : ℕ} (hk : 1 ≤ k) :
    (∫ y, nativeRestartExcess E y^k ∂π) ≤ stationaryExcessMomentBound k := by
  have hnn : 0 ≤ᵐ[π] fun y => nativeRestartExcess E y^k :=
    Filter.Eventually.of_forall fun y => pow_nonneg (le_max_right _ _) k
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    (measurable_nativeRestartExcess_pow E k).aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (stationary_excess_pow_lintegral_le hX hi hG hE hπ hk)
  rwa [ENNReal.toReal_ofReal (stationaryExcessMomentBound_nonneg k)] at h

theorem stationary_marginPos_pow_integral_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {k : ℕ} (hk : 1 ≤ k) :
    (∫ y, nativeRestartMarginPos E y^k ∂π) ≤ stationaryMarginPosMomentBound k := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  have henvint : Integrable (fun ω => nativeGaussianEnvelope X ω^k) μ :=
    nativeGaussianEnvelope_integrable_pow hX hi hG k
  have henvle : (∫ ω, nativeGaussianEnvelope X ω^k ∂μ) ≤
      nativeGaussianEnvelopeExpTailConstant*expTailMomentSum 1 k :=
    nativeGaussianEnvelope_integral_pow_le hX hi hG k
  have hmp_meas : Measurable (fun y : ℝ => nativeRestartMarginPos E y^k) :=
    (measurable_nativeRestartMarginPos E).pow_const k
  have hmp_nonneg : ∀ y : ℝ, 0 ≤ nativeRestartMarginPos E y^k :=
    fun y => pow_nonneg (le_max_right _ _) k
  have hmp_upper : ∀ y : ℝ, nativeRestartMarginPos E y^k ≤ E^k := by
    intro y
    exact pow_le_pow_left₀ (le_max_right _ _)
      (max_le (by linarith [abs_nonneg y]) hEpos.le) k
  have hmp_int : Integrable (fun y : ℝ => nativeRestartMarginPos E y^k) π :=
    Doeblin.integrable_bounded_reward π hmp_meas hmp_nonneg hmp_upper
  have hFm : Measurable
      (fun p : ℝ × Ω => nativeRestartMarginPos E (nativeRestartNext X E p.1 p.2)^k) :=
    hmp_meas.comp (nativeRestartNext_measurable X hX E)
  have hFx : ∀ x : ℝ, Measurable
      (fun ω : Ω => nativeRestartMarginPos E (nativeRestartNext X E x ω)^k) :=
    fun x => hFm.comp ((measurable_const (a := x)).prodMk measurable_id)
  have hslice_int : ∀ x : ℝ, Integrable
      (fun ω => nativeRestartMarginPos E (nativeRestartNext X E x ω)^k) μ :=
    fun x => Doeblin.integrable_bounded_reward μ (hFx x)
      (fun ω => hmp_nonneg _) (fun ω => hmp_upper _)
  have hfm : Measurable
      (fun x : ℝ => ∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ∂μ) :=
    hFm.stronglyMeasurable.integral_prod_right.measurable
  have hfn : ∀ x : ℝ,
      0 ≤ ∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ∂μ :=
    fun x => integral_nonneg (fun ω => hmp_nonneg _)
  have hfu : ∀ x : ℝ,
      (∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ∂μ) ≤ E^k := by
    intro x
    calc (∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ∂μ)
        ≤ ∫ _ω : Ω, E^k ∂μ :=
          integral_mono (hslice_int x) (integrable_const _) (fun ω => hmp_upper _)
      _ = E^k := by simp
  have hf_int : Integrable
      (fun x : ℝ => ∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ∂μ) π :=
    Doeblin.integrable_bounded_reward π hfm hfn hfu
  have hexc_int : Integrable (fun y => nativeRestartExcess E y^k) π :=
    stationary_excess_pow_integrable hX hi hG hE hπ hk
  have hinner : ∀ x : ℝ,
      (∫ ω, nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ∂μ) ≤
        (25 : ℝ)^k*(1+nativeRestartExcess E x^k+
          (∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) := by
    intro x
    have h1 : Integrable
        (fun ω : Ω => (25 : ℝ)^k*(1+nativeRestartExcess E x^k+
          nativeGaussianEnvelope X ω^k)) μ :=
      (((integrable_const (1 : ℝ)).add (integrable_const _)).add henvint).const_mul _
    have hae : ∀ᵐ ω ∂μ,
        nativeRestartMarginPos E (nativeRestartNext X E x ω)^k ≤
          (25 : ℝ)^k*(1+nativeRestartExcess E x^k+nativeGaussianEnvelope X ω^k) := by
      filter_upwards [nativeRestartLength_ae_finite hX hi hG hEpos x,
        nativeGaussianEnvelope_bounds_ae hX hi hG] with ω hfin hW
      exact nativeRestart_marginPos_pow_next_le X hEpos.le x ω hW hfin k
    have hmono := integral_mono_ae (hslice_int x) h1 hae
    have heq : (∫ ω, (25 : ℝ)^k*(1+nativeRestartExcess E x^k+
        nativeGaussianEnvelope X ω^k) ∂μ) =
        (25 : ℝ)^k*(1+nativeRestartExcess E x^k+
          (∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) := by
      have hconst : Integrable (fun _ : Ω => 1+nativeRestartExcess E x^k) μ :=
        integrable_const _
      rw [integral_const_mul, integral_add hconst henvint, integral_const]
      simp
    rw [heq] at hmono
    exact hmono
  have hg1 : Integrable (fun x : ℝ => (25 : ℝ)^k*(1+nativeRestartExcess E x^k+
      (∫ ω, nativeGaussianEnvelope X ω^k ∂μ))) π :=
    (((integrable_const (1 : ℝ)).add hexc_int).add (integrable_const _)).const_mul _
  have hmono := integral_mono hf_int hg1 hinner
  have heq2 : (∫ x, (25 : ℝ)^k*(1+nativeRestartExcess E x^k+
      (∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) ∂π) =
      (25 : ℝ)^k*(1+(∫ y, nativeRestartExcess E y^k ∂π)+
        (∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) := by
    have hA : Integrable (fun x : ℝ => 1+nativeRestartExcess E x^k) π :=
      (integrable_const (1 : ℝ)).add hexc_int
    have hB : Integrable
        (fun _ : ℝ => (∫ ω, nativeGaussianEnvelope X ω^k ∂μ)) π := integrable_const _
    rw [integral_const_mul, integral_add hA hB,
      integral_add (integrable_const (1 : ℝ)) hexc_int, integral_const, integral_const]
    simp
  rw [heq2] at hmono
  rw [nativeRestart_invariant_integral_eq_fresh hX hπ hmp_meas hmp_int]
  refine hmono.trans ?_
  rw [stationaryMarginPosMomentBound]
  have hexcle := stationary_excess_pow_integral_le hX hi hG hE hπ hk
  have h25 : (0 : ℝ) ≤ (25 : ℝ)^k := by positivity
  apply mul_le_mul_of_nonneg_left _ h25
  linarith

/-! ### Theorem 4.2, uniform stationary margin moments -/

def stationaryMarginMomentBound (k : ℕ) : ℝ :=
  stationaryMarginPosMomentBound k + stationaryExcessMomentBound k

theorem abs_margin_pow_eq (E y : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    |E-abs y|^k = nativeRestartMarginPos E y^k + nativeRestartExcess E y^k := by
  unfold nativeRestartMarginPos nativeRestartExcess
  rcases le_total (|y|) E with h | h
  · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith : (0 : ℝ) ≤ E-|y|),
      max_eq_right (by linarith : |y|-E ≤ 0), zero_pow (by omega : k ≠ 0), add_zero]
  · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith : E-|y| ≤ 0),
      max_eq_left (by linarith : (0 : ℝ) ≤ |y|-E), zero_pow (by omega : k ≠ 0), zero_add]
    congr 1
    ring

/-- Theorem 4.2, moment part: every fixed integer moment of the stationary
boundary margin is bounded uniformly in the tolerance. -/
theorem nativeRestart_stationary_margin_pow_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {k : ℕ} (hk : 1 ≤ k) :
    (∫ y, |E-abs y|^k ∂π) ≤ stationaryMarginMomentBound k := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEm : stationaryMarginThreshold ≤ E :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hEm
  have hEpos : (0 : ℝ) < E := by linarith
  have hmp_meas : Measurable (fun y : ℝ => nativeRestartMarginPos E y^k) :=
    (measurable_nativeRestartMarginPos E).pow_const k
  have hmp_nonneg : ∀ y : ℝ, 0 ≤ nativeRestartMarginPos E y^k :=
    fun y => pow_nonneg (le_max_right _ _) k
  have hmp_upper : ∀ y : ℝ, nativeRestartMarginPos E y^k ≤ E^k := by
    intro y
    exact pow_le_pow_left₀ (le_max_right _ _)
      (max_le (by linarith [abs_nonneg y]) hEpos.le) k
  have hmp_int : Integrable (fun y : ℝ => nativeRestartMarginPos E y^k) π :=
    Doeblin.integrable_bounded_reward π hmp_meas hmp_nonneg hmp_upper
  have hexc_int : Integrable (fun y => nativeRestartExcess E y^k) π :=
    stationary_excess_pow_integrable hX hi hG hE hπ hk
  have hsplit : (∫ y, |E-abs y|^k ∂π) =
      (∫ y, nativeRestartMarginPos E y^k ∂π)+(∫ y, nativeRestartExcess E y^k ∂π) := by
    rw [← integral_add hmp_int hexc_int]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => abs_margin_pow_eq E y hk)
  rw [hsplit, stationaryMarginMomentBound]
  exact add_le_add (stationary_marginPos_pow_integral_le hX hi hG hE hπ hk)
    (stationary_excess_pow_integral_le hX hi hG hE hπ hk)

/-- Theorem 4.2 (`thm:stationaryscale`) for the actual constrained-SSE restart
chain.  Both conclusions are stated for every invariant probability law of the
genuine restart kernel; Theorem 4.1 supplies such a law and its uniqueness.
The constants do not depend on the tolerance. -/
theorem theorem_4_2_stationary_scale [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) :
    (∀ k : ℕ, 1 ≤ k → ∀ E : ℝ, stationaryScaleThreshold ≤ E →
        ∀ π : Measure ℝ, IsProbabilityMeasure π →
          (nativeRestartKernel X μ E).Invariant π →
            (∫ y, |E-abs y|^k ∂π) ≤ stationaryMarginMomentBound k) ∧
      (∀ E : ℝ, stationaryScaleThreshold ≤ E →
        ∀ π : Measure ℝ, IsProbabilityMeasure π →
          (nativeRestartKernel X μ E).Invariant π →
            (∫ x, nativeRestartMean X μ E x ∂π) ≤
              stationaryScaleConstant*E*Real.log E) := by
  constructor
  · intro k hk E hE π hp hπ
    let : IsProbabilityMeasure π := hp
    exact nativeRestart_stationary_margin_pow_le hX hi hG hE hπ hk
  · intro E hE π hp hπ
    let : IsProbabilityMeasure π := hp
    exact nativeRestart_stationary_mean_scale hX hi hG hE hπ

end SwingRepair
