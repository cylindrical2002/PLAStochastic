import PLAStochastic.Swing.StationaryScale.BadBranch

/-! # The stationary negative-margin moment

`eq:stationarynegativemoment` for `p = 1`.  The refined tail is integrated on
the integer grid: below the threshold `8 log E` the complementary-branch term
is used, above it the stopped-sum alternative, whose Gaussian factor beats
`E^{-2}`.  Only the two already proved stationary tails enter.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! ### An elementary geometric series -/

def stationaryGeomExpSum : ℝ := (1-Real.exp (-1))⁻¹

theorem stationaryGeomExpSum_pos : 0 < stationaryGeomExpSum := by
  have h : Real.exp (-1) < 1 := by
    have hh := Real.exp_lt_one_iff (x := (-1 : ℝ))
    exact hh.mpr (by norm_num)
  unfold stationaryGeomExpSum
  exact inv_pos.mpr (by linarith)

theorem exp_neg_one_lt_one : Real.exp (-1) < 1 := by
  have h := Real.exp_lt_one_iff (x := (-1 : ℝ))
  exact h.mpr (by norm_num)

theorem exp_neg_nat_eq_pow (n : ℕ) : Real.exp (-(n : ℝ)) = (Real.exp (-1))^n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem summable_exp_neg_nat : Summable (fun n : ℕ => Real.exp (-(n : ℝ))) := by
  have hbase : Summable (fun n : ℕ => (Real.exp (-1))^n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le exp_neg_one_lt_one
  exact hbase.congr (fun n => (exp_neg_nat_eq_pow n).symm)

theorem tsum_exp_neg_nat : ∑' n : ℕ, Real.exp (-(n : ℝ)) = stationaryGeomExpSum := by
  rw [tsum_congr exp_neg_nat_eq_pow,
    tsum_geometric_of_lt_one (Real.exp_pos _).le exp_neg_one_lt_one]
  rfl

theorem tsum_ofReal_exp_neg {K : ℝ} (hK : 0 ≤ K) :
    ∑' n : ℕ, ENNReal.ofReal (K*Real.exp (-(n : ℝ))) =
      ENNReal.ofReal (K*stationaryGeomExpSum) := by
  have hsum : Summable (fun n : ℕ => K*Real.exp (-(n : ℝ))) :=
    summable_exp_neg_nat.mul_left K
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hK (Real.exp_pos _).le) hsum,
    tsum_mul_left, tsum_exp_neg_nat]

/-- `exp(-n²/2)` is dominated by a geometric series. -/
theorem exp_neg_sq_half_le (n : ℕ) :
    Real.exp (-(n : ℝ)^2/2) ≤ Real.exp (1/2)*Real.exp (-(n : ℝ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ((n : ℝ)-1)]

/-- Above a threshold the same factor gains the whole threshold decay. -/
theorem exp_neg_sq_half_le_of_ge {n n₀ : ℕ} (h : n₀ ≤ n) :
    Real.exp (-(n : ℝ)^2/2) ≤
      Real.exp 1*Real.exp (-(n₀ : ℝ)^2/4)*Real.exp (-(n : ℝ)) := by
  have hn : ((n₀ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have hn0 : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ((n : ℝ)-2), sq_nonneg ((n : ℝ)-(n₀ : ℝ))]

/-! ### The discrete layer-cake bound -/

theorem lintegral_ofReal_le_tsum_meas_gt {S : Type*} [MeasurableSpace S] (π : Measure S)
    {M : S → ℝ} (hM : Measurable M) :
    (∫⁻ s, ENNReal.ofReal (M s) ∂π) ≤ ∑' n : ℕ, π {s | (n : ℝ) < M s} := by
  have hMeas : ∀ n : ℕ, MeasurableSet {s | (n : ℝ) < M s} :=
    fun n => measurableSet_lt measurable_const hM
  have hpoint : ∀ s, ENNReal.ofReal (M s) ≤
      ∑' n : ℕ, Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s := by
    intro s
    have hle : ENNReal.ofReal (M s) ≤ ((⌈M s⌉₊ : ℕ) : ℝ≥0∞) := by
      rw [show (((⌈M s⌉₊ : ℕ)) : ℝ≥0∞) = ENNReal.ofReal ((⌈M s⌉₊ : ℕ) : ℝ) from
        (ENNReal.ofReal_natCast _).symm]
      exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
    have hterm : ∀ n ∈ Finset.range ⌈M s⌉₊,
        Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s = 1 := by
      intro n hn
      exact Set.indicator_of_mem
        (show s ∈ {s' | (n : ℝ) < M s'} from Nat.lt_ceil.mp (Finset.mem_range.mp hn))
        (fun _ => (1 : ℝ≥0∞))
    calc
      ENNReal.ofReal (M s) ≤ ((⌈M s⌉₊ : ℕ) : ℝ≥0∞) := hle
      _ = ∑ _n ∈ Finset.range ⌈M s⌉₊, (1 : ℝ≥0∞) := by simp
      _ = ∑ n ∈ Finset.range ⌈M s⌉₊,
            Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s :=
        (Finset.sum_congr rfl hterm).symm
      _ ≤ ∑' n : ℕ, Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s :=
        ENNReal.sum_le_tsum _
  calc
    (∫⁻ s, ENNReal.ofReal (M s) ∂π)
        ≤ ∫⁻ s, ∑' n : ℕ, Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s ∂π :=
      lintegral_mono hpoint
    _ = ∑' n : ℕ, ∫⁻ s, Set.indicator {s' | (n : ℝ) < M s'} (fun _ => (1 : ℝ≥0∞)) s ∂π :=
      lintegral_tsum (fun n => (measurable_const.indicator (hMeas n)).aemeasurable)
    _ = ∑' n : ℕ, π {s | (n : ℝ) < M s} := by
      refine tsum_congr fun n => ?_
      rw [lintegral_indicator (hMeas n)]
      simp

/-! ### The stationary first moment of the negative margin -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def stationaryMarginMomentConstant : ℝ := Real.exp (1/2)*stationaryGeomExpSum

theorem stationaryMarginMomentConstant_nonneg : 0 ≤ stationaryMarginMomentConstant := by
  have := stationaryGeomExpSum_pos
  unfold stationaryMarginMomentConstant
  positivity

theorem measurable_nativeRestartExcess (E : ℝ) : Measurable (nativeRestartExcess E) := by
  unfold nativeRestartExcess
  exact (measurable_id.abs.sub_const E).max measurable_const

/-- The integer-grid split of the refined stationary tail: below the threshold
the complementary branch is used, above it the stopped-sum alternative. -/
theorem stationary_excess_tail_split [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryMarginThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π)
    {n₀ : ℕ} (hn0pos : 1 ≤ n₀) (hn0ge : 8*Real.log E ≤ (n₀ : ℝ)) (n : ℕ) :
    π {y | (n : ℝ) < nativeRestartExcess E y} ≤
      ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) +
        (if n < n₀ then ENNReal.ofReal (stationaryBadBranchConstant*
          (∫ x, nativeRestartMean X μ E x ∂π)/E^2) else 0) +
        (if n < n₀ then 0 else
          ENNReal.ofReal (2*(∫ x, nativeRestartMean X μ E x ∂π)*Real.exp 1*(1/E^2)*
            Real.exp (-(n : ℝ)))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hE
  have hEpos : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hC1 : 1 ≤ ∫ x, nativeRestartMean X μ E x ∂π :=
    one_le_stationary_mean hX hi hG hEpos
  have hC0 : (0 : ℝ) ≤ ∫ x, nativeRestartMean X μ E x ∂π := by linarith
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
  have hβ : (π.prod μ) (nativeRestartFavorableSet X E)ᶜ ≤
      ENNReal.ofReal (stationaryBadBranchConstant*
        (∫ x, nativeRestartMean X μ E x ∂π)/E^2) :=
    measure_prod_nativeRestart_bad_branch_le hX hi hG hE hπ
  have hn0' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hn : n < n₀
  · rw [if_pos hn, if_pos hn, add_zero]
    refine (measure_pi_nativeRestart_margin_refined_tail hX hi hG hEpos hπ hn0').trans ?_
    exact add_le_add (ENNReal.ofReal_le_ofReal (exp_neg_sq_half_le n)) hβ
  · rw [if_neg hn, if_neg hn, add_zero]
    refine le_trans ?_ le_add_self
    refine (measure_pi_nativeRestart_margin_raw_tail hX hi hG hEpos hπ hn0').trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hdom := exp_neg_sq_half_le_of_ge (le_of_not_gt hn)
    have hstep : Real.exp (-(n : ℝ)^2/2) ≤ Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ)) := by
      refine hdom.trans ?_
      have h1 : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
      have h2 : 0 ≤ Real.exp (-(n : ℝ)) := (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left hexpn0 h1
      nlinarith
    nlinarith [Real.exp_pos (-(n : ℝ)), Real.exp_pos (-(n : ℝ)^2/2)]

theorem stationary_excess_lintegral_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryMarginThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (∫⁻ y, ENNReal.ofReal (nativeRestartExcess E y) ∂π) ≤
      ENNReal.ofReal (stationaryMarginMomentConstant +
        ((8*Real.log E+2)*stationaryBadBranchConstant +
          2*Real.exp 1*stationaryGeomExpSum)*
            (∫ x, nativeRestartMean X μ E x ∂π)/E^2) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hE
  have hEpos : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hE2 : (0 : ℝ) < E^2 := by positivity
  set C := ∫ x, nativeRestartMean X μ E x ∂π with hCdef
  have hC1 : 1 ≤ C := one_le_stationary_mean hX hi hG hEpos
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hgeom : 0 < stationaryGeomExpSum := stationaryGeomExpSum_pos
  have hKbad : 0 < stationaryBadBranchConstant := stationaryBadBranchConstant_pos
  set L := Real.log E with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hE1
  set n₀ : ℕ := ⌈8*L⌉₊+1 with hn0def
  have hn0pos : 1 ≤ n₀ := by omega
  have hn0ge : 8*L ≤ (n₀ : ℝ) := by
    have h := Nat.le_ceil (8*L)
    have h1 : ((⌈8*L⌉₊ : ℕ) : ℝ) ≤ (n₀ : ℝ) := by
      rw [hn0def]
      push_cast
      linarith
    linarith
  have hn0le : ((n₀ : ℕ) : ℝ) ≤ 8*L+2 := by
    have h := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 8*L)
    rw [hn0def]
    push_cast
    linarith
  have hn0R : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn0pos
  -- the threshold decay
  have hlogexp : Real.exp (-(2*L)) = 1/E^2 := by
    have hEe : Real.exp L = E := Real.exp_log hEpos
    rw [Real.exp_neg, two_mul, Real.exp_add, hEe]
    rw [one_div]
    congr 1
    ring
  have hexpn0 : Real.exp (-(n₀ : ℝ)^2/4) ≤ 1/E^2 := by
    rw [← hlogexp]
    apply Real.exp_le_exp.mpr
    nlinarith
  -- the branch measure
  set β := (π.prod μ) (nativeRestartFavorableSet X E)ᶜ with hβdef
  have hβ : β ≤ ENNReal.ofReal (stationaryBadBranchConstant*C/E^2) := by
    rw [hβdef, hCdef]
    exact measure_prod_nativeRestart_bad_branch_le hX hi hG hE hπ
  -- the integer tail bound
  have hT : ∀ n : ℕ, π {y | (n : ℝ) < nativeRestartExcess E y} ≤
      ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) +
        (if n < n₀ then ENNReal.ofReal (stationaryBadBranchConstant*C/E^2) else 0) +
        (if n < n₀ then 0 else
          ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ)))) := by
    intro n
    rw [hCdef]
    exact stationary_excess_tail_split hX hi hG hE hπ hn0pos hn0ge n
  -- summation
  have hsum1 : ∑' n : ℕ, ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) =
      ENNReal.ofReal (Real.exp (1/2)*stationaryGeomExpSum) :=
    tsum_ofReal_exp_neg (Real.exp_pos _).le
  have hsum2 : ∑' n : ℕ,
      (if n < n₀ then ENNReal.ofReal (stationaryBadBranchConstant*C/E^2) else 0) =
      (n₀ : ℝ≥0∞)*ENNReal.ofReal (stationaryBadBranchConstant*C/E^2) := by
    rw [tsum_eq_sum (s := Finset.range n₀) (fun b hb => by
      rw [if_neg (by simpa using hb)])]
    rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_range.mp hn)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum3 : ∑' n : ℕ, (if n < n₀ then 0 else
        ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ)))) ≤
      ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*stationaryGeomExpSum) := by
    rw [← tsum_ofReal_exp_neg (K := 2*C*Real.exp 1*(1/E^2))
      (by positivity)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    by_cases hn : n < n₀
    · rw [if_pos hn]
      exact zero_le
    · rw [if_neg hn]
  calc
    (∫⁻ y, ENNReal.ofReal (nativeRestartExcess E y) ∂π)
        ≤ ∑' n : ℕ, π {y | (n : ℝ) < nativeRestartExcess E y} :=
      lintegral_ofReal_le_tsum_meas_gt π (measurable_nativeRestartExcess E)
    _ ≤ ∑' n : ℕ, (ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ))) +
          (if n < n₀ then ENNReal.ofReal (stationaryBadBranchConstant*C/E^2) else 0) +
          (if n < n₀ then 0 else
            ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ))))) :=
      ENNReal.tsum_le_tsum hT
    _ = (∑' n : ℕ, ENNReal.ofReal (Real.exp (1/2)*Real.exp (-(n : ℝ)))) +
          (∑' n : ℕ, (if n < n₀ then
            ENNReal.ofReal (stationaryBadBranchConstant*C/E^2) else 0)) +
          (∑' n : ℕ, (if n < n₀ then 0 else
            ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*Real.exp (-(n : ℝ))))) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal (Real.exp (1/2)*stationaryGeomExpSum) +
          (n₀ : ℝ≥0∞)*ENNReal.ofReal (stationaryBadBranchConstant*C/E^2) +
          ENNReal.ofReal (2*C*Real.exp 1*(1/E^2)*stationaryGeomExpSum) := by
      rw [hsum1, hsum2]
      exact add_le_add le_rfl hsum3
    _ ≤ ENNReal.ofReal (stationaryMarginMomentConstant +
          ((8*L+2)*stationaryBadBranchConstant +
            2*Real.exp 1*stationaryGeomExpSum)*C/E^2) := by
      have hmid : (n₀ : ℝ≥0∞)*ENNReal.ofReal (stationaryBadBranchConstant*C/E^2) =
          ENNReal.ofReal ((n₀ : ℝ)*(stationaryBadBranchConstant*C/E^2)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      rw [hmid]
      have hnn1 : (0 : ℝ) ≤ Real.exp (1/2)*stationaryGeomExpSum := by positivity
      have hnn2 : (0 : ℝ) ≤ (n₀ : ℝ)*(stationaryBadBranchConstant*C/E^2) := by positivity
      have hnn3 : (0 : ℝ) ≤ 2*C*Real.exp 1*(1/E^2)*stationaryGeomExpSum := by positivity
      rw [← ENNReal.ofReal_add hnn1 hnn2, ← ENNReal.ofReal_add (by linarith) hnn3]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [stationaryMarginMomentConstant]
      have hkey : ((8*L+2)*stationaryBadBranchConstant +
          2*Real.exp 1*stationaryGeomExpSum)*C/E^2 =
          (8*L+2)*stationaryBadBranchConstant*C/E^2 +
            2*C*Real.exp 1*(1/E^2)*stationaryGeomExpSum := by
        field_simp
      have hcmp : (n₀ : ℝ)*(stationaryBadBranchConstant*C/E^2) ≤
          (8*L+2)*stationaryBadBranchConstant*C/E^2 := by
        have hfac : 0 ≤ stationaryBadBranchConstant*C/E^2 := by positivity
        have := mul_le_mul_of_nonneg_right hn0le hfac
        calc (n₀ : ℝ)*(stationaryBadBranchConstant*C/E^2)
            ≤ (8*L+2)*(stationaryBadBranchConstant*C/E^2) := this
          _ = (8*L+2)*stationaryBadBranchConstant*C/E^2 := by ring
      linarith

theorem stationary_excess_integrable [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryMarginThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    Integrable (nativeRestartExcess E) π := by
  have hnn : 0 ≤ᵐ[π] nativeRestartExcess E :=
    Filter.Eventually.of_forall fun y => le_max_right _ _
  refine ⟨(measurable_nativeRestartExcess E).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn]
  exact lt_of_le_of_lt (stationary_excess_lintegral_le hX hi hG hE hπ) ENNReal.ofReal_lt_top

theorem stationary_excess_integral_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryMarginThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (∫ y, nativeRestartExcess E y ∂π) ≤
      stationaryMarginMomentConstant +
        ((8*Real.log E+2)*stationaryBadBranchConstant +
          2*Real.exp 1*stationaryGeomExpSum)*
            (∫ x, nativeRestartMean X μ E x ∂π)/E^2 := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEnum : (5120000 : ℝ) ≤ E := by simpa [stationaryMarginThreshold] using hE
  have hEpos : (0 : ℝ) < E := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hC1 : 1 ≤ ∫ x, nativeRestartMean X μ E x ∂π :=
    one_le_stationary_mean hX hi hG hEpos
  have hL0 : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hnn : 0 ≤ᵐ[π] nativeRestartExcess E :=
    Filter.Eventually.of_forall fun y => le_max_right _ _
  have hbound0 : 0 ≤ stationaryMarginMomentConstant +
      ((8*Real.log E+2)*stationaryBadBranchConstant +
        2*Real.exp 1*stationaryGeomExpSum)*
          (∫ x, nativeRestartMean X μ E x ∂π)/E^2 := by
    have h1 := stationaryMarginMomentConstant_nonneg
    have h2 := stationaryBadBranchConstant_pos
    have h3 := stationaryGeomExpSum_pos
    have h4 : (0 : ℝ) ≤ ∫ x, nativeRestartMean X μ E x ∂π := by linarith
    have hnum : 0 ≤ ((8*Real.log E+2)*stationaryBadBranchConstant +
        2*Real.exp 1*stationaryGeomExpSum) := by positivity
    have : 0 ≤ ((8*Real.log E+2)*stationaryBadBranchConstant +
        2*Real.exp 1*stationaryGeomExpSum)*(∫ x, nativeRestartMean X μ E x ∂π)/E^2 :=
      div_nonneg (mul_nonneg hnum h4) (by positivity)
    linarith
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    (measurable_nativeRestartExcess E).aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (stationary_excess_lintegral_le hX hi hG hE hπ)
  rwa [ENNReal.toReal_ofReal hbound0] at h

end SwingRepair
