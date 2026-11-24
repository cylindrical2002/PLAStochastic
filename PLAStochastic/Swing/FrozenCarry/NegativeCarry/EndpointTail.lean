import PLAStochastic.Swing.FrozenCarry.DurationTail.UniformMeanBound
import PLAStochastic.Swing.FrozenCarry.Interior.GoodTail

/-! Endpoint Gaussian tails for negative carries, retaining the true maximal prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

omit mΩ in
/-- The first and last cone constraints alone force a negative Gaussian endpoint. -/
theorem frozenPrefixLength_negative_endpoint {c E : ℝ} {n : ℕ} {ω : Ω}
    (h : ((n+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X (-c) E ω) :
    cumulativeSamples X n ω ≤ 2*E-c*(n : ℝ) := by
  have hh := frozenBridgeStart_nonneg_of_feasible h
  dsimp [frozenBridgeStart] at hh
  have hp : (0 : ℝ) < (n : ℝ)+1 := by positivity
  have hd := (div_le_iff₀ hp).mp (show (-c+cumulativeSamples X n ω-2*E)/((n : ℝ)+1) ≤ -c by linarith)
  nlinarith

/-- Beyond the linear negative-carry cutoff the tail is genuinely Gaussian. -/
theorem frozenPrefixLength_negative_geometric_tail
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c E : ℝ} (hc : 0 < c) {n : ℕ} (hn : 0 < n) (hcut : 4*E ≤ c*(n : ℝ)) :
    μ.real {ω | ((n+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X (-c) E ω} ≤
      2*Real.exp (-(c^2)/8)^n := by
  have := hi.isProbabilityMeasure
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : {ω | ((n+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X (-c) E ω} ⊆
      {ω | c*(n : ℝ)/2 ≤ |cumulativeSamples X n ω|} := by
    intro ω hω
    have hh := frozenPrefixLength_negative_endpoint hω
    have ha := neg_le_abs (cumulativeSamples X n ω)
    change c*(n : ℝ)/2 ≤ |cumulativeSamples X n ω|
    linarith
  refine (measureReal_mono hs).trans ((cumulativeSamples_abs_tail_bound hX hi hG n
    (show 0 ≤ c*(n : ℝ)/2 by positivity)).trans_eq ?_)
  rw [← Real.exp_nat_mul]
  congr 2
  field_simp
  ring

/-- The elementary geometric denominator is uniform in the carry parameter. -/
theorem negativeCarry_geometric_denominator {c : ℝ} (hc : 0 < c) :
    (1-Real.exp (-(c^2)/8))⁻¹ ≤ 1+8/c^2 := by
  let a := c^2/8
  have ha : 0 < a := by dsimp [a]; positivity
  have he : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hprod : 1 ≤ (1-Real.exp (-a))*(1+a⁻¹) := by
    have hh := Real.add_one_le_exp a
    have hei : Real.exp (-a)*Real.exp a = 1 := by rw [← Real.exp_add]; simp
    have hl := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-a)).le
    rw [hei] at hl
    have har : a*a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
    nlinarith [mul_le_mul_of_nonneg_right hl (inv_nonneg.mpr ha.le)]
  have hh : (1-Real.exp (-a))⁻¹ ≤ 1+a⁻¹ := by
    rw [inv_eq_one_div, div_le_iff₀ (sub_pos.mpr he)]
    nlinarith [hprod]
  simpa only [a, neg_div, inv_div, inv_pow, one_div] using hh

/-- A harmonic finite head can be followed by a fresh endpoint geometric tail. -/
theorem frozenPrefixLength_negative_mean_weighted_head
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c E : ℝ} (hc : 0 < c) (hE : 0 < E) {m : ℕ} (hm : 0 < m)
    (hcut : 4*E ≤ c*(m : ℝ)) :
    (∫ ω, frozenPrefixLengthReal X (-c) E ω ∂μ) ≤
      (∑ j ∈ Finset.range m, μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0})+
      2*Real.exp (-(c^2)/8)^m/(1-Real.exp (-(c^2)/8)) := by
  have := hi.isProbabilityMeasure
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(c^2)/8))
  have hq : q < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hc]))
  have htail (k : ℕ) : μ {ω | 1*k < (frozenPrefixLength X (-c) E ω).untopD 0-m} ≤
      ((2 : ℝ≥0∞)*q^m)*q^k := by
    have hs : {ω | 1*k < (frozenPrefixLength X (-c) E ω).untopD 0-m} ⊆
        {ω | ((m+k+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X (-c) E ω} := by
      intro ω hω
      apply frozenPrefixLength_nat_tail_subset X (-c) E (m+k)
      change m+k < (frozenPrefixLength X (-c) E ω).untopD 0
      simp only [Set.mem_ofPred_eq, one_mul] at hω
      omega
    have hbound := frozenPrefixLength_negative_geometric_tail hX hi hG hc
      (show 0 < m+k by omega) (hcut.trans (by gcongr; exact_mod_cast Nat.le_add_right m k))
    have hr : μ.real {ω | 1*k < (frozenPrefixLength X (-c) E ω).untopD 0-m} ≤
        2*Real.exp (-(c^2)/8)^(m+k) := (measureReal_mono hs).trans hbound
    have hh := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_pow (Real.exp_pos _).le, pow_add] at hh
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (Real.exp_pos _).le, pow_add, ← mul_assoc, q] using hh
  have hh := integral_natCast_le_head_add_weighted_tail
    ((frozenPrefixLength_measurable hX (-c) E).untopD 0)
    (frozenPrefixLengthReal_integrable hX hi hG (-c) hE) m (by omega : 0 < 1) hq
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by simp [q])) : (2 : ℝ≥0∞)*q^m ≠ ⊤) htail
  have he : q.toReal = Real.exp (-(c^2)/8) := ENNReal.toReal_ofReal (Real.exp_pos _).le
  simpa only [Nat.cast_one, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, one_mul, he, frozenPrefixLengthReal] using hh

/-- A simpler unweighted form is useful for carries bounded away from zero. -/
theorem frozenPrefixLength_negative_mean_head
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c E : ℝ} (hc : 0 < c) (hE : 0 < E) {m : ℕ} (hm : 0 < m)
    (hcut : 4*E ≤ c*(m : ℝ)) :
    (∫ ω, frozenPrefixLengthReal X (-c) E ω ∂μ) ≤
      (∑ j ∈ Finset.range m, μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0})+
      2*(1+8/c^2) := by
  have hh := frozenPrefixLength_negative_mean_weighted_head hX hi hG hc hE hm hcut
  have he : Real.exp (-(c^2)/8) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hc])
  have hpow : Real.exp (-(c^2)/8)^m ≤ 1 := pow_le_one₀ (Real.exp_pos (-(c^2)/8)).le he.le
  have hq : 0 < 1-Real.exp (-(c^2)/8) := by linarith
  have htail : 2*Real.exp (-(c^2)/8)^m/(1-Real.exp (-(c^2)/8)) ≤ 2*(1+8/c^2) := by
    calc
      _ ≤ 2/(1-Real.exp (-(c^2)/8)) := by gcongr; simpa using hpow
      _ ≤ _ := by
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left (negativeCarry_geometric_denominator hc) (by norm_num : (0 : ℝ) ≤ 2)
  linarith

end SwingRepair
