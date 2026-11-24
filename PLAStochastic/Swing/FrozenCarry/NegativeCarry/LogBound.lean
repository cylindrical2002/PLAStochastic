import PLAStochastic.Swing.FrozenCarry.NegativeCarry.LargeCarryBound
import PLAStochastic.Swing.FrozenCarry.NegativeCarry.HarmonicInterval

/-! # Lemma H.1: the negative-carry conditional mean

`g_E(-c) ≤ C E (1+log_+(1/c))` for every `c>0`, uniformly in the budget.
Three ranges are combined: a coarse endpoint-geometric bound for `c ≥ 1`, a
harmonic head with an endpoint-geometric tail for the intermediate range, and
the uniform `E log(eE)` bound for carries so small that the logarithm on the
right already dominates.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

def frozenNegativeCarryLogConstant : ℝ :=
  48+frozenHarmonicTailConstant+2*frozenUniformMeanConstant

theorem frozenNegativeCarryLogConstant_pos : 0 < frozenNegativeCarryLogConstant := by
  have h₁ := frozenHarmonicTailConstant_pos
  have h₂ := frozenUniformMeanConstant_pos
  unfold frozenNegativeCarryLogConstant
  positivity

/-- The intermediate range: the head is harmonic above the linear scale and the
endpoint-geometric remainder is already `O(E)`. -/
theorem frozenPrefixLength_negative_mean_middle_c
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c E : ℝ} (hc : 0 < c) (hc1 : c < 1) (hE : 16 ≤ E) (hcE : (Real.sqrt E)⁻¹ ≤ c) :
    (∫ ω, frozenPrefixLengthReal X (-c) E ω ∂μ) ≤
      (23+frozenHarmonicTailConstant)*E*(1+Real.log (1/c)) := by
  have := hi.isProbabilityMeasure
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hEp : (0 : ℝ) < E := by linarith
  have hmax : max (-c) 0 = 0 := max_eq_right (by linarith)
  have hlog : 0 ≤ Real.log (1/c) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  set m : ℕ := ⌈4*E/c⌉₊ with hmdef
  set k : ℕ := ⌈4*E⌉₊ with hkdef
  have hmpos : 0 < m := Nat.ceil_pos.mpr (by positivity)
  have hcut : 4*E ≤ c*(m : ℝ) := by
    have hceil : 4*E/c ≤ (m : ℝ) := Nat.le_ceil _
    have := (div_le_iff₀ hc).mp hceil
    linarith
  have hkr : (4 : ℝ)*E ≤ (k : ℝ) := Nat.le_ceil _
  have hkr' : (k : ℝ) < 4*E+1 := Nat.ceil_lt_add_one (by positivity)
  have hmr : (m : ℝ) < 4*E/c+1 := Nat.ceil_lt_add_one (by positivity)
  have hmr' : 4*E/c ≤ (m : ℝ) := Nat.le_ceil _
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hkm : k ≤ m := by
    have hle : (4 : ℝ)*E ≤ 4*E/c := by
      rw [le_div_iff₀ hc]
      nlinarith
    exact Nat.ceil_le_ceil hle
  -- the head window stays below the bridge horizon
  have hsqrt : Real.sqrt E ≤ E/4 := by
    have h1 : E ≤ (E/4)^2 := by nlinarith
    have h2 : Real.sqrt E ≤ Real.sqrt ((E/4)^2) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ E/4)] at h2
  have hinvc : 1/c ≤ Real.sqrt E := by
    have hs : 0 < Real.sqrt E := Real.sqrt_pos.mpr (by linarith)
    have h1 : 1 ≤ c*Real.sqrt E := by
      have hm := mul_le_mul_of_nonneg_right hcE hs.le
      rwa [inv_mul_cancel₀ hs.ne'] at hm
    rw [div_le_iff₀ hc]
    nlinarith [h1]
  have hmE : (m : ℝ) ≤ E^2+1 := by
    have hdiv : 4*E/c = 4*E*(1/c) := by ring
    have hle : 4*E/c ≤ 4*E*Real.sqrt E := by
      rw [hdiv]
      exact mul_le_mul_of_nonneg_left hinvc (by linarith)
    nlinarith [hsqrt, hmr]
  -- weighted head decomposition
  have hsplit := frozenPrefixLength_negative_mean_weighted_head hX hi hG hc hEp hmpos hcut
  have hq : Real.exp (-(c^2)/8) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [sq_pos_of_pos hc])
  have hqpos : 0 < 1-Real.exp (-(c^2)/8) := by linarith
  have hpow : Real.exp (-(c^2)/8)^m ≤ 1 := pow_le_one₀ (Real.exp_pos _).le hq.le
  have hden := negativeCarry_geometric_denominator hc
  have hinvc2 : 8/c^2 ≤ 8*E := by
    have hs : Real.sqrt E ^ 2 = E := Real.sq_sqrt (by linarith)
    have hcc : 1/c^2 ≤ E := by
      have h1 : (1/c)^2 ≤ (Real.sqrt E)^2 := by
        apply pow_le_pow_left₀ (by positivity) hinvc
      rw [hs] at h1
      calc 1/c^2 = (1/c)^2 := by rw [div_pow, one_pow]
        _ ≤ E := h1
    have h8 : 8/c^2 = 8*(1/c^2) := by ring
    rw [h8]
    linarith
  have htail : 2*Real.exp (-(c^2)/8)^m/(1-Real.exp (-(c^2)/8)) ≤ 18*E := by
    calc
      _ ≤ 2/(1-Real.exp (-(c^2)/8)) := by gcongr; simpa using hpow
      _ ≤ 2*(1+8/c^2) := by
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ 18*E := by linarith
  -- head: trivial below the linear scale, harmonic above it
  have hheadsplit : (∑ j ∈ Finset.range m, μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0}) =
      (∑ j ∈ Finset.range k, μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0})+
      (∑ j ∈ Finset.Ico k m, μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0}) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) hkm]
  have htriv : (∑ j ∈ Finset.range k, μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0}) ≤
      (k : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum (fun j _ => measureReal_le_one)
      _ = (k : ℝ) := by simp
  have hharm := frozenPrefixLength_harmonic_interval hX hi hG (-c) hE1 hk1 hkm hmE
  rw [hmax] at hharm
  have hratio : (m : ℝ)/(k : ℝ) ≤ 2*(1/c) := by
    have hkpos : (0 : ℝ) < k := by linarith
    rw [div_le_iff₀ hkpos]
    have hone : (1 : ℝ) ≤ 4*E := by linarith
    have hcc : (1 : ℝ) ≤ 1/c := by rw [le_div_iff₀ hc]; linarith
    have hstep : 4*E/c+1 ≤ 2*(1/c)*(4*E) := by
      have h1 : 4*E/c = (1/c)*(4*E) := by field_simp
      nlinarith [hcc, hone]
    nlinarith [hmr, hkr]
  have hlogratio : Real.log ((m : ℝ)/(k : ℝ)) ≤ 1+Real.log (1/c) := by
    have hpos : (0 : ℝ) < (m : ℝ)/(k : ℝ) := by
      have hkpos : (0 : ℝ) < k := by linarith
      have hmpos' : (0 : ℝ) < m := by
        have : (0 : ℝ) < 4*E/c := by positivity
        linarith [hmr']
      positivity
    have h2 : Real.log ((m : ℝ)/(k : ℝ)) ≤ Real.log (2*(1/c)) :=
      Real.log_le_log hpos hratio
    have h3 : Real.log (2*(1/c)) = Real.log 2+Real.log (1/c) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    have h4 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    linarith
  have hC := frozenHarmonicTailConstant_pos
  have hharm' : (∑ j ∈ Finset.Ico k m, μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0}) ≤
      frozenHarmonicTailConstant*E*(1+Real.log (1/c)) := by
    refine hharm.trans ?_
    have : frozenHarmonicTailConstant*(1+(0:ℝ))*E = frozenHarmonicTailConstant*E := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hlogratio (by positivity)
  have hkE : (k : ℝ) ≤ 5*E := by linarith
  have hlog1 : (1 : ℝ) ≤ 1+Real.log (1/c) := by linarith
  calc
    _ ≤ (∑ j ∈ Finset.range m, μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0})+
        2*Real.exp (-(c^2)/8)^m/(1-Real.exp (-(c^2)/8)) := hsplit
    _ ≤ ((k : ℝ)+frozenHarmonicTailConstant*E*(1+Real.log (1/c)))+18*E := by
      rw [hheadsplit]
      exact add_le_add (add_le_add htriv hharm') htail
    _ ≤ (23+frozenHarmonicTailConstant)*E*(1+Real.log (1/c)) := by nlinarith

/-- Lemma H.1 (`eq:secondnegativemean`): the actual conditional mean at a negative
carry `-c` is at most `C E (1+log_+(1/c))`, uniformly in the budget. -/
theorem frozenPrefixLength_negative_mean_log_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c E : ℝ} (hc : 0 < c) (hE : 16 ≤ E) :
    (∫ ω, frozenPrefixLengthReal X (-c) E ω ∂μ) ≤
      frozenNegativeCarryLogConstant*E*(1+max (Real.log (1/c)) 0) := by
  have := hi.isProbabilityMeasure
  have hE1 : (1 : ℝ) ≤ E := by linarith
  have hEp : (0 : ℝ) < E := by linarith
  have hCh := frozenHarmonicTailConstant_pos
  have hCu := frozenUniformMeanConstant_pos
  have hmaxnn : 0 ≤ max (Real.log (1/c)) 0 := le_max_right _ _
  have hone : (1 : ℝ) ≤ 1+max (Real.log (1/c)) 0 := by linarith
  rcases le_or_gt 1 c with hc1 | hc1
  · -- large carry: the coarse endpoint-geometric bound already gives `O(E)`
    refine (frozenPrefixLength_negative_mean_large_c hX hi hG hc1 hE1).trans ?_
    have hbig : (25 : ℝ)*E ≤ frozenNegativeCarryLogConstant*E := by
      have : (25 : ℝ) ≤ frozenNegativeCarryLogConstant := by
        unfold frozenNegativeCarryLogConstant
        linarith
      nlinarith
    nlinarith
  · have hlogpos : 0 < Real.log (1/c) := Real.log_pos (by rw [lt_div_iff₀ hc]; linarith)
    have hmaxeq : max (Real.log (1/c)) 0 = Real.log (1/c) := max_eq_left hlogpos.le
    rcases le_or_gt (Real.sqrt E)⁻¹ c with hcE | hcE
    · -- intermediate carries
      refine (frozenPrefixLength_negative_mean_middle_c hX hi hG hc hc1 hE hcE).trans ?_
      rw [hmaxeq]
      have hle : (23 : ℝ)+frozenHarmonicTailConstant ≤ frozenNegativeCarryLogConstant := by
        unfold frozenNegativeCarryLogConstant
        linarith
      have hfac : 0 ≤ E*(1+Real.log (1/c)) := by nlinarith
      nlinarith
    · -- very small carries: the uniform bound is already dominated
      have huni := frozenPrefixLength_uniform_mean_bound hX hi hG (-c) hE1
      have hmaxw : max (-c) 0 = 0 := max_eq_right (by linarith)
      rw [hmaxw] at huni
      have hlogE : Real.log (Real.exp 1*E) = 1+Real.log E := by
        rw [Real.log_mul (Real.exp_ne_zero 1) (by linarith), Real.log_exp]
      rw [hlogE] at huni
      have hsq : Real.log (Real.sqrt E) = Real.log E/2 := Real.log_sqrt (by linarith)
      have hcomp : Real.log E/2 ≤ Real.log (1/c) := by
        have hs : 0 < Real.sqrt E := Real.sqrt_pos.mpr (by linarith)
        have hlt : Real.sqrt E < 1/c := by
          rw [lt_div_iff₀ hc]
          have hm := mul_lt_mul_of_pos_right hcE hs
          rwa [inv_mul_cancel₀ hs.ne', mul_comm] at hm
        have := Real.log_le_log hs hlt.le
        linarith [hsq ▸ this]
      rw [hmaxeq]
      have huni' : (∫ ω, frozenPrefixLengthReal X (-c) E ω ∂μ) ≤
          frozenUniformMeanConstant*E*(1+Real.log E) := by
        simpa only [add_zero, mul_one] using huni
      have hCE : (0 : ℝ) ≤ frozenUniformMeanConstant*E := by positivity
      have hstep : frozenUniformMeanConstant*E*(1+Real.log E) ≤
          frozenUniformMeanConstant*E*(1+2*Real.log (1/c)) :=
        mul_le_mul_of_nonneg_left (by linarith) hCE
      have hfinal : frozenUniformMeanConstant*E*(1+2*Real.log (1/c)) ≤
          2*frozenUniformMeanConstant*E*(1+Real.log (1/c)) := by
        have hdiff : 2*frozenUniformMeanConstant*E*(1+Real.log (1/c))-
            frozenUniformMeanConstant*E*(1+2*Real.log (1/c)) = frozenUniformMeanConstant*E := by
          ring
        linarith
      have hle : 2*frozenUniformMeanConstant ≤ frozenNegativeCarryLogConstant := by
        unfold frozenNegativeCarryLogConstant
        linarith
      have hfac : (0 : ℝ) ≤ E*(1+Real.log (1/c)) := by positivity
      have hlast : 2*frozenUniformMeanConstant*E*(1+Real.log (1/c)) ≤
          frozenNegativeCarryLogConstant*E*(1+Real.log (1/c)) := by
        have h1 : 2*frozenUniformMeanConstant*E*(1+Real.log (1/c)) =
            (2*frozenUniformMeanConstant)*(E*(1+Real.log (1/c))) := by ring
        have h2 : frozenNegativeCarryLogConstant*E*(1+Real.log (1/c)) =
            frozenNegativeCarryLogConstant*(E*(1+Real.log (1/c))) := by ring
        rw [h1, h2]
        exact mul_le_mul_of_nonneg_right hle hfac
      exact huni'.trans (hstep.trans (hfinal.trans hlast))

end SwingRepair
