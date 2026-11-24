import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Cesaro convolution limits and the symmetric ladder-height mean identity. -/
noncomputable section
open Filter Finset
open scoped Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The finite convolution normalized by its number of summands. -/
def ladderCesaroConvolution (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n+1), f k*g (n-k))/((n : ℝ)+1)

theorem ladderCesaroConvolution_tendsto_zero
    {f g : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C)
    (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (ladderCesaroConvolution f g) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hf 0)
  have havg : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹*
      ∑ k ∈ Finset.range (n+1), |g k|) atTop (𝓝 0) := by
    have hh := (hg.abs.cesaro).comp (tendsto_add_atTop_nat 1)
    simpa only [abs_zero, Nat.cast_add, Nat.cast_one, Function.comp_def] using hh
  have hlim := havg.const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm _ hlim
  intro n
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hsum : |∑ k ∈ Finset.range (n+1), f k*g (n-k)| ≤
      C*∑ k ∈ Finset.range (n+1), |g k| := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n+1), |f k*g (n-k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (n+1), C*|g (n-k)| := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hf k) (abs_nonneg _)
      _ = C*∑ k ∈ Finset.range (n+1), |g k| := by
        rw [← Finset.mul_sum]
        congr 1
        simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun k => |g k|) (n+1)
  rw [Real.norm_eq_abs, ladderCesaroConvolution, abs_div, abs_of_pos hn]
  calc
    _ ≤ (C*∑ k ∈ Finset.range (n+1), |g k|)/((n : ℝ)+1) :=
      div_le_div_of_nonneg_right hsum hn.le
    _ = _ := by ring

/-- A bounded convergent sequence has the square of its limit as its Cesaro
convolution limit. No summability of the sequence is required. -/
theorem ladderCesaroConvolution_self_tendsto
    {e : ℕ → ℝ} {M m : ℝ} (heM : ∀ n, |e n| ≤ M)
    (he : Tendsto e atTop (𝓝 m)) :
    Tendsto (ladderCesaroConvolution e e) atTop (𝓝 (m^2)) := by
  have hdiff : Tendsto (fun n => e n-m) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr he
  have hleft := ladderCesaroConvolution_tendsto_zero heM hdiff
  have hright := ladderCesaroConvolution_tendsto_zero (f := fun _ => m)
    (C := |m|) (fun _ => le_rfl) hdiff
  have hadd := hleft.add hright
  simp only [add_zero] at hadd
  apply tendsto_sub_nhds_zero_iff.mp
  refine hadd.congr (fun n => ?_)
  unfold ladderCesaroConvolution
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hrev : (∑ k ∈ Finset.range (n+1), m*(e (n-k)-m)) =
      ∑ k ∈ Finset.range (n+1), m*(e k-m) := by
    simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun k => m*(e k-m)) (n+1)
  rw [hrev]
  field_simp
  rw [← Finset.sum_add_distrib]
  have hterms : (∑ k ∈ Finset.range (n+1), (e k*(e (n-k)-m)+m*(e k-m))) =
      (∑ k ∈ Finset.range (n+1), e k*e (n-k))-((n : ℝ)+1)*m^2 := by
    calc
      _ = ∑ k ∈ Finset.range (n+1), (e k*e (n-k)-m^2) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by simp [Finset.sum_sub_distrib, mul_comm]
  nlinarith only [hterms]

/-- The scalar renewal/Wald identity forces the ladder mean square to be 1/2. -/
theorem ladder_mean_sq_of_convolution_identity
    {e d q : ℕ → ℝ} {M C m : ℝ}
    (heM : ∀ n, |e n| ≤ M) (he : Tendsto e atTop (𝓝 m))
    (hdC : ∀ n, |d n| ≤ C) (hq : Tendsto q atTop (𝓝 0))
    (hid : ∀ n : ℕ, 2*((∑ k ∈ Finset.range (n+1), e k*e (n-k))+
      (∑ k ∈ Finset.range (n+1), d k*q (n-k))) = (n : ℝ)) :
    m^2 = 1/2 := by
  have hconv := ((ladderCesaroConvolution_self_tendsto heM he).add
    (ladderCesaroConvolution_tendsto_zero hdC hq)).const_mul 2
  simp only [add_zero] at hconv
  have heq : (fun n : ℕ => 2*(ladderCesaroConvolution e e n+ladderCesaroConvolution d q n)) =
      (fun n : ℕ => (n : ℝ)/((n : ℝ)+1)) := by
    funext n
    unfold ladderCesaroConvolution
    rw [← add_div, ← mul_div_assoc, hid]
  rw [heq] at hconv
  have hh := tendsto_nhds_unique hconv (tendsto_natCast_div_add_atTop (1 : ℝ))
  linarith

/-- The nonnegative symmetric ladder mean is exactly 1/sqrt(2). -/
theorem ladder_mean_eq_inv_sqrt_two_of_convolution_identity
    {e d q : ℕ → ℝ} {M C m : ℝ}
    (heM : ∀ n, |e n| ≤ M) (he : Tendsto e atTop (𝓝 m))
    (hdC : ∀ n, |d n| ≤ C) (hq : Tendsto q atTop (𝓝 0))
    (hid : ∀ n : ℕ, 2*((∑ k ∈ Finset.range (n+1), e k*e (n-k))+
      (∑ k ∈ Finset.range (n+1), d k*q (n-k))) = (n : ℝ))
    (hm : 0 ≤ m) : m = 1/Real.sqrt 2 := by
  have hsq := ladder_mean_sq_of_convolution_identity heM he hdC hq hid
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  apply (eq_div_iff hs.ne').mpr
  have hmul : (m*Real.sqrt 2)^2 = 1 := by rw [mul_pow, hsq, hs2]; norm_num
  nlinarith [mul_nonneg hm hs.le]

/-- Summing one factor before convolving integrates the constant convolution. -/
theorem ladder_prefix_convolution_eq_index {q : ℕ → ℝ}
    (hq : ∀ n : ℕ, (∑ k ∈ Finset.range (n+1), q k*q (n-k)) = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (∑ j ∈ Finset.range k, q j)*q (n-k)) = (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Finset.sum_range_zero, zero_mul, add_zero, Nat.add_sub_add_right]
    have hterm (k : ℕ) : (∑ j ∈ Finset.range (k+1), q j)*q (n-k) =
        (∑ j ∈ Finset.range k, q j)*q (n-k)+q k*q (n-k) := by
      rw [Finset.sum_range_succ, add_mul]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ih, hq]
    simp

/-- The finite Wald and minimum-decomposition identities give exactly the
scalar identity used in the Cesaro limit argument. -/
theorem ladder_convolution_identity_of_wald {q a d e : ℕ → ℝ}
    (hq : ∀ n : ℕ, (∑ k ∈ Finset.range (n+1), q k*q (n-k)) = 1)
    (ha : ∀ k, a k = (∑ j ∈ Finset.range k, q j)-d k)
    (hid : ∀ n : ℕ, (n : ℝ) =
      2*(∑ k ∈ Finset.range (n+1), a k*q (n-k))-
      2*(∑ k ∈ Finset.range (n+1), e k*e (n-k))) :
    ∀ n : ℕ, 2*((∑ k ∈ Finset.range (n+1), e k*e (n-k))+
      (∑ k ∈ Finset.range (n+1), d k*q (n-k))) = (n : ℝ) := by
  intro n
  have hconv : (∑ k ∈ Finset.range (n+1), a k*q (n-k)) =
      (n : ℝ)-(∑ k ∈ Finset.range (n+1), d k*q (n-k)) := by
    simp_rw [ha, sub_mul]
    rw [Finset.sum_sub_distrib, ladder_prefix_convolution_eq_index hq n]
  have hh := hid n
  rw [hconv] at hh
  linarith

end SwingRepair
