import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # The Spitzer–Baxter exponential formula from the argmax factorisation (roadmap 1.4, step 2)

Purely analytic facts about real sequences.

* `convolution_recursion`.  If `A * B = (1, 1, 1, …)` and `(n A_n) * B = P * (1, 1, …)` as
  Cauchy products with `B₀ = 1`, then `n A_n = ∑_{k ≤ n} P_k A_{n-k}`.  (Cancel `B` in `ℝ⟦X⟧`.)
* `genFun_eq_exp_of_recursion`.  If nonnegative bounded `A` and nonnegative summable `P` with
  `A₀ = 1`, `P₀ = 0` satisfy that recursion, then `F(t) = ∑ A_n tⁿ = exp(∑ (P_n/n) tⁿ)` on `[0, 1)`
  (`F' = Q' F`, so `F e^{-Q}` is constant).
* `spitzer_limit_of_factorisation`.  If moreover `B` is antitone with limit `p`, then
  `(1 - t) F_B(t) = 1/F_A(t) = exp(-Q(t))`, and the Abelian mean of `B` gives
  `p = exp(-∑ P_n/n)`.

Applied to `A_n = P(S_n > S_k ∀ k < n)`, `B_m = P(S_1 ≤ 0, …, S_m ≤ 0)`, `P_j = P(S_j > 0)` for
the drift `-a` Gaussian walk, this yields Spitzer's formula `p_a = exp(-∑ Φ(-a√j)/j)`.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace SwingRepair
namespace Fluctuation

/-! ### Cancelling the convolution -/

theorem convolution_recursion {A B P : ℕ → ℝ} (hB0 : B 0 = 1)
    (h1 : ∀ n, ∑ k ∈ Finset.range (n + 1), A k * B (n - k) = 1)
    (h2 : ∀ n, ∑ k ∈ Finset.range (n + 1), (k : ℝ) * A k * B (n - k) =
      ∑ j ∈ Finset.range (n + 1), P j) :
    ∀ n : ℕ, (n : ℝ) * A n = ∑ k ∈ Finset.range (n + 1), P k * A (n - k) := by
  classical
  set FA : PowerSeries ℝ := PowerSeries.mk A with hFA
  set FB : PowerSeries ℝ := PowerSeries.mk B with hFB
  set FP : PowerSeries ℝ := PowerSeries.mk P with hFP
  set FD : PowerSeries ℝ := PowerSeries.mk fun n => (n : ℝ) * A n with hFD
  set FU : PowerSeries ℝ := PowerSeries.mk fun _ => (1 : ℝ) with hFU
  have hAB : FA * FB = FU := by
    ext n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [hFA, hFB, hFU, PowerSeries.coeff_mk]
    exact h1 n
  have hDB : FD * FB = FP * FU := by
    ext n
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [hFD, hFB, hFP, hFU, PowerSeries.coeff_mk, mul_one]
    exact h2 n
  have hBne : FB ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff 0) h
    simp [hFB, PowerSeries.coeff_mk, hB0] at this
  have hD : FD = FP * FA := by
    apply mul_right_cancel₀ hBne
    rw [hDB, mul_assoc, hAB]
  intro n
  have := congrArg (PowerSeries.coeff n) hD
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
  simpa only [hFD, hFP, hFA, PowerSeries.coeff_mk] using this

/-! ### Generating functions of bounded nonnegative sequences -/

section GenFun

variable {A P : ℕ → ℝ} {C : ℝ}

/-- The generating function `F(t) = ∑ A_n tⁿ`. -/
def genFun (A : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n, A n * t ^ n

theorem summable_coeff_mul_pow (hAnn : ∀ n, 0 ≤ A n) (hAb : ∀ n, A n ≤ C) {t : ℝ} (ht : |t| < 1) :
    Summable fun n => A n * t ^ n := by
  refine Summable.of_norm_bounded (g := fun n => C * |t| ^ n) ?_ fun n => ?_
  · exact (summable_geometric_of_lt_one (abs_nonneg t) ht).mul_left _
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (hAnn n)]
    exact mul_le_mul_of_nonneg_right (hAb n) (pow_nonneg (abs_nonneg t) n)

theorem genFun_zero (A : ℕ → ℝ) : genFun A 0 = A 0 := by
  unfold genFun
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

theorem genFun_nonneg (hAnn : ∀ n, 0 ≤ A n) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ genFun A t :=
  tsum_nonneg fun n => mul_nonneg (hAnn n) (pow_nonneg ht n)

/-- The dominating series `C/r · n rⁿ` for the derivative. -/
theorem summable_deriv_dominant {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (C : ℝ) :
    Summable fun n : ℕ => C / r * ((n : ℝ) * r ^ n) := by
  have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
    (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  simpa [pow_one] using this.mul_left (C / r)

theorem deriv_term_le (hAnn : ∀ n, 0 ≤ A n) (hAb : ∀ n, A n ≤ C) {r y : ℝ} (hr0 : 0 < r)
    (hy : |y| ≤ r) (n : ℕ) :
    ‖A n * ((n : ℝ) * y ^ (n - 1))‖ ≤ C / r * ((n : ℝ) * r ^ n) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hAnn n), abs_mul, abs_pow, Nat.abs_cast]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hC0 : 0 ≤ C := (hAnn 0).trans (hAb 0)
    have hy' : |y| ^ (n - 1) ≤ r ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg y) hy _
    have hrn : r ^ n = r * r ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hA := hAb n
    calc A n * ((n : ℝ) * |y| ^ (n - 1)) ≤ C * ((n : ℝ) * r ^ (n - 1)) := by gcongr
      _ = C / r * ((n : ℝ) * r ^ n) := by rw [hrn]; field_simp

/-- Derivative of the generating function inside the unit disc. -/
theorem hasDerivAt_genFun (hAnn : ∀ n, 0 ≤ A n) (hAb : ∀ n, A n ≤ C) {t : ℝ} (ht : |t| < 1) :
    HasDerivAt (genFun A) (∑' n, A n * ((n : ℝ) * t ^ (n - 1))) t := by
  set r : ℝ := (|t| + 1) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have htr : |t| < r := by rw [hr]; linarith
  have hopen : IsOpen (Metric.ball (0 : ℝ) r) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) r) := (convex_ball 0 r).isPreconnected
  refine hasDerivAt_tsum_of_isPreconnected (g := fun n t => A n * t ^ n)
    (g' := fun n t => A n * ((n : ℝ) * t ^ (n - 1))) (summable_deriv_dominant hr0 hr1 C)
    hopen hconn ?_ ?_ (y₀ := 0) ?_ ?_ ?_
  · intro n y _
    exact (hasDerivAt_pow n y).const_mul (A n)
  · intro n y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    exact deriv_term_le hAnn hAb hr0 hy.le n
  · exact Metric.mem_ball_self hr0
  · simpa using (summable_coeff_mul_pow hAnn hAb (t := 0) (by simp)).congr (fun n => by ring)
  · rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact htr

/-- The shifted-index form of the derivative series. -/
theorem tsum_deriv_shift (hAnn : ∀ n, 0 ≤ A n) (hAb : ∀ n, A n ≤ C) {t : ℝ} (ht : |t| < 1) :
    ∑' n, A n * ((n : ℝ) * t ^ (n - 1)) = ∑' n : ℕ, ((n : ℝ) + 1) * A (n + 1) * t ^ n := by
  have hs : Summable fun n => A n * ((n : ℝ) * t ^ (n - 1)) := by
    set r : ℝ := (|t| + 1) / 2 with hr
    have hr0 : 0 < r := by rw [hr]; positivity
    have hr1 : r < 1 := by rw [hr]; linarith
    have htr : |t| < r := by rw [hr]; linarith
    exact Summable.of_norm_bounded (summable_deriv_dominant hr0 hr1 C)
      (deriv_term_le hAnn hAb hr0 htr.le)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.cast_add, Nat.cast_one,
    Nat.add_sub_cancel]
  refine tsum_congr fun n => ?_
  ring

/-- **Exponential formula on `[0, 1)`.** -/
theorem genFun_eq_exp_of_recursion (hA0 : A 0 = 1) (hAnn : ∀ n, 0 ≤ A n) (hAb : ∀ n, A n ≤ C)
    (hPnn : ∀ n, 0 ≤ P n) (hP0 : P 0 = 0) (hPs : Summable P)
    (hrec : ∀ n : ℕ, (n : ℝ) * A n = ∑ k ∈ Finset.range (n + 1), P k * A (n - k))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    genFun A t = Real.exp (genFun (fun n => P n / n) t) := by
  set q : ℕ → ℝ := fun n => P n / n with hq
  have hqnn : ∀ n, 0 ≤ q n := fun n => div_nonneg (hPnn n) (Nat.cast_nonneg n)
  have hqle : ∀ n, q n ≤ P n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hq, hP0]
    · simp only [hq]
      rw [div_le_iff₀ (by exact_mod_cast hn)]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [hPnn n]
  have hqs : Summable q := Summable.of_nonneg_of_le hqnn hqle hPs
  have hqb : ∀ n, q n ≤ ∑' m, q m := fun n => hqs.le_tsum n fun m _ => hqnn m
  have hq0 : q 0 = 0 := by simp [hq, hP0]
  -- `F' = Q' F` on `(-1, 1)`
  have hderiv : ∀ t : ℝ, |t| < 1 →
      HasDerivAt (fun s => genFun A s * Real.exp (-genFun q s)) 0 t := by
    intro t ht
    have hF := hasDerivAt_genFun hAnn hAb ht
    have hQ := hasDerivAt_genFun hqnn hqb ht
    have hFQ := hF.mul (hQ.neg.exp)
    have hkey : (∑' n, A n * ((n : ℝ) * t ^ (n - 1))) =
        (∑' n, q n * ((n : ℝ) * t ^ (n - 1))) * genFun A t := by
      rw [tsum_deriv_shift hAnn hAb ht, tsum_deriv_shift hqnn hqb ht]
      have hq' : ∀ n : ℕ, ((n : ℝ) + 1) * q (n + 1) = P (n + 1) := by
        intro n
        simp only [hq]
        rw [Nat.cast_succ]
        field_simp
      simp_rw [hq']
      unfold genFun
      have hsP : Summable fun n => ‖P (n + 1) * t ^ n‖ := by
        refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
          ((summable_nat_add_iff 1).mpr hPs)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hPnn _), abs_pow]
        exact mul_le_of_le_one_right (hPnn _) (pow_le_one₀ (abs_nonneg t) ht.le)
      have hsA : Summable fun n => ‖A n * t ^ n‖ :=
        (summable_coeff_mul_pow hAnn hAb ht).abs
      rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsP hsA]
      refine tsum_congr fun n => ?_
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => P (i + 1) * t ^ i * (A j * t ^ j))]
      have hrec' := hrec (n + 1)
      rw [Finset.sum_range_succ', hP0, zero_mul, add_zero] at hrec'
      simp only [Nat.add_sub_add_right] at hrec'
      rw [Nat.cast_succ] at hrec'
      rw [hrec', Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : t ^ k * t ^ (n - k) = t ^ n := by rw [← pow_add, Nat.add_sub_cancel' hk']
      calc P (k + 1) * A (n - k) * t ^ n = P (k + 1) * A (n - k) * (t ^ k * t ^ (n - k)) := by
            rw [this]
        _ = P (k + 1) * t ^ k * (A (n - k) * t ^ (n - k)) := by ring
    refine hFQ.congr_deriv ?_
    rw [hkey]
    simp only [Pi.neg_apply]
    ring
  -- `F · exp(-Q)` is constant on `[0, 1)`, equal to `1`
  have hconst : genFun A t * Real.exp (-genFun q t) = 1 := by
    have hcont : ContinuousOn (fun s => genFun A s * Real.exp (-genFun q s)) (Set.Icc 0 t) := by
      intro s hs
      exact (hderiv s (by rw [abs_of_nonneg hs.1]; exact lt_of_le_of_lt hs.2 ht1))
        |>.continuousAt.continuousWithinAt
    have h := constant_of_has_deriv_right_zero hcont (fun s hs =>
      (hderiv s (by rw [abs_of_nonneg hs.1]; exact lt_of_lt_of_le hs.2 ht1.le)).hasDerivWithinAt)
      t ⟨ht0, le_rfl⟩
    rw [h, genFun_zero, genFun_zero, hA0, hq0]
    simp
  have hpos : Real.exp (-genFun q t) ≠ 0 := (Real.exp_pos _).ne'
  calc genFun A t = genFun A t * Real.exp (-genFun q t) * Real.exp (genFun q t) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = Real.exp (genFun q t) := by rw [hconst, one_mul]

/-- Abel's theorem for the generating function of a summable sequence. -/
theorem tendsto_genFun_nhdsWithin_lt (hAs : Summable A) :
    Tendsto (genFun A) (𝓝[<] 1) (𝓝 (∑' n, A n)) :=
  Real.tendsto_tsum_powerSeries_nhdsWithin_lt hAs.tendsto_sum_tsum_nat

/-- **Exponential formula** for a summable sequence. -/
theorem tsum_eq_exp_of_recursion (hA0 : A 0 = 1) (hAnn : ∀ n, 0 ≤ A n) (hAs : Summable A)
    (hPnn : ∀ n, 0 ≤ P n) (hP0 : P 0 = 0) (hPs : Summable P)
    (hrec : ∀ n : ℕ, (n : ℝ) * A n = ∑ k ∈ Finset.range (n + 1), P k * A (n - k)) :
    ∑' n, A n = Real.exp (∑' n, P n / n) := by
  set q : ℕ → ℝ := fun n => P n / n with hq
  have hqnn : ∀ n, 0 ≤ q n := fun n => div_nonneg (hPnn n) (Nat.cast_nonneg n)
  have hqle : ∀ n, q n ≤ P n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hq, hP0]
    · simp only [hq]
      rw [div_le_iff₀ (by exact_mod_cast hn)]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [hPnn n]
  have hqs : Summable q := Summable.of_nonneg_of_le hqnn hqle hPs
  have hAb : ∀ n, A n ≤ ∑' m, A m := fun n => hAs.le_tsum n fun m _ => hAnn m
  have hA1 := tendsto_genFun_nhdsWithin_lt hAs
  have hq1 : Tendsto (fun t => Real.exp (genFun q t)) (𝓝[<] 1) (𝓝 (Real.exp (∑' n, q n))) :=
    (Real.continuous_exp.tendsto _).comp (tendsto_genFun_nhdsWithin_lt hqs)
  have hA1' : Tendsto (genFun A) (𝓝[<] 1) (𝓝 (Real.exp (∑' n, q n))) := by
    refine hq1.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (genFun_eq_exp_of_recursion hA0 hAnn hAb hPnn hP0 hPs hrec ht.1.le ht.2).symm
  exact tendsto_nhds_unique hA1 hA1'

/-! ### The Abelian mean of the factor `B` -/

variable {B : ℕ → ℝ}

/-- `F_A(t) F_B(t) = 1/(1-t)` from `A * B = (1, 1, …)`. -/
theorem genFun_mul_genFun_eq (hAnn : ∀ n, 0 ≤ A n) (hAb : ∀ n, A n ≤ C)
    (hBnn : ∀ n, 0 ≤ B n) (hBb : ∀ n, B n ≤ C)
    (h1 : ∀ n, ∑ k ∈ Finset.range (n + 1), A k * B (n - k) = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    genFun A t * genFun B t = (1 - t)⁻¹ := by
  have ht : |t| < 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hterm : ∀ n : ℕ,
      ∑ kl ∈ Finset.antidiagonal n, A kl.1 * t ^ kl.1 * (B kl.2 * t ^ kl.2) = t ^ n := by
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => A i * t ^ i * (B j * t ^ j))]
    have hstep : ∀ k ∈ Finset.range (n + 1),
        A k * t ^ k * (B (n - k) * t ^ (n - k)) = A k * B (n - k) * t ^ n := by
      intro k hk
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : t ^ k * t ^ (n - k) = t ^ n := by rw [← pow_add, Nat.add_sub_cancel' hk']
      rw [← this]; ring
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, h1 n, one_mul]
  have hA' := (summable_coeff_mul_pow hAnn hAb ht).abs
  have hB' := (summable_coeff_mul_pow hBnn hBb ht).abs
  calc genFun A t * genFun B t
      = ∑' n : ℕ, ∑ kl ∈ Finset.antidiagonal n, A kl.1 * t ^ kl.1 * (B kl.2 * t ^ kl.2) :=
        tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA' hB'
    _ = ∑' n : ℕ, t ^ n := tsum_congr hterm
    _ = (1 - t)⁻¹ := tsum_geometric_of_lt_one ht0 ht1

/-- The lower Abelian bound: if `p ≤ B m` for all `m`, then `p ≤ (1 - t) F_B(t)`. -/
theorem le_one_sub_mul_genFun {p : ℝ} (hBnn : ∀ n, 0 ≤ B n) (hBb : ∀ n, B n ≤ C)
    (hpB : ∀ m, p ≤ B m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    p ≤ (1 - t) * genFun B t := by
  have ht : |t| < 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have h1t : 0 < 1 - t := by linarith
  have hgeo : Summable fun n : ℕ => p * t ^ n := (summable_geometric_of_lt_one ht0 ht1).mul_left p
  have hle : ∑' n : ℕ, p * t ^ n ≤ genFun B t :=
    hgeo.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (hpB n) (pow_nonneg ht0 n))
      (summable_coeff_mul_pow hBnn hBb ht)
  rw [tsum_mul_left, tsum_geometric_of_lt_one ht0 ht1] at hle
  have : p = (1 - t) * (p * (1 - t)⁻¹) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hle h1t.le

/-- The upper Abelian bound for an antitone `B ≤ 1`: `(1 - t) F_B(t) ≤ N (1 - t) + B N`. -/
theorem one_sub_mul_genFun_le (hBnn : ∀ n, 0 ≤ B n) (hB1 : ∀ n, B n ≤ 1) (hBanti : Antitone B)
    (N : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) * genFun B t ≤ N * (1 - t) + B N := by
  have ht : |t| < 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have h1t : 0 < 1 - t := by linarith
  have hs : Summable fun n => B n * t ^ n := summable_coeff_mul_pow hBnn hB1 ht
  have hsplit := (hs.sum_add_tsum_nat_add N).symm
  unfold genFun
  rw [hsplit]
  have hhead : ∑ i ∈ Finset.range N, B i * t ^ i ≤ N := by
    calc ∑ i ∈ Finset.range N, B i * t ^ i ≤ ∑ _i ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_one₀ (hB1 i) (pow_nonneg ht0 i) (pow_le_one₀ ht0 ht1.le)
      _ = N := by simp
  have htail : ∑' i, B (i + N) * t ^ (i + N) ≤ B N * (1 - t)⁻¹ := by
    have hgeo : Summable fun i : ℕ => B N * t ^ i := (summable_geometric_of_lt_one ht0 ht1).mul_left _
    calc ∑' i, B (i + N) * t ^ (i + N) ≤ ∑' i : ℕ, B N * t ^ i := by
          refine ((summable_nat_add_iff N).mpr hs).tsum_le_tsum (fun i => ?_) hgeo
          have h1 : B (i + N) ≤ B N := hBanti (Nat.le_add_left N i)
          have h2 : t ^ (i + N) ≤ t ^ i := pow_le_pow_of_le_one ht0 ht1.le (Nat.le_add_right i N)
          exact mul_le_mul h1 h2 (pow_nonneg ht0 _) (hBnn N)
      _ = B N * (1 - t)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one ht0 ht1]
  calc (1 - t) * (∑ i ∈ Finset.range N, B i * t ^ i + ∑' i, B (i + N) * t ^ (i + N))
      ≤ (1 - t) * (N + B N * (1 - t)⁻¹) := by gcongr
    _ = N * (1 - t) + B N := by field_simp

/-- **Spitzer's limit formula.**  From the two convolution identities, `A₀ = B₀ = 1`,
`0 ≤ A, B ≤ 1`, `B` antitone with limit `p`, and nonnegative summable `P` with `P₀ = 0`:
`p = exp(-∑ P_n / n)`. -/
theorem spitzer_limit_of_factorisation {p : ℝ}
    (hA0 : A 0 = 1) (hAnn : ∀ n, 0 ≤ A n) (hA1 : ∀ n, A n ≤ 1)
    (hB0 : B 0 = 1) (hBnn : ∀ n, 0 ≤ B n) (hB1 : ∀ n, B n ≤ 1) (hBanti : Antitone B)
    (hBlim : Tendsto B atTop (𝓝 p))
    (hPnn : ∀ n, 0 ≤ P n) (hP0 : P 0 = 0) (hPs : Summable P)
    (h1 : ∀ n, ∑ k ∈ Finset.range (n + 1), A k * B (n - k) = 1)
    (h2 : ∀ n, ∑ k ∈ Finset.range (n + 1), (k : ℝ) * A k * B (n - k) =
      ∑ j ∈ Finset.range (n + 1), P j) :
    p = Real.exp (-∑' n, P n / n) := by
  set q : ℕ → ℝ := fun n => P n / n with hq
  have hqnn : ∀ n, 0 ≤ q n := fun n => div_nonneg (hPnn n) (Nat.cast_nonneg n)
  have hqle : ∀ n, q n ≤ P n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hq, hP0]
    · simp only [hq]
      rw [div_le_iff₀ (by exact_mod_cast hn)]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [hPnn n]
  have hqs : Summable q := Summable.of_nonneg_of_le hqnn hqle hPs
  have hrec := convolution_recursion hB0 h1 h2
  -- `(1 - t) F_B(t) = exp(-Q(t))` on `[0, 1)`
  have hkey : ∀ t : ℝ, 0 ≤ t → t < 1 → (1 - t) * genFun B t = Real.exp (-genFun q t) := by
    intro t ht0 ht1
    have hE := genFun_eq_exp_of_recursion hA0 hAnn hA1 hPnn hP0 hPs hrec ht0 ht1
    have hAB := genFun_mul_genFun_eq hAnn hA1 hBnn hB1 h1 ht0 ht1
    have h1t : (1 - t) ≠ 0 := by linarith
    have hEpos : Real.exp (genFun q t) ≠ 0 := (Real.exp_pos _).ne'
    rw [hE] at hAB
    have hAB' : Real.exp (genFun q t) * genFun B t = (1 - t)⁻¹ := hAB
    have hprod : (1 - t) * genFun B t * Real.exp (genFun q t) = 1 := by
      rw [mul_assoc, mul_comm (genFun B t), hAB', mul_inv_cancel₀ h1t]
    rw [Real.exp_neg]
    calc (1 - t) * genFun B t
        = (1 - t) * genFun B t * Real.exp (genFun q t) * (Real.exp (genFun q t))⁻¹ := by
          rw [mul_inv_cancel_right₀ hEpos]
      _ = (Real.exp (genFun q t))⁻¹ := by rw [hprod, one_mul]
  have hpB : ∀ m, p ≤ B m := fun m => hBanti.le_of_tendsto hBlim m
  -- the limit of the right side as `t ↑ 1`
  have hlim : Tendsto (fun t => Real.exp (-genFun q t)) (𝓝[<] 1) (𝓝 (Real.exp (-∑' n, q n))) :=
    (Real.continuous_exp.tendsto _).comp ((tendsto_genFun_nhdsWithin_lt hqs).neg)
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 ≤ t ∧ t < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact ⟨ht.1.le, ht.2⟩
  -- lower bound: `p ≤ exp(-Q(1))`
  have hlow : p ≤ Real.exp (-∑' n, q n) := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [hev] with t ht
    rw [← hkey t ht.1 ht.2]
    exact le_one_sub_mul_genFun hBnn hB1 hpB ht.1 ht.2
  -- upper bound: `exp(-Q(1)) ≤ B N` for every `N`, hence `≤ p`
  have hup : ∀ N : ℕ, Real.exp (-∑' n, q n) ≤ B N := by
    intro N
    have hlimN : Tendsto (fun t : ℝ => (N : ℝ) * (1 - t) + B N) (𝓝[<] 1) (𝓝 (B N)) := by
      have : Tendsto (fun t : ℝ => (N : ℝ) * (1 - t) + B N) (𝓝 1) (𝓝 ((N : ℝ) * (1 - 1) + B N)) :=
        (Continuous.tendsto (by fun_prop) 1)
      simpa using this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hlim hlimN ?_
    filter_upwards [hev] with t ht
    rw [← hkey t ht.1 ht.2]
    exact one_sub_mul_genFun_le hBnn hB1 hBanti N ht.1 ht.2
  have hup' : Real.exp (-∑' n, q n) ≤ p := ge_of_tendsto' hBlim hup
  exact le_antisymm hlow hup'

end GenFun

end Fluctuation
end SwingRepair
