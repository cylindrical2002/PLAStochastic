import PLAStochastic.ForMathlib.Analysis.Fourier.InverseAsymptotics
import PLAStochastic.ForMathlib.Analysis.Fourier.CoefficientMeasurable

/-!
# Finite-order three-band Fourier estimates

A finite-regularity version of the all-orders inversion assembly. The low band and
the coefficient envelopes are required through a fixed order `Q`, the high band
through a fixed order `R`, and the mid-band exponent `δ` is fixed. Every consumer
states its requirement on `(Q, R)` through `n ≤ Q` and the explicit order
`fourierHighOrder δ m n ≤ R`, which is monotone in both budgets.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace PGM

/-- Explicit high-frequency order paying derivative budget `m` and inverse order `n`. -/
def fourierHighOrder (δ : ℝ) (m n : ℕ) : ℕ := m + 2 + (⌊((n + m + 4 : ℕ) : ℝ) / δ⌋₊ + 1)

theorem fourierHighOrder_mono {δ : ℝ} {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') (hδ : 0 < δ) :
    fourierHighOrder δ m n ≤ fourierHighOrder δ m' n' := by
  unfold fourierHighOrder
  have hf : ⌊((n + m + 4 : ℕ) : ℝ) / δ⌋₊ ≤ ⌊((n' + m' + 4 : ℕ) : ℝ) / δ⌋₊ := by
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hδ.le
    exact_mod_cast (by omega : n + m + 4 ≤ n' + m' + 4)
  omega

/-- The explicit version of `exists_high_frequency_order`. -/
theorem high_frequency_order_spec {δ : ℝ} (hδ : 0 < δ) (m n : ℕ) {eps t K y : ℝ}
    (he : 1 ≤ eps) (ht : eps ^ (1 + δ) ≤ t) (hK : 0 ≤ K) (hy : 0 ≤ y)
    (hb : t ^ fourierHighOrder δ m n * y ≤ K * eps ^ (fourierHighOrder δ m n + 2)) :
    (1 + t) ^ (m + 2) * y ≤ 2 ^ (m + 2) * K * (eps⁻¹) ^ n := by
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ, s = ⌊((n + m + 4 : ℕ) : ℝ) / δ⌋₊ + 1 := ⟨_, rfl⟩
  have hr : fourierHighOrder δ m n = m + 2 + s := by rw [hsdef]; rfl
  rw [hr] at hb
  have hs : ((n + m + 4 : ℕ) : ℝ) / δ < s := by
    rw [hsdef]
    push_cast
    exact Nat.lt_floor_add_one _
  have hs' : ((n + m + 4 : ℕ) : ℝ) ≤ δ * s := by
    have h := (div_lt_iff₀ hδ).mp hs
    linarith
  have he0 : 0 < eps := zero_lt_one.trans_le he
  have hcut1 : 1 ≤ eps ^ (1 + δ) := Real.one_le_rpow he (by linarith)
  have ht1 : 1 ≤ t := hcut1.trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hpow : eps ^ (m + 2 + s + 2 + n) ≤ t ^ s := by
    calc
      _ = eps ^ (((m + 2 + s + 2 + n : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
      _ ≤ eps ^ ((1 + δ) * s) := by
        apply Real.rpow_le_rpow_of_exponent_le he
        push_cast at hs' ⊢
        linarith
      _ = (eps ^ (1 + δ)) ^ s := by rw [← Real.rpow_natCast, ← Real.rpow_mul he0.le]
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg he0.le _) ht s
  have hcore : t ^ (m + 2) * y ≤ K * (eps⁻¹) ^ n := by
    apply (mul_le_mul_iff_right₀ (pow_pos ht0 s)).mp
    calc
      _ = t ^ (m + 2 + s) * y := by ring
      _ ≤ K * eps ^ (m + 2 + s + 2) := hb
      _ = (K * (eps⁻¹) ^ n) * eps ^ (m + 2 + s + 2 + n) := by
        rw [pow_add (eps) (m + 2 + s + 2) n, inv_pow]
        field_simp
      _ ≤ (K * (eps⁻¹) ^ n) * t ^ s := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (2 * t) ^ (m + 2) * y := by gcongr; linarith
    _ = 2 ^ (m + 2) * (t ^ (m + 2) * y) := by rw [mul_pow]; ring
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hcore (by positivity : 0 ≤ (2 : ℝ) ^ (m + 2))

/-- Finite-order three-band estimates: mid-band exponent `δ`, low band through order `Q`,
coefficient envelopes for `k ≤ Q`, high band through order `R`. -/
structure FourierBandEstimatesUpTo (φ : ℝ → ℝ → ℂ) (a : ℕ → ℝ → ℂ) (δ : ℝ) (Q R : ℕ) : Prop where
  delta_pos : 0 < δ
  delta_lt_one : δ < 1
  mid : ∃ c U K : ℝ, 0 < c ∧ 0 ≤ U ∧ 0 ≤ K ∧ ∃ d : ℕ,
      (∀ᶠ eps in atTop, ∀ u : ℝ, U ≤ |u| → |u| ≤ eps ^ (1 + δ) →
        ‖φ eps u‖ ≤ K * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|) +
          K * eps ^ d * Real.exp (-c * eps)) ∧
      (∀ k ≤ Q, ∃ B : ℝ, 0 ≤ B ∧ ∃ d : ℕ, ∀ u : ℝ,
        ‖a k u‖ ≤ B * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|))
  high : ∀ r ≤ R, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ eps in atTop, ∀ u : ℝ,
    |u| ^ r * ‖φ eps u‖ ≤ K * eps ^ (r + 2)
  low : ∀ P ≤ Q, ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧ ∃ d : ℕ,
    ∀ᶠ eps in atTop, ∀ u : ℝ, |u| ≤ (A * Real.log eps) ^ 2 →
      ‖φ eps u - ∑ k ∈ Finset.range (P + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤
        K * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ d

/-- Coefficient transforms through order `Q` have a common stretched-exponential
moment bound below any order `P ≤ Q`. -/
theorem finite_stretchedExp_moment_bound_upTo {a : ℕ → ℝ → ℂ} {c : ℝ} {Q : ℕ} (hc : 0 < c)
    (ha : ∀ k ≤ Q, ∃ B : ℝ, 0 ≤ B ∧ ∃ d : ℕ, ∀ u : ℝ,
      ‖a k u‖ ≤ B * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) (m P : ℕ) (hP : P ≤ Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ∑ k ∈ range (P + 1), (1 + |u|) ^ m * ‖a k u‖ ≤
        B * Real.exp (-(c / 2) * Real.sqrt |u|) := by
  classical
  have hsingle : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, k ≤ Q →
      (1 + |u|) ^ m * ‖a k u‖ ≤ C * Real.exp (-(c / 2) * Real.sqrt |u|) := by
    intro k
    by_cases hk : k ≤ Q
    · obtain ⟨B, hB, d, hb⟩ := ha k hk
      obtain ⟨C, hC, hc'⟩ := polynomial_mul_stretchedExp_le hc (m + d)
      refine ⟨B * C, by positivity, fun u _ => ?_⟩
      calc
        _ ≤ (1 + |u|) ^ m * (B * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) :=
          mul_le_mul_of_nonneg_left (hb u) (by positivity)
        _ = B * ((1 + |u|) ^ (m + d) * Real.exp (-c * Real.sqrt |u|)) := by rw [pow_add]; ring
        _ ≤ _ := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hc' |u| (abs_nonneg _)) hB
    · exact ⟨0, le_rfl, fun _ hk' => absurd hk' hk⟩
  choose C hC hbound using hsingle
  refine ⟨∑ k ∈ range (P + 1), C k, sum_nonneg fun k _ => hC k, fun u => ?_⟩
  rw [sum_mul]
  exact sum_le_sum fun k hk => hbound k u (by have := mem_range.mp hk; omega)

/-- A pointwise integrable majorant for the Fourier remainder of order `n ≤ Q`.
One algebraic order is reserved for the polynomial logarithmic loss. -/
theorem FourierBandEstimatesUpTo.remainder_moment_bound {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R) (m n : ℕ) (hn : n ≤ Q)
    (hR : fourierHighOrder δ m n ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ eps in atTop, ∀ u : ℝ,
      (1 + |u|) ^ (m + 2) *
        ‖φ eps u - ∑ k ∈ range (n + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤ C * (eps⁻¹) ^ n := by
  have hδ := h.delta_pos
  have hδ1 := h.delta_lt_one
  obtain ⟨c, U, K, hc, hU, hK, d, hmed, ha⟩ := h.mid
  let A := max 1 (2 * (n : ℝ) / c)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hnA : (n : ℝ) ≤ (c / 2) * A := by
    have h := le_max_right (1 : ℝ) (2 * (n : ℝ) / c)
    have hd := (div_le_iff₀ hc).mp h
    dsimp [A]
    nlinarith
  obtain ⟨H, hH, hhigh⟩ := h.high (fourierHighOrder δ m n) hR
  obtain ⟨L, hL, dl, hlow⟩ := h.low n hn A hA
  obtain ⟨M, hM, hm⟩ := polynomial_mul_stretchedExp_le hc (m + 2 + d)
  obtain ⟨B, hB, hb⟩ := finite_stretchedExp_moment_bound_upTo hc ha (m + 2) n hn
  obtain ⟨E, hE, he⟩ := polynomial_mul_exp_le_inverse hc (d + 2 * (m + 2)) n
  let C := L * (1 + A ^ 2) ^ (dl + m + 2) + K * M +
    2 ^ (m + 2) * (K * E + H) + B
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hlogs : ∀ᶠ eps : ℝ in atTop, max 1 U ≤ Real.log eps :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 U))
  filter_upwards [hmed, hhigh, hlow, hlogs, eventually_ge_atTop (1 : ℝ),
    eventually_log_band_polynomial_le A (dl + m + 2)] with eps hmed hhigh hlow hlog heps hlogpoly
  intro u
  have heps0 : 0 < eps := zero_lt_one.trans_le heps
  have hi0 : 0 ≤ eps⁻¹ := (inv_pos.mpr heps0).le
  have hi1 : eps⁻¹ ≤ 1 := (inv_le_one₀ heps0).mpr heps
  have ht0 : 0 ≤ |u| := abs_nonneg _
  have hbase : 0 ≤ 1 + |u| := by positivity
  by_cases hlu : |u| ≤ (A * Real.log eps) ^ 2
  · have hlb : (1 + |u|) ^ (m + 2) *
        ‖φ eps u - ∑ k ∈ range (n + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤
        (L * (1 + A ^ 2) ^ (dl + m + 2)) * (eps⁻¹) ^ n := by
      calc
        _ ≤ (1 + |u|) ^ (m + 2) * (L * (eps⁻¹) ^ (n + 1) * (1 + |u|) ^ dl) :=
          mul_le_mul_of_nonneg_left (hlow u hlu) (by positivity)
        _ = L * (eps⁻¹) ^ (n + 1) * (1 + |u|) ^ (dl + m + 2) := by rw [pow_add, pow_add]; ring
        _ ≤ L * (eps⁻¹) ^ (n + 1) * ((1 + A ^ 2) ^ (dl + m + 2) * eps) := by
          gcongr
          exact (pow_le_pow_left₀ hbase (by linarith) _).trans hlogpoly
        _ = _ := by rw [pow_succ]; field_simp
    have hrest : 0 ≤ K * M + 2 ^ (m + 2) * (K * E + H) + B := by positivity
    exact hlb.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hi0 _))
  · have hcut : (A * Real.log eps) ^ 2 ≤ |u| := (not_le.mp hlu).le
    have htail := stretchedExp_log_cutoff (by positivity : 0 < c / 2) heps hnA ht0 hcut
    have hUu : U ≤ |u| := by
      have hlog1 : 1 ≤ Real.log eps := (le_max_left _ _).trans hlog
      have hlogU : U ≤ Real.log eps := (le_max_right _ _).trans hlog
      have hx : Real.log eps ≤ A * Real.log eps := by nlinarith
      nlinarith
    have hcoeff : (1 + |u|) ^ (m + 2) *
        ‖∑ k ∈ range (n + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤ B * (eps⁻¹) ^ n := by
      calc
        _ ≤ (1 + |u|) ^ (m + 2) * ∑ k ∈ range (n + 1), ‖((eps⁻¹) ^ k : ℝ) • a k u‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ ≤ ∑ k ∈ range (n + 1), (1 + |u|) ^ (m + 2) * ‖a k u‖ := by
          rw [mul_sum]
          apply sum_le_sum
          intro k _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hi0 _)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hi0 hi1) (norm_nonneg _)).trans_eq
            (one_mul _)
        _ ≤ B * Real.exp (-(c / 2) * Real.sqrt |u|) := hb u
        _ ≤ _ := mul_le_mul_of_nonneg_left htail hB
    have hactual : (1 + |u|) ^ (m + 2) * ‖φ eps u‖ ≤
        (K * M + 2 ^ (m + 2) * (K * E + H)) * (eps⁻¹) ^ n := by
      by_cases hmu : |u| ≤ eps ^ (1 + δ)
      · have hu2 : |u| ≤ eps ^ (2 : ℕ) := by
          refine hmu.trans ?_
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le heps (by norm_num; linarith)
        have hpoly : (1 + |u|) ^ (m + 2) * eps ^ d ≤ 2 ^ (m + 2) * eps ^ (d + 2 * (m + 2)) := by
          calc
            _ ≤ (2 * eps ^ 2) ^ (m + 2) * eps ^ d := by gcongr; nlinarith [sq_nonneg eps]
            _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
        have h1 : (1 + |u|) ^ (m + 2) * (K * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) ≤
            K * M * (eps⁻¹) ^ n := by
          calc
            _ = K * ((1 + |u|) ^ (m + 2 + d) * Real.exp (-c * Real.sqrt |u|)) := by
              rw [pow_add]; ring
            _ ≤ K * (M * Real.exp (-(c / 2) * Real.sqrt |u|)) :=
              mul_le_mul_of_nonneg_left (hm |u| ht0) hK
            _ ≤ _ := by
              simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail (mul_nonneg hK hM)
        have h2 : (1 + |u|) ^ (m + 2) * (K * eps ^ d * Real.exp (-c * eps)) ≤
            2 ^ (m + 2) * K * E * (eps⁻¹) ^ n := by
          calc
            _ = K * ((1 + |u|) ^ (m + 2) * eps ^ d) * Real.exp (-c * eps) := by ring
            _ ≤ K * (2 ^ (m + 2) * eps ^ (d + 2 * (m + 2))) * Real.exp (-c * eps) := by gcongr
            _ = (2 ^ (m + 2) * K) * (eps ^ (d + 2 * (m + 2)) * Real.exp (-c * eps)) := by ring
            _ ≤ _ := by
              simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (he eps heps)
                (by positivity : 0 ≤ (2 : ℝ) ^ (m + 2) * K)
        have hh := mul_le_mul_of_nonneg_left (hmed u hUu hmu) (pow_nonneg hbase (m + 2))
        rw [mul_add] at hh
        have hHextra : 0 ≤ 2 ^ (m + 2) * H * (eps⁻¹) ^ n := by positivity
        nlinarith
      · have hh := high_frequency_order_spec hδ m n heps (not_le.mp hmu).le hH (norm_nonneg _)
          (hhigh u)
        have hextra : 0 ≤ K * M * (eps⁻¹) ^ n + 2 ^ (m + 2) * K * E * (eps⁻¹) ^ n := by
          positivity
        nlinarith
    calc
      _ ≤ (1 + |u|) ^ (m + 2) *
          (‖φ eps u‖ + ‖∑ k ∈ range (n + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ C * (eps⁻¹) ^ n := by
        rw [mul_add]
        apply (add_le_add hactual hcoeff).trans
        have hlow0 : 0 ≤ L * (1 + A ^ 2) ^ (dl + m + 2) * (eps⁻¹) ^ n := by positivity
        dsimp [C]
        nlinarith

/-- Coefficient measurability through order `Q` follows from the local expansions. -/
theorem FourierBandEstimatesUpTo.coefficient_aestronglyMeasurable {φ : ℝ → ℝ → ℂ}
    {a : ℕ → ℝ → ℂ} {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps)) (k : ℕ) (hk : k ≤ Q) :
    AEStronglyMeasurable (a k) := by
  classical
  revert hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkQ
    obtain ⟨E, hE⟩ := eventually_atTop.mp hφ
    let Φ : ℝ → ℝ → ℂ := fun eps u => if E ≤ eps then φ eps u else 0
    let b : ℝ → ℝ → ℂ := fun eps u => (eps ^ k : ℝ) •
      (Φ eps u - ∑ i ∈ range k, ((eps⁻¹) ^ i : ℝ) • a i u)
    have hb (eps : ℝ) : AEStronglyMeasurable (b eps) := by
      have hm : AEStronglyMeasurable (Φ eps) := by
        by_cases he : E ≤ eps
        · simpa only [Φ, if_pos he] using hE eps he
        · simpa only [Φ, if_neg he] using
            (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ)))
      exact (hm.sub (Finset.aestronglyMeasurable_fun_sum _ fun i hi =>
        (ih i (mem_range.mp hi) (by have := mem_range.mp hi; omega)).const_smul
          ((eps⁻¹) ^ i : ℝ))).const_smul (eps ^ k : ℝ)
    obtain ⟨K, hK, d, hlocal⟩ := h.low k hkQ 1 (by norm_num)
    have hlim (u : ℝ) : Tendsto (fun eps => b eps u) atTop (𝓝 (a k u)) := by
      have hlog : ∀ᶠ eps : ℝ in atTop, Real.sqrt |u| ≤ Real.log eps :=
        Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.sqrt |u|))
      have hbound : ∀ᶠ eps : ℝ in atTop,
          ‖b eps u - a k u‖ ≤ (K * (1 + |u|) ^ d) * eps⁻¹ := by
        filter_upwards [hlocal, hlog, eventually_ge_atTop E, eventually_ge_atTop (1 : ℝ)]
          with eps hl hs he he1
        have he0 : 0 < eps := zero_lt_one.trans_le he1
        have hlog0 : 0 ≤ Real.log eps := Real.log_nonneg he1
        have hcut : |u| ≤ (1 * Real.log eps) ^ 2 := by
          simp only [one_mul]
          nlinarith [Real.sq_sqrt (abs_nonneg u), Real.sqrt_nonneg |u|]
        have heq : b eps u - a k u = (eps ^ k : ℝ) •
            (φ eps u - ∑ i ∈ range (k + 1), ((eps⁻¹) ^ i : ℝ) • a i u) := by
          dsimp [b, Φ]
          rw [if_pos he, sum_range_succ]
          push_cast
          have hcancel : eps ^ k * (eps⁻¹) ^ k = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ he0.ne', one_pow]
          have hc : (eps ^ k : ℂ) * ((eps⁻¹) ^ k : ℂ) = 1 := by
            exact_mod_cast hcancel
          push_cast at hc
          calc
            _ = (eps ^ k : ℂ) * (φ eps u -
                (∑ i ∈ range k, ((eps⁻¹) ^ i : ℂ) * a i u + ((eps⁻¹) ^ k : ℂ) * a k u)) +
                ((eps ^ k : ℂ) * ((eps⁻¹) ^ k : ℂ) - 1) * a k u := by push_cast; ring
            _ = _ := by push_cast; rw [hc]; ring
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg he0.le _)]
        calc
          _ ≤ eps ^ k * (K * (eps⁻¹) ^ (k + 1) * (1 + |u|) ^ d) :=
            mul_le_mul_of_nonneg_left (hl u hcut) (pow_nonneg he0.le _)
          _ = _ := by
            have hc : eps ^ k * (eps⁻¹) ^ k = 1 := by
              rw [← mul_pow, mul_inv_cancel₀ he0.ne', one_pow]
            rw [pow_succ]
            calc
              _ = (eps ^ k * (eps⁻¹) ^ k) * K * (1 + |u|) ^ d * eps⁻¹ := by ring
              _ = _ := by rw [hc]; ring
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
        (by simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul (K * (1 + |u|) ^ d))
    exact aestronglyMeasurable_of_tendsto_ae atTop hb (ae_of_all _ hlim)

theorem FourierBandEstimatesUpTo.coefficient_moment_bound {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R) (m k : ℕ) (hk : k ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, (1 + |u|) ^ (m + 2) * ‖a k u‖ ≤ C := by
  obtain ⟨c, U, K, hc, -, -, d, -, ha⟩ := h.mid
  obtain ⟨B, hB, hb⟩ := finite_stretchedExp_moment_bound_upTo hc ha (m + 2) k hk
  refine ⟨B, hB, fun u => ?_⟩
  have hsingle : (1 + |u|) ^ (m + 2) * ‖a k u‖ ≤
      ∑ j ∈ range (k + 1), (1 + |u|) ^ (m + 2) * ‖a j u‖ := by
    apply single_le_sum (f := fun j : ℕ => (1 + |u|) ^ (m + 2) * ‖a j u‖) (a := k)
    · intro j _; positivity
    · exact mem_range.mpr (Nat.lt_succ_self k)
  have hex : Real.exp (-(c / 2) * Real.sqrt |u|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg |u|])
  exact (hsingle.trans (hb u)).trans ((mul_le_mul_of_nonneg_left hex hB).trans_eq (mul_one _))

theorem FourierBandEstimatesUpTo.actual_moment_bound {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R) (m : ℕ)
    (hR : fourierHighOrder δ m 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ eps in atTop, ∀ u : ℝ,
      (1 + |u|) ^ (m + 2) * ‖φ eps u‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := h.remainder_moment_bound m 0 (Nat.zero_le _) hR
  obtain ⟨B, hB, ha⟩ := h.coefficient_moment_bound m 0 (Nat.zero_le _)
  refine ⟨C + B, by positivity, ?_⟩
  filter_upwards [hb] with eps he u
  simp only [Nat.zero_add, sum_range_one, pow_zero, one_smul, mul_one] at he
  have htri := mul_le_mul_of_nonneg_left (norm_sub_le (φ eps u - a 0 u) (-a 0 u))
    (by positivity : 0 ≤ (1 + |u|) ^ (m + 2))
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
  rw [mul_add] at htri
  exact htri.trans (add_le_add (he u) (ha u))

theorem FourierBandEstimatesUpTo.coefficient_contDiff {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R)
    (ha : ∀ k ≤ Q, AEStronglyMeasurable (a k)) (m k : ℕ) (hk : k ≤ Q) :
    ContDiff ℝ m (angularRealInverse (a k)) := by
  obtain ⟨B, -, hb⟩ := h.coefficient_moment_bound m k hk
  exact (contDiff_angularInverse (ha k hk) (fun r hr =>
    (integrable_fourier_moment_of_bound (ha k hk) hr hb).1)).continuousLinearMap_comp Complex.reCLM

/-- The actual inverse derivatives through order `m` are eventually bounded by one constant. -/
theorem FourierBandEstimatesUpTo.actual_inverse_bounded {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps)) (m : ℕ)
    (hR : fourierHighOrder δ m 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ eps in atTop,
      ContDiff ℝ m (angularRealInverse (φ eps)) ∧
        ∀ r ≤ m, ∀ x, |iteratedDeriv r (angularRealInverse (φ eps)) x| ≤ B := by
  obtain ⟨C, hC, hc⟩ := h.actual_moment_bound m hR
  let J := ∫ u : ℝ, fourierMomentWeight (2 * Real.pi * u)
  have hJ : 0 ≤ J := integral_nonneg fun _ => by unfold fourierMomentWeight; positivity
  refine ⟨(2 * Real.pi) ^ m * C * J, by positivity, ?_⟩
  filter_upwards [hc, hφ] with eps he hm
  have hcd := contDiff_angularInverse hm
    (fun r hr => (integrable_fourier_moment_of_bound hm hr he).1)
  refine ⟨hcd.continuousLinearMap_comp Complex.reCLM, fun r hr x => ?_⟩
  change |iteratedDeriv r (fun y => (angularInverse (φ eps) y).re) x| ≤ _
  rw [iteratedDeriv_re hcd hr]
  refine (Complex.abs_re_le_norm _).trans
    ((norm_deriv_angularInverse_of_bound hm hC hr he x).trans ?_)
  have hp : (2 * Real.pi) ^ r ≤ (2 * Real.pi) ^ m :=
    pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hr
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hC) hJ

/-- Uniform real-space inverse-power expansions through order `M`. -/
def UniformInverseExpansionUpTo (F : ℝ → ℝ → ℝ) (a : ℕ → ℝ → ℝ) (M : ℕ) : Prop :=
  ∀ n ≤ M, ∃ K E : ℝ, ∀ eps ≥ E, ∀ x : ℝ,
    |F eps x - inversePolynomial (fun i => a i x) n eps| ≤ K * (eps⁻¹) ^ (n + 1)

theorem UniformInverseExpansionUpTo.congr_eventually {F F' : ℝ → ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    {M : ℕ} (h : UniformInverseExpansionUpTo F g M) (he : ∀ᶠ eps in atTop, F eps = F' eps) :
    UniformInverseExpansionUpTo F' g M := by
  intro n hn
  obtain ⟨K, E, hK⟩ := h n hn
  obtain ⟨E', hE'⟩ := eventually_atTop.mp he
  refine ⟨K, max E E', fun eps he x => ?_⟩
  rw [← hE' eps ((le_max_right _ _).trans he)]
  exact hK eps ((le_max_left _ _).trans he) x

/-- The coefficients through order `M` inherit a common positive exponential rate. -/
theorem UniformInverseExpansionUpTo.finite_coefficient_envelopes {F : ℝ → ℝ → ℝ}
    {a : ℕ → ℝ → ℝ} {M : ℕ} (h : UniformInverseExpansionUpTo F a M)
    (henv : ∃ D θ E : ℝ, 0 ≤ D ∧ 0 < θ ∧
      ∀ eps ≥ E, ∀ x, |F eps x| ≤ D * Real.exp (-θ * |x|)) :
    ∃ D θ E : ℝ, 0 ≤ D ∧ 0 < θ ∧
      (∀ eps ≥ E, ∀ x, |F eps x| ≤ D * Real.exp (-θ * |x|)) ∧
      ∀ i ≤ M, ∀ x, |a i x| ≤ D * Real.exp (-θ * |x|) := by
  have haux : ∀ n : ℕ, n ≤ M + 1 → ∃ D θ E : ℝ, 0 ≤ D ∧ 0 < θ ∧
      (∀ eps ≥ E, ∀ x, |F eps x| ≤ D * Real.exp (-θ * |x|)) ∧
      ∀ i < n, ∀ x, |a i x| ≤ D * Real.exp (-θ * |x|) := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨D, θ, E, hD, hθ, hF⟩ := henv
      exact ⟨D, θ, E, hD, hθ, hF, fun i hi => by omega⟩
    | succ n ih =>
      intro hn
      obtain ⟨D, θ, E, hD, hθ, hF, ha⟩ := ih (by omega)
      obtain ⟨B, hB, hb⟩ := exponential_envelope_of_last_coefficient hD hθ hF ha (h n (by omega))
      let θ' := θ / ((n : ℝ) + 1)
      have hθ' : 0 < θ' := by dsimp [θ']; positivity
      have hθle : θ' ≤ θ := by
        dsimp [θ']
        exact div_le_self hθ.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hex (x : ℝ) : Real.exp (-θ * |x|) ≤ Real.exp (-θ' * |x|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])
      refine ⟨D + B, θ', E, by positivity, hθ', ?_, ?_⟩
      · intro eps he x
        exact (hF eps he x).trans
          (mul_le_mul (by linarith) (hex x) (Real.exp_pos _).le (by positivity))
      · intro i hi x
        rcases (show i ≤ n by omega).lt_or_eq with hi' | rfl
        · exact (ha i hi' x).trans
            (mul_le_mul (by linarith) (hex x) (Real.exp_pos _).le (by positivity))
        · exact (hb x).trans
            (mul_le_mul_of_nonneg_right (by linarith : B ≤ D + B) (Real.exp_pos _).le)
  obtain ⟨D, θ, E, hD, hθ, hF, ha⟩ := haux (M + 1) le_rfl
  exact ⟨D, θ, E, hD, hθ, hF, fun i hi => ha i (by omega)⟩

/-- Every real-space derivative has a uniform expansion through order `M`, provided the
low band reaches `M + 1` and the high band reaches `fourierHighOrder δ r (M + 1)`. -/
theorem FourierBandEstimatesUpTo.uniform_inverse_expansion {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps))
    (ha : ∀ k ≤ Q, AEStronglyMeasurable (a k)) (r M : ℕ) (hM : M + 1 ≤ Q)
    (hR : fourierHighOrder δ r (M + 1) ≤ R) :
    UniformInverseExpansionUpTo (fun eps => iteratedDeriv r (angularRealInverse (φ eps)))
      (fun k => iteratedDeriv r (angularRealInverse (a k))) M := by
  intro P hP
  have hδ := h.delta_pos
  have hR0 : fourierHighOrder δ r 0 ≤ R :=
    (fourierHighOrder_mono le_rfl (Nat.zero_le _) hδ).trans hR
  have hRP : fourierHighOrder δ r (P + 1) ≤ R :=
    (fourierHighOrder_mono le_rfl (by omega) hδ).trans hR
  obtain ⟨C, hC, hb⟩ := h.remainder_moment_bound r (P + 1) (by omega) hRP
  obtain ⟨B, hB, hbcoef⟩ := h.coefficient_moment_bound r (P + 1) (by omega)
  obtain ⟨V, -, hact⟩ := h.actual_inverse_bounded hφ r hR0
  obtain ⟨A, hA, hamoment⟩ := h.actual_moment_bound r hR0
  let J := ∫ u : ℝ, fourierMomentWeight (2 * Real.pi * u)
  have hJ : 0 ≤ J := integral_nonneg fun _ => by unfold fourierMomentWeight; positivity
  obtain ⟨E, hE⟩ := eventually_atTop.mp (hb.and (hφ.and (hact.and hamoment)))
  refine ⟨(2 * Real.pi) ^ r * (C + B) * J, max 1 E, fun eps heps x => ?_⟩
  have he1 : 1 ≤ eps := (le_max_left _ _).trans heps
  obtain ⟨hbe, hφe, hcd, ham⟩ := hE eps ((le_max_right _ _).trans heps)
  have hkQ : ∀ k ∈ range (P + 1 + 1), k ≤ Q := fun k hk => by
    have := mem_range.mp hk
    omega
  let Rm : ℝ → ℂ := fun u => φ eps u - ∑ k ∈ range (P + 1 + 1), ((eps⁻¹) ^ k : ℝ) • a k u
  have hRm : AEStronglyMeasurable Rm :=
    hφe.sub (Finset.aestronglyMeasurable_fun_sum _ fun k hk =>
      (ha k (hkQ k hk)).const_smul ((eps⁻¹) ^ k : ℝ))
  have hRbound : ∀ u, (1 + |u|) ^ (r + 2) * ‖Rm u‖ ≤ C * (eps⁻¹) ^ (P + 1) := hbe
  have hRcd := contDiff_angularInverse hRm
    (fun j hj => (integrable_fourier_moment_of_bound hRm hj hRbound).1)
  have hφi : Integrable (φ eps) := by
    apply (integrable_norm_iff hφe).mp
    simpa only [pow_zero, one_mul] using
      (integrable_fourier_moment_of_bound hφe (Nat.zero_le r) ham).1
  have hai (k : ℕ) (hk : k ≤ Q) : Integrable (a k) := by
    obtain ⟨W, -, hv⟩ := h.coefficient_moment_bound 0 k hk
    apply (integrable_norm_iff (ha k hk)).mp
    simpa only [pow_zero, one_mul] using
      (integrable_fourier_moment_of_bound (ha k hk) le_rfl hv).1
  have hreq : angularRealInverse Rm = fun y => angularRealInverse (φ eps) y -
      ∑ k ∈ range (P + 1 + 1), (eps⁻¹) ^ k * angularRealInverse (a k) y :=
    angularRealInverse_sub_sum hφi _ (fun k hk => hai k (hkQ k hk)) _
  have hRderiv (y : ℝ) : iteratedDeriv r (angularRealInverse Rm) y =
      iteratedDeriv r (angularRealInverse (φ eps)) y -
        ∑ k ∈ range (P + 1 + 1), (eps⁻¹) ^ k * iteratedDeriv r (angularRealInverse (a k)) y := by
    rw [hreq]
    exact iteratedDeriv_inverseRemainder hcd.1 _
      (fun k hk => h.coefficient_contDiff ha r k (hkQ k hk)) _ y
  have hs : |iteratedDeriv r (angularRealInverse Rm) x| ≤
      (2 * Real.pi) ^ r * C * J * (eps⁻¹) ^ (P + 1) := by
    change |iteratedDeriv r (fun y => (angularInverse Rm y).re) x| ≤ _
    rw [iteratedDeriv_re hRcd le_rfl]
    exact (Complex.abs_re_le_norm _).trans
      ((norm_deriv_angularInverse_of_bound hRm (by positivity) le_rfl hRbound x).trans_eq
        (by dsimp [J]; ring))
  have hP1 : P + 1 ≤ Q := by omega
  have hcoef : |iteratedDeriv r (angularRealInverse (a (P + 1))) x| ≤
      (2 * Real.pi) ^ r * B * J := by
    have hcc := contDiff_angularInverse (ha (P + 1) hP1) (fun j hj =>
      (integrable_fourier_moment_of_bound (ha (P + 1) hP1) hj hbcoef).1)
    change |iteratedDeriv r (fun y => (angularInverse (a (P + 1)) y).re) x| ≤ _
    rw [iteratedDeriv_re hcc le_rfl]
    exact (Complex.abs_re_le_norm _).trans
      (norm_deriv_angularInverse_of_bound (ha (P + 1) hP1) hB le_rfl hbcoef x)
  rw [hRderiv] at hs
  have hsplit : iteratedDeriv r (angularRealInverse (φ eps)) x -
      inversePolynomial (fun k => iteratedDeriv r (angularRealInverse (a k)) x) P eps =
      (iteratedDeriv r (angularRealInverse (φ eps)) x -
        ∑ k ∈ range (P + 1 + 1), (eps⁻¹) ^ k * iteratedDeriv r (angularRealInverse (a k)) x) +
          (eps⁻¹) ^ (P + 1) * iteratedDeriv r (angularRealInverse (a (P + 1))) x := by
    unfold inversePolynomial
    rw [sum_range_succ (n := P + 1)]
    have heq : ∑ k ∈ range (P + 1), iteratedDeriv r (angularRealInverse (a k)) x * (eps⁻¹) ^ k =
        ∑ k ∈ range (P + 1), (eps⁻¹) ^ k * iteratedDeriv r (angularRealInverse (a k)) x :=
      sum_congr rfl fun _ _ => mul_comm _ _
    rw [heq]
    ring
  rw [hsplit]
  have hi : 0 ≤ (eps⁻¹) ^ (P + 1) := by positivity
  have ht := mul_le_mul_of_nonneg_left hcoef hi
  rw [← abs_of_nonneg hi, ← abs_mul] at ht
  rw [abs_of_nonneg hi] at ht
  exact (abs_add_le _ _).trans ((add_le_add hs ht).trans_eq (by ring))

/-- The real inverse representative equals a given continuous density. -/
theorem FourierBandEstimatesUpTo.eventually_inverse_eq_density {φ : ℝ → ℝ → ℂ}
    {a : ℕ → ℝ → ℂ} {F : ℝ → ℝ → ℝ} {δ : ℝ} {Q R : ℕ} (h : FourierBandEstimatesUpTo φ a δ Q R)
    (hR : fourierHighOrder δ 0 0 ≤ R)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps))
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ)) :
    ∀ᶠ eps in atTop, angularRealInverse (φ eps) = F eps := by
  obtain ⟨B, -, hb⟩ := h.actual_moment_bound 0 hR
  filter_upwards [hb, hφ, hF] with eps he hm hf
  have hi : Integrable (φ eps) := by
    have hn : Integrable (fun u => ‖φ eps u‖) := by
      simpa only [pow_zero, one_mul] using (integrable_fourier_moment_of_bound hm le_rfl he).1
    exact (integrable_norm_iff hm).mp hn
  have hinv := angularInverse_charIntegral hf.1 hf.2.1 (by simpa only [← hf.2.2] using hi)
  rw [← hf.2.2] at hinv
  funext x
  exact congrArg Complex.re (congrFun hinv x)

end PGM
