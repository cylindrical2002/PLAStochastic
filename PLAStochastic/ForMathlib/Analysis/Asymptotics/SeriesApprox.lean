import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite-order approximation by a power series at one point

`SeriesApprox z F N h K` says that the complex number `z` is approximated by the truncation of
the formal power series `F` at the point `h ∈ [0, 1]`: the coefficients of order `≤ N` are at
most `K` and `‖z - ∑_{k ≤ N} [X^k]F hᵏ‖ ≤ K h^{N+1}`. The statement is pointwise in `h`; the
constants of every closure lemma are explicit functions of the input constants, so families of
approximations with common constants stay uniform.

* closure under sums, constant multiples, products (`SeriesApprox.mul`, constant
  `3 (N+2)² K L`), powers, and inverses (`SeriesApprox.inv`, given a bound on the
  coefficients of the inverse series);
* `norm_coeff_inv_mk_le`: the coefficients of `(∑ c_k X^k)⁻¹` of order `≤ N` are at most
  `((N+1)(1 + B/c_lo))^N / c_lo` when `‖c₀‖ ≥ c_lo > 0` and `‖c_k‖ ≤ B`, `k ≤ N`.
-/

namespace PGM

noncomputable section

open PowerSeries Finset

/-- The truncation of order `N` of a power series, evaluated at the real point `h`. -/
def truncEval (F : PowerSeries ℂ) (N : ℕ) (h : ℝ) : ℂ :=
  ∑ k ∈ range (N + 1), coeff k F * (h : ℂ) ^ k

/-- `z` is approximated to order `N` by the series `F` at the point `h`, with constant `K`. -/
def SeriesApprox (z : ℂ) (F : PowerSeries ℂ) (N : ℕ) (h K : ℝ) : Prop :=
  (∀ k ≤ N, ‖coeff k F‖ ≤ K) ∧ ‖z - truncEval F N h‖ ≤ K * h ^ (N + 1)

/-! ## Truncated evaluation -/

theorem truncEval_add (F G : PowerSeries ℂ) (N : ℕ) (h : ℝ) :
    truncEval (F + G) N h = truncEval F N h + truncEval G N h := by
  simp only [truncEval, map_add, add_mul, sum_add_distrib]

theorem truncEval_sub (F G : PowerSeries ℂ) (N : ℕ) (h : ℝ) :
    truncEval (F - G) N h = truncEval F N h - truncEval G N h := by
  simp only [truncEval, map_sub, sub_mul, sum_sub_distrib]

theorem truncEval_C_mul (a : ℂ) (F : PowerSeries ℂ) (N : ℕ) (h : ℝ) :
    truncEval (C a * F) N h = a * truncEval F N h := by
  simp only [truncEval, coeff_C_mul, mul_sum, mul_assoc]

theorem truncEval_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℂ) (N : ℕ) (h : ℝ) :
    truncEval (∑ i ∈ s, F i) N h = ∑ i ∈ s, truncEval (F i) N h := by
  simp only [truncEval, map_sum, sum_mul]
  exact sum_comm

theorem truncEval_C (a : ℂ) (N : ℕ) (h : ℝ) : truncEval (C a) N h = a := by
  simp [truncEval, coeff_C]

theorem truncEval_one (N : ℕ) (h : ℝ) : truncEval 1 N h = 1 := by
  simpa using truncEval_C 1 N h

theorem truncEval_X_pow (j N : ℕ) (h : ℝ) :
    truncEval (X ^ j) N h = if j ≤ N then (h : ℂ) ^ j else 0 := by
  simp only [truncEval, coeff_X_pow, ite_mul, one_mul, zero_mul]
  rw [sum_ite_eq' (range (N + 1)) j]
  simp

theorem norm_truncEval_le {F : PowerSeries ℂ} {N : ℕ} {h K : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hF : ∀ k ≤ N, ‖coeff k F‖ ≤ K) : ‖truncEval F N h‖ ≤ (N + 1) * K := by
  unfold truncEval
  calc ‖∑ k ∈ range (N + 1), coeff k F * (h : ℂ) ^ k‖
      ≤ ∑ k ∈ range (N + 1), ‖coeff k F * (h : ℂ) ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (N + 1), K := by
        refine sum_le_sum fun k hk => ?_
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
        calc ‖coeff k F‖ * h ^ k ≤ K * 1 :=
              mul_le_mul (hF k hk') (pow_le_one₀ h0 h1) (by positivity)
                ((norm_nonneg _).trans (hF k hk'))
          _ = K := mul_one K
    _ = (N + 1) * K := by simp

/-! ## Closure lemmas -/

namespace SeriesApprox

variable {z w : ℂ} {F G : PowerSeries ℂ} {N : ℕ} {h K L : ℝ}

theorem nonneg (hz : SeriesApprox z F N h K) : 0 ≤ K :=
  (norm_nonneg _).trans (hz.1 0 (Nat.zero_le _))

theorem mono (hz : SeriesApprox z F N h K) (hh : 0 ≤ h) (hKL : K ≤ L) :
    SeriesApprox z F N h L :=
  ⟨fun k hk => (hz.1 k hk).trans hKL, hz.2.trans (by gcongr)⟩

theorem add (hz : SeriesApprox z F N h K) (hw : SeriesApprox w G N h L) :
    SeriesApprox (z + w) (F + G) N h (K + L) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hz.1 k hk) (hw.1 k hk))
  · rw [truncEval_add, add_mul]
    have e : z + w - (truncEval F N h + truncEval G N h) =
        (z - truncEval F N h) + (w - truncEval G N h) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add hz.2 hw.2)

theorem const_mul (hz : SeriesApprox z F N h K) (a : ℂ) :
    SeriesApprox (a * z) (C a * F) N h (‖a‖ * K) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [coeff_C_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hz.1 k hk) (norm_nonneg a)
  · rw [truncEval_C_mul, ← mul_sub, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hz.2 (norm_nonneg a)

theorem sub_const (hz : SeriesApprox z F N h K) (hh : 0 ≤ h) (a : ℂ) :
    SeriesApprox (z - a) (F - C a) N h (K + ‖a‖) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [map_sub, coeff_C]
    refine (norm_sub_le _ _).trans (add_le_add (hz.1 k hk) ?_)
    split_ifs <;> simp
  · rw [truncEval_sub, truncEval_C]
    have e : z - a - (truncEval F N h - a) = z - truncEval F N h := by ring
    rw [e]
    refine hz.2.trans ?_
    have := norm_nonneg a
    gcongr
    linarith

theorem of_close (hw : SeriesApprox w F N h K) (hL : 0 ≤ L)
    (hzw : ‖z - w‖ ≤ L * h ^ (N + 1)) : SeriesApprox z F N h (K + L) := by
  refine ⟨fun k hk => (hw.1 k hk).trans (le_add_of_nonneg_right hL), ?_⟩
  have e : z - truncEval F N h = (z - w) + (w - truncEval F N h) := by ring
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (by linarith [hw.2])

end SeriesApprox

theorem seriesApprox_zero (N : ℕ) (h : ℝ) : SeriesApprox 0 0 N h 0 :=
  ⟨fun k _ => by simp, by simp [truncEval]⟩

theorem seriesApprox_sum {ι : Type*} (s : Finset ι) {z : ι → ℂ} {F : ι → PowerSeries ℂ} {N : ℕ}
    {h : ℝ} {K : ι → ℝ} (hz : ∀ i ∈ s, SeriesApprox (z i) (F i) N h (K i)) :
    SeriesApprox (∑ i ∈ s, z i) (∑ i ∈ s, F i) N h (∑ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using seriesApprox_zero N h
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, sum_insert ha]
    exact (hz a (mem_insert_self a s)).add (ih fun i hi => hz i (mem_insert_of_mem hi))

/-- A truncation approximates its own series exactly. -/
theorem seriesApprox_truncEval {F : PowerSeries ℂ} {N : ℕ} {h K : ℝ} (hh : 0 ≤ h)
    (hF : ∀ k ≤ N, ‖coeff k F‖ ≤ K) : SeriesApprox (truncEval F N h) F N h K := by
  refine ⟨hF, ?_⟩
  have hK : 0 ≤ K := (norm_nonneg _).trans (hF 0 (Nat.zero_le _))
  rw [sub_self, norm_zero]
  positivity

theorem seriesApprox_C (a : ℂ) (N : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    SeriesApprox a (C a) N h ‖a‖ := by
  have := seriesApprox_truncEval (F := C a) (N := N) (K := ‖a‖) hh fun k _ => by
    rw [coeff_C]
    split_ifs <;> simp
  rwa [truncEval_C] at this

theorem seriesApprox_one (N : ℕ) {h : ℝ} (hh : 0 ≤ h) : SeriesApprox 1 1 N h 1 := by
  simpa using seriesApprox_C 1 N hh

theorem seriesApprox_X_pow (j N : ℕ) {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    SeriesApprox ((h : ℂ) ^ j) (X ^ j) N h 1 := by
  refine ⟨fun k _ => ?_, ?_⟩
  · rw [coeff_X_pow]
    split_ifs <;> simp
  · rw [truncEval_X_pow, one_mul]
    split_ifs with hj
    · rw [sub_self, norm_zero]
      positivity
    · rw [sub_zero, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      exact pow_le_pow_of_le_one h0 h1 (by omega)

/-! ## Products -/

/-- The finite reindexing of a double sum along diagonals. -/
theorem sum_range_sum_range_sub' {M : Type*} [AddCommMonoid M] (P : ℕ) (f : ℕ → ℕ → M) :
    ∑ k ∈ range (P + 1), ∑ j ∈ range (P + 1 - k), f k j =
      ∑ n ∈ range (P + 1), ∑ k ∈ range (n + 1), f k (n - k) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [sum_range_succ (fun n => ∑ k ∈ range (n + 1), f k (n - k)) (P + 1), ← ih]
    have h1 : ∀ k ∈ range (P + 1 + 1), ∑ j ∈ range (P + 1 + 1 - k), f k j =
        ∑ j ∈ range (P + 1 - k), f k j + f k (P + 1 - k) := by
      intro k hk
      have hk' : P + 1 + 1 - k = (P + 1 - k) + 1 := by have := mem_range.mp hk; omega
      rw [hk', sum_range_succ]
    rw [sum_congr rfl h1, sum_add_distrib,
      sum_range_succ (fun k => ∑ j ∈ range (P + 1 - k), f k j) (P + 1)]
    simp

/-- The product of two truncations differs from the truncated product by the terms of total
order `> N`. -/
theorem norm_truncEval_mul_sub_le {F G : PowerSeries ℂ} {N : ℕ} {h K L : ℝ} (h0 : 0 ≤ h)
    (h1 : h ≤ 1) (hF : ∀ k ≤ N, ‖coeff k F‖ ≤ K) (hG : ∀ k ≤ N, ‖coeff k G‖ ≤ L) :
    ‖truncEval F N h * truncEval G N h - truncEval (F * G) N h‖ ≤
      ((N : ℝ) + 1) ^ 2 * (K * L) * h ^ (N + 1) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hF 0 (Nat.zero_le _))
  set f : ℕ → ℕ → ℂ := fun i j => coeff i F * coeff j G * (h : ℂ) ^ (i + j) with hf
  have hprod : truncEval F N h * truncEval G N h =
      ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), f i j := by
    rw [truncEval, truncEval, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hf]; dsimp only; rw [pow_add]; ring
  have htr : truncEval (F * G) N h = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1 - i), f i j := by
    rw [sum_range_sum_range_sub']
    simp only [truncEval, coeff_mul, sum_mul, hf]
    refine sum_congr rfl fun n hn => ?_
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine sum_congr rfl fun k hk => ?_
    have : k + (n - k) = n := by have := mem_range.mp hk; omega
    simp only [this]
  have hsplit : ∀ i ∈ range (N + 1), ∑ j ∈ range (N + 1), f i j - ∑ j ∈ range (N + 1 - i), f i j =
      ∑ j ∈ Ico (N + 1 - i) (N + 1), f i j := by
    intro i _
    rw [← sum_range_add_sum_Ico _ (Nat.sub_le (N + 1) i)]
    ring
  rw [hprod, htr, ← sum_sub_distrib, sum_congr rfl hsplit]
  have hL : 0 ≤ L := (norm_nonneg _).trans (hG 0 (Nat.zero_le _))
  have hterm : ∀ i ∈ range (N + 1), ∀ j ∈ Ico (N + 1 - i) (N + 1), ‖f i j‖ ≤ K * L * h ^ (N + 1) := by
    intro i hi j hj
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hj' := mem_Ico.mp hj
    simp only [hf, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    refine mul_le_mul (mul_le_mul (hF i hi') (hG j (by omega)) (norm_nonneg _) hK)
      (pow_le_pow_of_le_one h0 h1 (by omega)) (by positivity) (by positivity)
  calc ‖∑ i ∈ range (N + 1), ∑ j ∈ Ico (N + 1 - i) (N + 1), f i j‖
      ≤ ∑ i ∈ range (N + 1), ∑ j ∈ Ico (N + 1 - i) (N + 1), ‖f i j‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i ∈ range (N + 1), ∑ _j ∈ range (N + 1), K * L * h ^ (N + 1) := by
        refine sum_le_sum fun i hi => ?_
        calc ∑ j ∈ Ico (N + 1 - i) (N + 1), ‖f i j‖
            ≤ ∑ _j ∈ Ico (N + 1 - i) (N + 1), K * L * h ^ (N + 1) :=
              sum_le_sum fun j hj => hterm i hi j hj
          _ ≤ ∑ _j ∈ range (N + 1), K * L * h ^ (N + 1) := by
              refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun _ _ _ => by positivity
              exact mem_range.mpr (mem_Ico.mp hj).2
    _ = ((N : ℝ) + 1) ^ 2 * (K * L) * h ^ (N + 1) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

theorem SeriesApprox.mul {z w : ℂ} {F G : PowerSeries ℂ} {N : ℕ} {h K L : ℝ}
    (hz : SeriesApprox z F N h K) (hw : SeriesApprox w G N h L) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    SeriesApprox (z * w) (F * G) N h (3 * ((N : ℝ) + 2) ^ 2 * K * L) := by
  have hK := hz.nonneg
  have hL := hw.nonneg
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hc : ((N : ℝ) + 1) * (K * L) ≤ 3 * ((N : ℝ) + 2) ^ 2 * K * L := by
    have : ((N : ℝ) + 1) ≤ 3 * ((N : ℝ) + 2) ^ 2 := by nlinarith
    have hKL : 0 ≤ K * L := mul_nonneg hK hL
    nlinarith
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [coeff_mul]
    calc ‖∑ p ∈ Finset.antidiagonal k, coeff p.1 F * coeff p.2 G‖
        ≤ ∑ p ∈ Finset.antidiagonal k, ‖coeff p.1 F * coeff p.2 G‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ Finset.antidiagonal k, K * L := by
          refine sum_le_sum fun p hp => ?_
          have hp' := Finset.mem_antidiagonal.mp hp
          rw [norm_mul]
          exact mul_le_mul (hz.1 p.1 (by omega)) (hw.1 p.2 (by omega)) (norm_nonneg _) hK
      _ = ((k : ℝ) + 1) * (K * L) := by
          rw [sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((N : ℝ) + 1) * (K * L) := by
          have : (k : ℝ) ≤ N := by exact_mod_cast hk
          have hKL : 0 ≤ K * L := mul_nonneg hK hL
          nlinarith
      _ ≤ _ := hc
  · set a := truncEval F N h
    set b := truncEval G N h
    have ha : ‖a‖ ≤ (N + 1) * K := norm_truncEval_le h0 h1 hz.1
    have hb : ‖b‖ ≤ (N + 1) * L := norm_truncEval_le h0 h1 hw.1
    have hw' : ‖w‖ ≤ (N + 2) * L := by
      have hp : h ^ (N + 1) ≤ 1 := pow_le_one₀ h0 h1
      have : ‖w‖ ≤ ‖w - b‖ + ‖b‖ := by
        have := norm_add_le (w - b) b
        rwa [sub_add_cancel] at this
      have h2 : ‖w - b‖ ≤ L := hw.2.trans (by nlinarith)
      linarith
    have hm := norm_truncEval_mul_sub_le h0 h1 hz.1 hw.1
    have e : z * w - truncEval (F * G) N h =
        (z - a) * w + a * (w - b) + (a * b - truncEval (F * G) N h) := by ring
    rw [e]
    have hpow : 0 ≤ h ^ (N + 1) := by positivity
    calc ‖(z - a) * w + a * (w - b) + (a * b - truncEval (F * G) N h)‖
        ≤ ‖z - a‖ * ‖w‖ + ‖a‖ * ‖w - b‖ + ‖a * b - truncEval (F * G) N h‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
          rw [norm_mul, norm_mul]
      _ ≤ (K * h ^ (N + 1)) * ((N + 2) * L) + ((N + 1) * K) * (L * h ^ (N + 1)) +
            ((N : ℝ) + 1) ^ 2 * (K * L) * h ^ (N + 1) := by
          gcongr
          · exact hz.2
          · exact hw.2
      _ = ((N + 2) + (N + 1) + ((N : ℝ) + 1) ^ 2) * (K * L) * h ^ (N + 1) := by ring
      _ ≤ 3 * ((N : ℝ) + 2) ^ 2 * K * L * h ^ (N + 1) := by
          have h3 : (N + 2) + (N + 1) + ((N : ℝ) + 1) ^ 2 ≤ 3 * ((N : ℝ) + 2) ^ 2 := by nlinarith
          have hKL : 0 ≤ K * L * h ^ (N + 1) := by positivity
          nlinarith

theorem SeriesApprox.pow {z : ℂ} {F : PowerSeries ℂ} {N : ℕ} {h K : ℝ}
    (hz : SeriesApprox z F N h K) (h0 : 0 ≤ h) (h1 : h ≤ 1) (m : ℕ) :
    SeriesApprox (z ^ m) (F ^ m) N h ((3 * ((N : ℝ) + 2) ^ 2 * K) ^ m) := by
  induction m with
  | zero => simpa using seriesApprox_one N h0
  | succ m ih =>
    have := ih.mul hz h0 h1
    rw [pow_succ, pow_succ]
    refine this.mono h0 (le_of_eq ?_)
    ring

/-! ## Inverses -/

theorem SeriesApprox.inv {z : ℂ} {F : PowerSeries ℂ} {N : ℕ} {h K L σ : ℝ}
    (hz : SeriesApprox z F N h K) (h0 : 0 ≤ h) (h1 : h ≤ 1) (hσ : 0 < σ) (hzσ : σ ≤ ‖z‖)
    (hF0 : constantCoeff F ≠ 0) (hinv : ∀ k ≤ N, ‖coeff k F⁻¹‖ ≤ L) :
    SeriesApprox z⁻¹ F⁻¹ N h (L + 3 * ((N : ℝ) + 2) ^ 2 * K * L / σ) := by
  have hw := seriesApprox_truncEval (F := F⁻¹) h0 hinv
  have hL : 0 ≤ L := hw.nonneg
  have hK := hz.nonneg
  have hm := hz.mul hw h0 h1
  rw [PowerSeries.mul_inv_cancel F hF0] at hm
  have hm2 := hm.2
  rw [truncEval_one] at hm2
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hσ.trans_le hzσ)
  have hzn : 0 < ‖z‖ := hσ.trans_le hzσ
  refine ⟨fun k hk => (hinv k hk).trans (le_add_of_nonneg_right (by positivity)), ?_⟩
  have e : z⁻¹ - truncEval F⁻¹ N h = -(z * truncEval F⁻¹ N h - 1) / z := by
    field_simp
    ring
  rw [e, norm_div, norm_neg, add_mul]
  have hpow : 0 ≤ h ^ (N + 1) := by positivity
  calc ‖z * truncEval F⁻¹ N h - 1‖ / ‖z‖
      ≤ (3 * ((N : ℝ) + 2) ^ 2 * K * L * h ^ (N + 1)) / σ := by
        rw [div_le_div_iff₀ hzn hσ]
        calc ‖z * truncEval F⁻¹ N h - 1‖ * σ
            ≤ (3 * ((N : ℝ) + 2) ^ 2 * K * L * h ^ (N + 1)) * σ := by gcongr
          _ ≤ (3 * ((N : ℝ) + 2) ^ 2 * K * L * h ^ (N + 1)) * ‖z‖ := by gcongr
    _ = 3 * ((N : ℝ) + 2) ^ 2 * K * L / σ * h ^ (N + 1) := by ring
    _ ≤ L * h ^ (N + 1) + 3 * ((N : ℝ) + 2) ^ 2 * K * L / σ * h ^ (N + 1) := by
        have : 0 ≤ L * h ^ (N + 1) := by positivity
        linarith

/-- Coefficients of the inverse of `∑ c_k X^k`. -/
theorem norm_coeff_inv_mk_le {c : ℕ → ℂ} {N : ℕ} {c_lo B : ℝ} (hclo : 0 < c_lo)
    (hc0 : c_lo ≤ ‖c 0‖) (hB : ∀ k ≤ N, ‖c k‖ ≤ B) :
    ∀ k ≤ N, ‖coeff k (PowerSeries.mk c)⁻¹‖ ≤ (((N : ℝ) + 1) * (1 + B / c_lo)) ^ N / c_lo := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  set Λ : ℝ := ((N : ℝ) + 1) * (1 + B / c_lo) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ B / c_lo := div_nonneg hB0 hclo.le
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hc0' : c 0 ≠ 0 := norm_pos_iff.mp (hclo.trans_le hc0)
  have key : ∀ k, k ≤ N → ‖coeff k (PowerSeries.mk c)⁻¹‖ ≤ Λ ^ k / c_lo := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rw [coeff_inv]
      split_ifs with hk0
      · subst hk0
        rw [constantCoeff_mk, norm_inv, pow_zero]
        exact inv_anti₀ hclo hc0 |>.trans_eq (one_div c_lo).symm
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        rw [constantCoeff_mk, norm_mul, norm_neg, norm_inv]
        have hterm : ∀ p ∈ Finset.antidiagonal k,
            ‖if p.2 < k then coeff p.1 (PowerSeries.mk c) * coeff p.2 (PowerSeries.mk c)⁻¹
              else 0‖ ≤ B * (Λ ^ (k - 1) / c_lo) := by
          intro p hp
          have hp' := Finset.mem_antidiagonal.mp hp
          split_ifs with h2
          · rw [coeff_mk, norm_mul]
            refine mul_le_mul (hB p.1 (by omega)) ((ih p.2 h2 (by omega)).trans ?_)
              (norm_nonneg _) hB0
            exact div_le_div_of_nonneg_right (pow_le_pow_right₀ hΛ1 (by omega)) hclo.le
          · rw [norm_zero]
            positivity
        have hsum := (norm_sum_le _ _).trans (sum_le_sum hterm)
        rw [sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul] at hsum
        have hkN : ((k : ℝ) + 1) ≤ (N : ℝ) + 1 := by
          have : (k : ℝ) ≤ N := by exact_mod_cast hk
          linarith
        have hpow : Λ ^ k = Λ ^ (k - 1) * Λ := by
          rw [← pow_succ, Nat.sub_add_cancel hk1]
        have hΛk : 0 ≤ Λ ^ (k - 1) := by positivity
        calc ‖c 0‖⁻¹ * ‖∑ p ∈ Finset.antidiagonal k,
              if p.2 < k then coeff p.1 (PowerSeries.mk c) * coeff p.2 (PowerSeries.mk c)⁻¹
              else 0‖
            ≤ c_lo⁻¹ * (((k + 1 : ℕ) : ℝ) * (B * (Λ ^ (k - 1) / c_lo))) :=
              mul_le_mul (inv_anti₀ hclo hc0) hsum (norm_nonneg _) (inv_nonneg.mpr hclo.le)
          _ ≤ Λ ^ k / c_lo := by
              rw [hpow]
              push_cast
              have hBc : ((k : ℝ) + 1) * (B / c_lo) ≤ Λ := by
                rw [hΛ]
                have : 0 ≤ B / c_lo := div_nonneg hB0 hclo.le
                nlinarith
              have e1 : c_lo⁻¹ * (((k : ℝ) + 1) * (B * (Λ ^ (k - 1) / c_lo))) =
                  (((k : ℝ) + 1) * (B / c_lo)) * Λ ^ (k - 1) / c_lo := by
                field_simp
              rw [e1, div_le_div_iff_of_pos_right hclo]
              nlinarith
  intro k hk
  exact (key k hk).trans (div_le_div_of_nonneg_right (pow_le_pow_right₀ hΛ1 hk) hclo.le)

end

end PGM
