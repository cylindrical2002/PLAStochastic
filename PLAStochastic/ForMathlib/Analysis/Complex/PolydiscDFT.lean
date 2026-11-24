import PLAStochastic.ForMathlib.Analysis.Complex.FiniteBoxTaylor
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Coordinate coefficients of box polynomials from a finite Fourier average

Let `Q x = ∑_{β ∈ box n} c β ∏ᵢ xᵢ^{βᵢ}` be a polynomial in `d` complex variables of degree at
most `n` in each variable, and let `ω` be a primitive `(n+1)`-st root of unity. Averaging over the
grid `xᵢ = r ω^{kᵢ}` recovers every coefficient:

* `sum_dft_coordinate_box`: `∑_k Q(r ω^k) ∏ᵢ ω^{kᵢ (n+1-αᵢ)} = (n+1)^d r^{|α|} c α`;
* `norm_coeff_mul_pow_le_of_torus`: hence `‖c α‖ r^{|α|}` is at most any bound of `‖Q‖` on the
  polytorus `|xᵢ| = r` (a finite form of the Cauchy estimate).

Only finite sums are used.
-/

noncomputable section
open Complex Finset
namespace PGM

/-- The primitive `(n+1)`-st root of unity `exp(2πi/(n+1))`. -/
def polydiscRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n + 1 : ℕ) : ℂ))

theorem polydiscRoot_isPrimitiveRoot (n : ℕ) : IsPrimitiveRoot (polydiscRoot n) (n + 1) :=
  Complex.isPrimitiveRoot_exp (n + 1) (Nat.succ_ne_zero n)

theorem norm_polydiscRoot_pow (n m : ℕ) : ‖polydiscRoot n ^ m‖ = 1 := by
  rw [norm_pow, (polydiscRoot_isPrimitiveRoot n).norm'_eq_one (Nat.succ_ne_zero n), one_pow]

/-- Full-period sums of powers of a primitive root of unity. -/
theorem sum_fin_pow_mul_of_isPrimitiveRoot {ω : ℂ} {n : ℕ} (hω : IsPrimitiveRoot ω (n + 1))
    (m : ℕ) :
    ∑ j : Fin (n + 1), ω ^ ((j : ℕ) * m) = if (n + 1) ∣ m then ((n + 1 : ℕ) : ℂ) else 0 := by
  have hsum : ∑ j : Fin (n + 1), ω ^ ((j : ℕ) * m) = ∑ j ∈ range (n + 1), (ω ^ m) ^ j := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ω ^ (j * m)) (n + 1)]
    exact sum_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  rw [hsum]
  split_ifs with h
  · have h1 : ω ^ m = 1 := (hω.pow_eq_one_iff_dvd m).mpr h
    simp [h1]
  · have h1 : ω ^ m ≠ 1 := fun h' => h ((hω.pow_eq_one_iff_dvd m).mp h')
    have h2 : (ω ^ m) ^ (n + 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have h3 := mul_geom_sum (ω ^ m) (n + 1)
    rw [h2, sub_self] at h3
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h1)

/-- For exponents in `[0, n]`, the shifted difference is divisible by `n+1` only on the
diagonal. -/
theorem dvd_add_sub_iff_eq {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    (n + 1) ∣ b + (n + 1 - a) ↔ b = a := by
  constructor
  · rintro ⟨q, hq⟩
    have h1 : 0 < b + (n + 1 - a) := by omega
    have h2 : b + (n + 1 - a) < 2 * (n + 1) := by omega
    have hq1 : q = 1 := by
      rcases Nat.lt_or_ge q 2 with h | h
      · interval_cases q <;> omega
      · have : (n + 1) * 2 ≤ (n + 1) * q := Nat.mul_le_mul_left _ h
        omega
    subst hq1
    omega
  · rintro rfl
    exact ⟨1, by omega⟩

/-- **Finite Fourier extraction.** The grid average of a box polynomial against the conjugate
characters recovers its coordinate coefficients. -/
theorem sum_dft_coordinate_box {d n : ℕ} {ω : ℂ} (hω : IsPrimitiveRoot ω (n + 1))
    (c : (Fin d → ℕ) → ℂ) (r : ℂ) {α : Fin d → ℕ}
    (hα : α ∈ finiteCoordinateTaylorBox d n) :
    ∑ k : Fin d → Fin (n + 1),
        (∑ β ∈ finiteCoordinateTaylorBox d n, c β * ∏ i, (r * ω ^ (k i : ℕ)) ^ β i) *
          ∏ i, ω ^ ((k i : ℕ) * (n + 1 - α i)) =
      ((n + 1 : ℕ) : ℂ) ^ d * r ^ (∑ i, α i) * c α := by
  classical
  have hα' := mem_finiteCoordinateTaylorBox.mp hα
  have hterm : ∀ (k : Fin d → Fin (n + 1)) (β : Fin d → ℕ),
      (∏ i, (r * ω ^ (k i : ℕ)) ^ β i) * ∏ i, ω ^ ((k i : ℕ) * (n + 1 - α i)) =
        r ^ (∑ i, β i) * ∏ i, ω ^ ((k i : ℕ) * (β i + (n + 1 - α i))) := by
    intro k β
    rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, mul_add]
  have hfactor : ∀ β ∈ finiteCoordinateTaylorBox d n,
      (∏ i, ∑ j : Fin (n + 1), ω ^ ((j : ℕ) * (β i + (n + 1 - α i)))) =
        if β = α then ((n + 1 : ℕ) : ℂ) ^ d else 0 := by
    intro β hβ
    have hβ' := mem_finiteCoordinateTaylorBox.mp hβ
    simp_rw [sum_fin_pow_mul_of_isPrimitiveRoot hω, dvd_add_sub_iff_eq (hα' _) (hβ' _)]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨i, hi⟩ : ∃ i, β i ≠ α i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      exact prod_eq_zero (mem_univ i) (if_neg hi)
  calc
    _ = ∑ k : Fin d → Fin (n + 1), ∑ β ∈ finiteCoordinateTaylorBox d n,
          c β * (r ^ (∑ i, β i) * ∏ i, ω ^ ((k i : ℕ) * (β i + (n + 1 - α i)))) := by
        refine sum_congr rfl fun k _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun β _ => ?_
        rw [mul_assoc, hterm]
    _ = ∑ β ∈ finiteCoordinateTaylorBox d n, c β * r ^ (∑ i, β i) *
          ∏ i, ∑ j : Fin (n + 1), ω ^ ((j : ℕ) * (β i + (n + 1 - α i))) := by
        rw [sum_comm]
        refine sum_congr rfl fun β _ => ?_
        rw [Fintype.prod_sum, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        ring
    _ = ∑ β ∈ finiteCoordinateTaylorBox d n,
          if β = α then c β * r ^ (∑ i, β i) * ((n + 1 : ℕ) : ℂ) ^ d else 0 := by
        refine sum_congr rfl fun β hβ => ?_
        rw [hfactor β hβ]
        split_ifs <;> simp
    _ = _ := by
        rw [sum_ite_eq' _ α, if_pos hα]
        ring

/-- **Cauchy estimate for box polynomials.** A bound of a box polynomial on the polytorus of
radius `r` bounds every coefficient times `r^{|α|}`. -/
theorem norm_coeff_mul_pow_le_of_torus {d n : ℕ} (c : (Fin d → ℕ) → ℂ) {r B : ℝ} (hr : 0 ≤ r)
    {α : Fin d → ℕ} (hα : α ∈ finiteCoordinateTaylorBox d n)
    (hB : ∀ x : Fin d → ℂ, (∀ i, ‖x i‖ = r) →
      ‖∑ β ∈ finiteCoordinateTaylorBox d n, c β * ∏ i, x i ^ β i‖ ≤ B) :
    ‖c α‖ * r ^ (∑ i, α i) ≤ B := by
  classical
  have hω := polydiscRoot_isPrimitiveRoot n
  have h := sum_dft_coordinate_box hω c (r : ℂ) hα
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ d := by positivity
  have hnorm : ‖((n + 1 : ℕ) : ℂ) ^ d * (r : ℂ) ^ (∑ i, α i) * c α‖ =
      ((n + 1 : ℕ) : ℝ) ^ d * (‖c α‖ * r ^ (∑ i, α i)) := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hr]
    ring
  have hle : ‖∑ k : Fin d → Fin (n + 1),
      (∑ β ∈ finiteCoordinateTaylorBox d n,
          c β * ∏ i, ((r : ℂ) * polydiscRoot n ^ (k i : ℕ)) ^ β i) *
        ∏ i, polydiscRoot n ^ ((k i : ℕ) * (n + 1 - α i))‖ ≤ ((n + 1 : ℕ) : ℝ) ^ d * B := by
    calc
      _ ≤ ∑ k : Fin d → Fin (n + 1), ‖(∑ β ∈ finiteCoordinateTaylorBox d n,
            c β * ∏ i, ((r : ℂ) * polydiscRoot n ^ (k i : ℕ)) ^ β i) *
          ∏ i, polydiscRoot n ^ ((k i : ℕ) * (n + 1 - α i))‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin d → Fin (n + 1), B := by
        refine sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_prod]
        simp_rw [norm_polydiscRoot_pow]
        rw [prod_const_one, mul_one]
        refine hB _ fun i => ?_
        rw [norm_mul, norm_polydiscRoot_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]
      _ = ((n + 1 : ℕ) : ℝ) ^ d * B := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring
  rw [h, hnorm] at hle
  exact le_of_mul_le_mul_left hle hpos

end PGM
