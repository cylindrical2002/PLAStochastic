import PLAStochastic.Swing.Algorithm.Cone
import Mathlib.Tactic

/-!
# Deterministic prefix least-squares estimates

These identities are the algebraic part of the distant-crossing argument in
Appendix `app:limit`.  They deliberately carry no Gaussian or asymptotic
hypothesis: a pathwise envelope for the partial sums can be supplied later.
-/
namespace SwingRepair
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- On the index interval `1,...,N`, the native least-squares coefficient is
the weighted observation sum divided by the time-square sum. -/
theorem nativeLeastSquares_Icc_formula (N : ℕ) (D : ℕ → ℝ) :
    nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 =
      (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * D i) /
        (∑ i ∈ Finset.Icc 1 N, (i : ℝ)^2) := by
  unfold nativeLeastSquares nativeSSECross nativeSSETimeSquare
  simp only [sub_zero]

/-- Closed form for the time-square denominator on `Icc 1 N`. -/
theorem sum_Icc_one_sq_cast_prefix (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, (i : ℝ)^2 =
      (N : ℝ)*((N : ℝ)+1)*(2*(N : ℝ)+1)/6 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1), ih]
    push_cast
    ring

/-- Closed form for the first-power sum on `Icc 1 N`. -/
theorem sum_Icc_one_cast_prefix (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, (i : ℝ) =
      (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1), ih]
    push_cast
    ring

/-- The same least-squares identity with its denominator written explicitly. -/
theorem nativeLeastSquares_Icc_formula_closed (N : ℕ) (D : ℕ → ℝ) :
    nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ)) D 0 0 =
      (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * D i) /
        ((N : ℝ)*((N : ℝ)+1)*(2*(N : ℝ)+1)/6) := by
  rw [nativeLeastSquares_Icc_formula, sum_Icc_one_sq_cast_prefix]

/-- Weighted-sum control from a linear envelope on the observations. -/
theorem weighted_sum_abs_le_of_linear_envelope
    {N : ℕ} {D : ℕ → ℝ} {η : ℝ}
    (_hη : 0 ≤ η)
    (hD : ∀ i ∈ Finset.Icc 1 N, |D i| ≤ η * ((i : ℝ) + 1)) :
    |∑ i ∈ Finset.Icc 1 N, (i : ℝ) * D i| ≤
      η * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * ((i : ℝ) + 1) := by
  calc
    |∑ i ∈ Finset.Icc 1 N, (i : ℝ) * D i| ≤
        ∑ i ∈ Finset.Icc 1 N, |(i : ℝ) * D i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (η * ((i : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg i)]
      exact mul_le_mul_of_nonneg_left (hD i hi) (Nat.cast_nonneg i)
    _ = η * ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * ((i : ℝ) + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The elementary closed form for the weight `i(i+1)`. -/
theorem sum_Icc_one_mul_succ_cast_prefix (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * ((i : ℝ) + 1) =
      (N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) / 3 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1), ih]
    push_cast
    ring

/-- Tail-envelope form used for partial sums: if
`|W_(i-1)| ≤ η i` on the accepted index interval, its weighted contribution
is at most `η` times the sum of squares. -/
theorem weighted_cumulativeSamples_bound_of_tail
    {N : ℕ} {W : ℕ → ℝ} {η : ℝ}
    (_hη : 0 ≤ η)
    (hW : ∀ i ∈ Finset.Icc 1 N,
      |W (i-1)| ≤ η * (i : ℝ)) :
    |∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i-1)| ≤
      η * ∑ i ∈ Finset.Icc 1 N, (i : ℝ)^2 := by
  calc
    |∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i-1)| ≤
        ∑ i ∈ Finset.Icc 1 N, |(i : ℝ) * W (i-1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (η * (i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg i)]
      exact mul_le_mul_of_nonneg_left (hW i hi) (Nat.cast_nonneg i)
    _ = η * ∑ i ∈ Finset.Icc 1 N, (i : ℝ)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Closed form of the preceding weighted partial-sum estimate. -/
theorem weighted_cumulativeSamples_bound_of_tail_closed
    {N : ℕ} {W : ℕ → ℝ} {η : ℝ}
    (_hη : 0 ≤ η)
    (hW : ∀ i ∈ Finset.Icc 1 N,
      |W (i-1)| ≤ η * (i : ℝ)) :
    |∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i-1)| ≤
      η * ((N : ℝ)*((N : ℝ)+1)*(2*(N : ℝ)+1)/6) := by
  calc
    |∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i-1)| ≤
        η * ∑ i ∈ Finset.Icc 1 N, (i : ℝ)^2 :=
      weighted_cumulativeSamples_bound_of_tail _hη hW
    _ = η * ((N : ℝ)*((N : ℝ)+1)*(2*(N : ℝ)+1)/6) := by
      rw [sum_Icc_one_sq_cast_prefix]

/-! ## Deterministic selector bridge

Once the lower cone endpoint has been identified with the prefix slope, the
remaining selector step is purely algebraic: an unconstrained least-squares
coefficient below that endpoint is clipped to the endpoint. -/

theorem nativeClippedSlope_eq_lower_of_le {L U C : ℝ} (hC : C ≤ L) :
    nativeClippedSlope L U C = L := by
  unfold nativeClippedSlope
  apply max_eq_left
  exact (min_le_left C U).trans hC

theorem nativeSelectedSlope_eq_nativeConeLower_of_le
    {ι : Type*} {samples : Finset ι} (hne : samples.Nonempty)
    {t y : ι → ℝ} {a q ε : ℝ}
    (hC : nativeLeastSquares samples t y a q ≤
      nativeConeLower samples hne t y a q ε) :
    nativeSelectedSlope samples hne t y a q ε =
      nativeConeLower samples hne t y a q ε := by
  unfold nativeSelectedSlope
  exact nativeClippedSlope_eq_lower_of_le hC

theorem nativeSelectedSlope_eq_of_lower_endpoint
    {ι : Type*} {samples : Finset ι} (hne : samples.Nonempty)
    {t y : ι → ℝ} {a q ε A : ℝ}
    (hlower : nativeConeLower samples hne t y a q ε = A)
    (hC : nativeLeastSquares samples t y a q ≤ A) :
    nativeSelectedSlope samples hne t y a q ε = A := by
  rw [nativeSelectedSlope, hlower]
  exact nativeClippedSlope_eq_lower_of_le hC

/-! ### A closed least-squares upper bound

The next estimate is the quantitative algebra used in the distant-crossing
argument.  It separates the deterministic weighted-sum calculation from the
probabilistic assertion that the partial sums are sublinear. -/

theorem nativeLeastSquares_Icc_const_add_bound
    {N : ℕ} (hN : 1 ≤ N) {c η : ℝ} (hη : 0 ≤ η)
    {W : ℕ → ℝ}
    (hW : ∀ i ∈ Finset.Icc 1 N,
      |W (i - 1)| ≤ η * (i : ℝ)) :
    nativeLeastSquares (Finset.Icc 1 N) (fun i => (i : ℝ))
        (fun i => c + W (i - 1)) 0 0 ≤
      3 * c / (2 * (N : ℝ) + 1) + η := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdenpos : 0 <
      (N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6 := by
    positivity
  have hWsum := weighted_cumulativeSamples_bound_of_tail_closed hη hW
  have hsumid :
      (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (c + W (i - 1))) =
        c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
          ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) := by
    calc
      (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * (c + W (i - 1))) =
          ∑ i ∈ Finset.Icc 1 N,
            ((i : ℝ) * c + (i : ℝ) * W (i - 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * c) +
          ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) := by
        rw [Finset.sum_add_distrib]
      _ = c * (∑ i ∈ Finset.Icc 1 N, (i : ℝ)) +
          ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) := by
        congr 1
        calc
          (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * c) =
              ∑ i ∈ Finset.Icc 1 N, c * (i : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = c * (∑ i ∈ Finset.Icc 1 N, (i : ℝ)) := by
            rw [Finset.mul_sum]
      _ = c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
          ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) := by
        rw [sum_Icc_one_cast_prefix]
  rw [nativeLeastSquares_Icc_formula_closed, hsumid]
  have hWupper :
      ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1) ≤
        η * ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) := by
    exact le_trans (le_abs_self _) hWsum
  have hratio :
      (c * ((N : ℝ) * ((N : ℝ) + 1) / 2)) /
          ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) =
        3 * c / (2 * (N : ℝ) + 1) := by
    field_simp
    ring
  rw [show
      (c * ((N : ℝ) * ((N : ℝ) + 1) / 2) +
        ∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1)) /
          ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) =
      (c * ((N : ℝ) * ((N : ℝ) + 1) / 2)) /
          ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) +
        (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1)) /
          ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) by
    ring]
  rw [hratio]
  have hηdiv :
      (∑ i ∈ Finset.Icc 1 N, (i : ℝ) * W (i - 1)) /
          ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) ≤ η := by
    apply (div_le_iff₀ hdenpos).2
    exact hWupper
  linarith

theorem nativeSelectedSlope_eq_of_const_add_bound
    {N : ℕ} (hN : 1 ≤ N) {c η A : ℝ} (hη : 0 ≤ η)
    {W : ℕ → ℝ}
    (hW : ∀ i ∈ Finset.Icc 1 N,
      |W (i - 1)| ≤ η * (i : ℝ))
    (hlower : nativeConeLower (Finset.Icc 1 N)
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => c + W (i - 1)) 0 0 0 = A)
    (hbound : 3 * c / (2 * (N : ℝ) + 1) + η ≤ A) :
    nativeSelectedSlope (Finset.Icc 1 N)
      (Finset.nonempty_Icc.mpr hN) (fun i => (i : ℝ))
      (fun i => c + W (i - 1)) 0 0 0 = A := by
  apply nativeSelectedSlope_eq_of_lower_endpoint (Finset.nonempty_Icc.mpr hN)
    hlower
  exact (nativeLeastSquares_Icc_const_add_bound hN hη hW).trans hbound

end
end SwingRepair
