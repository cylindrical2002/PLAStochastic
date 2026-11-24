import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseArithmetic
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Finite inverse-power expansions indexed by formal power series

`HasSeriesExpansionAtOrder f F P` says that `f ε` has the finite expansion of order `P` whose
coefficients are those of the formal power series `F` in `h = ε⁻¹`. Finite expansions of this
kind are closed under sums, products, powers and finite products, with the formal product as
coefficient series; only the truncations through order `P` are ever evaluated. Coefficients of
products of series without constant term vanish below the total order, and depend only on the
low coefficients of the factors.
-/

namespace PGM

noncomputable section

open Filter Topology Finset PowerSeries
open scoped Polynomial

/-- A real function expands to order `P` with the coefficients of a formal power series. -/
def HasSeriesExpansionAtOrder (f : ℝ → ℝ) (F : PowerSeries ℝ) (P : ℕ) : Prop :=
  HasInverseExpansionAtOrder f (fun n => coeff n F) P

theorem eval_trunc_eq_inversePolynomial (F : PowerSeries ℝ) (P : ℕ) (eps : ℝ) :
    (trunc (P + 1) F).eval eps⁻¹ = inversePolynomial (fun n => coeff n F) P eps := by
  rw [trunc_apply, Polynomial.eval_finsetSum, inversePolynomial, Nat.Ico_zero_eq_range]
  exact sum_congr rfl fun n _ => by rw [Polynomial.eval_monomial]

theorem HasSeriesExpansionAtOrder.truncate {f : ℝ → ℝ} {F : PowerSeries ℝ} {P N : ℕ}
    (h : HasSeriesExpansionAtOrder f F P) (hN : N ≤ P) : HasSeriesExpansionAtOrder f F N :=
  HasInverseExpansionAtOrder.truncate h hN

theorem HasSeriesExpansionAtOrder.congr {f g : ℝ → ℝ} {F : PowerSeries ℝ} {P : ℕ}
    (h : HasSeriesExpansionAtOrder f F P) (he : ∀ᶠ eps in atTop, f eps = g eps) :
    HasSeriesExpansionAtOrder g F P := by
  obtain ⟨K, e0, hK⟩ := h
  obtain ⟨e1, he1⟩ := eventually_atTop.mp he
  refine ⟨K, max e0 e1, fun eps heps => ?_⟩
  rw [← he1 eps ((le_max_right _ _).trans heps)]
  exact hK eps ((le_max_left _ _).trans heps)

theorem HasSeriesExpansionAtOrder.congr_series {f : ℝ → ℝ} {F G : PowerSeries ℝ} {P : ℕ}
    (h : HasSeriesExpansionAtOrder f F P) (hc : ∀ n ≤ P, coeff n F = coeff n G) :
    HasSeriesExpansionAtOrder f G P := by
  obtain ⟨K, e0, hK⟩ := h
  refine ⟨K, e0, fun eps heps => ?_⟩
  have he : inversePolynomial (fun n => coeff n G) P eps =
      inversePolynomial (fun n => coeff n F) P eps :=
    sum_congr rfl fun n hn => by
      show coeff n G * _ = coeff n F * _
      rw [hc n (by have := mem_range.mp hn; omega)]
  rw [he]
  exact hK eps heps

theorem hasSeriesExpansionAtOrder_const (c : ℝ) (P : ℕ) :
    HasSeriesExpansionAtOrder (fun _ => c) (C c) P := by
  refine ⟨0, 1, fun eps _ => ?_⟩
  have he : inversePolynomial (fun n => coeff n (C c : PowerSeries ℝ)) P eps = c := by
    rw [inversePolynomial, sum_range_succ']
    simp [coeff_C]
  rw [he, sub_self, abs_zero, zero_mul]

theorem HasSeriesExpansionAtOrder.add {f g : ℝ → ℝ} {F G : PowerSeries ℝ} {P : ℕ}
    (hf : HasSeriesExpansionAtOrder f F P) (hg : HasSeriesExpansionAtOrder g G P) :
    HasSeriesExpansionAtOrder (fun eps => f eps + g eps) (F + G) P := by
  have h := HasInverseExpansionAtOrder.remainder hf |>.add (HasInverseExpansionAtOrder.remainder hg)
  have he (eps : ℝ) : f eps + g eps - inversePolynomial (fun n => coeff n (F + G)) P eps =
      (f eps - inversePolynomial (fun n => coeff n F) P eps) +
        (g eps - inversePolynomial (fun n => coeff n G) P eps) := by
    simp only [inversePolynomial, map_add, add_mul, sum_add_distrib]
    ring
  simpa only [HasSeriesExpansionAtOrder, HasInverseExpansionAtOrder, IsInverseOrder, he] using h

theorem HasSeriesExpansionAtOrder.neg {f : ℝ → ℝ} {F : PowerSeries ℝ} {P : ℕ}
    (hf : HasSeriesExpansionAtOrder f F P) :
    HasSeriesExpansionAtOrder (fun eps => -f eps) (-F) P := by
  have h := (HasInverseExpansionAtOrder.remainder hf).neg
  have he (eps : ℝ) : -f eps - inversePolynomial (fun n => coeff n (-F)) P eps =
      -(f eps - inversePolynomial (fun n => coeff n F) P eps) := by
    simp only [inversePolynomial, map_neg, neg_mul, sum_neg_distrib]
    ring
  simpa only [HasSeriesExpansionAtOrder, HasInverseExpansionAtOrder, IsInverseOrder, he] using h

theorem HasSeriesExpansionAtOrder.sub {f g : ℝ → ℝ} {F G : PowerSeries ℝ} {P : ℕ}
    (hf : HasSeriesExpansionAtOrder f F P) (hg : HasSeriesExpansionAtOrder g G P) :
    HasSeriesExpansionAtOrder (fun eps => f eps - g eps) (F - G) P := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The truncated polynomial of a series is eventually bounded. -/
theorem inversePolynomial_series_bounded (F : PowerSeries ℝ) (P : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ eps in atTop, |inversePolynomial (fun n => coeff n F) P eps| ≤ B := by
  obtain ⟨B, hB, hb⟩ := (polynomial_hasInverseExpansion (trunc (P + 1) F) 0).bounded
  refine ⟨B, hB, hb.mono fun eps he => ?_⟩
  rwa [eval_trunc_eq_inversePolynomial] at he

/-- **Products.** The formal product supplies the coefficients of the product. -/
theorem HasSeriesExpansionAtOrder.mul {f g : ℝ → ℝ} {F G : PowerSeries ℝ} {P : ℕ}
    (hf : HasSeriesExpansionAtOrder f F P) (hg : HasSeriesExpansionAtOrder g G P) :
    HasSeriesExpansionAtOrder (fun eps => f eps * g eps) (F * G) P := by
  set pf := fun eps => inversePolynomial (fun n => coeff n F) P eps
  set pg := fun eps => inversePolynomial (fun n => coeff n G) P eps
  have h1 : IsInverseOrder (fun eps => (f eps - pf eps) * g eps) (P + 1) := by
    obtain ⟨B, -, hB⟩ := HasInverseExpansionAtOrder.bounded hg
    exact (HasInverseExpansionAtOrder.remainder hf).mul_bounded ⟨B, hB⟩
  have h2 : IsInverseOrder (fun eps => (g eps - pg eps) * pf eps) (P + 1) := by
    obtain ⟨B, -, hB⟩ := inversePolynomial_series_bounded F P
    exact (HasInverseExpansionAtOrder.remainder hg).mul_bounded ⟨B, hB⟩
  -- the product of the two truncations against the truncated product
  set q : ℝ[X] := trunc (P + 1) F * trunc (P + 1) G
  have hq : ∀ n ≤ P, q.coeff n = coeff n (F * G) := by
    intro n hn
    have ht := congrArg (fun p : ℝ[X] => p.coeff n)
      (trunc_trunc_mul_trunc (n := P + 1) F G)
    simp only [coeff_trunc, if_pos (Nat.lt_succ_of_le hn)] at ht
    rw [← ht, ← Polynomial.coeff_coe, Polynomial.coe_mul]
  have h3 : IsInverseOrder (fun eps => pf eps * pg eps -
      inversePolynomial (fun n => coeff n (F * G)) P eps) (P + 1) := by
    have hp := polynomial_hasInverseExpansion q P
    have he (eps : ℝ) : pf eps * pg eps = q.eval eps⁻¹ := by
      simp only [pf, pg, q, Polynomial.eval_mul, eval_trunc_eq_inversePolynomial]
    have hpoly (eps : ℝ) : inversePolynomial q.coeff P eps =
        inversePolynomial (fun n => coeff n (F * G)) P eps :=
      sum_congr rfl fun n hn => by rw [hq n (by have := mem_range.mp hn; omega)]
    simpa only [HasInverseExpansionAtOrder, IsInverseOrder, he, hpoly] using hp
  have h := (h1.add h2).add h3
  have heq (eps : ℝ) : f eps * g eps - inversePolynomial (fun n => coeff n (F * G)) P eps =
      (f eps - pf eps) * g eps + (g eps - pg eps) * pf eps +
        (pf eps * pg eps - inversePolynomial (fun n => coeff n (F * G)) P eps) := by ring
  simpa only [HasSeriesExpansionAtOrder, HasInverseExpansionAtOrder, IsInverseOrder, heq] using h

theorem HasSeriesExpansionAtOrder.const_mul {f : ℝ → ℝ} {F : PowerSeries ℝ} {P : ℕ}
    (hf : HasSeriesExpansionAtOrder f F P) (c : ℝ) :
    HasSeriesExpansionAtOrder (fun eps => c * f eps) (C c * F) P :=
  (hasSeriesExpansionAtOrder_const c P).mul hf

theorem HasSeriesExpansionAtOrder.pow {f : ℝ → ℝ} {F : PowerSeries ℝ} {P : ℕ}
    (hf : HasSeriesExpansionAtOrder f F P) (k : ℕ) :
    HasSeriesExpansionAtOrder (fun eps => f eps ^ k) (F ^ k) P := by
  induction k with
  | zero =>
    simpa only [pow_zero, map_one] using hasSeriesExpansionAtOrder_const 1 P
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem HasSeriesExpansionAtOrder.prod {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    {F : ι → PowerSeries ℝ} {P : ℕ} (hf : ∀ i ∈ s, HasSeriesExpansionAtOrder (f i) (F i) P) :
    HasSeriesExpansionAtOrder (fun eps => ∏ i ∈ s, f i eps) (∏ i ∈ s, F i) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [prod_empty, map_one] using hasSeriesExpansionAtOrder_const 1 P
  | insert a s ha ih =>
    simp only [prod_insert ha]
    exact (hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem HasSeriesExpansionAtOrder.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    {F : ι → PowerSeries ℝ} {P : ℕ} (hf : ∀ i ∈ s, HasSeriesExpansionAtOrder (f i) (F i) P) :
    HasSeriesExpansionAtOrder (fun eps => ∑ i ∈ s, f i eps) (∑ i ∈ s, F i) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [sum_empty, map_zero] using hasSeriesExpansionAtOrder_const 0 P
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

/-- A higher inverse order implies a lower one. -/
theorem IsInverseOrder.mono {f : ℝ → ℝ} {n m : ℕ} (hf : IsInverseOrder f n) (hmn : m ≤ n) :
    IsInverseOrder f m := by
  obtain ⟨K, e0, hK, he0, hb⟩ := hf.nonneg_witness
  refine ⟨K, e0, fun eps he => (hb eps he).trans (mul_le_mul_of_nonneg_left ?_ hK)⟩
  have he1 : 1 ≤ eps := he0.trans he
  exact pow_le_pow_of_le_one (by positivity) ((inv_le_one₀ (by linarith)).mpr he1) hmn

/-- A series without constant term gives a function of the first inverse order. -/
theorem HasSeriesExpansionAtOrder.isInverseOrder_one {f : ℝ → ℝ} {F : PowerSeries ℝ} {P : ℕ}
    (hf : HasSeriesExpansionAtOrder f F P) (h0 : constantCoeff F = 0) : IsInverseOrder f 1 := by
  have hp := polynomial_hasInverseExpansion (trunc (P + 1) F) 0
  have hr : IsInverseOrder (fun eps => f eps - inversePolynomial (fun n => coeff n F) P eps) 1 :=
    (HasInverseExpansionAtOrder.remainder hf).mono (by omega)
  have hpoly : IsInverseOrder (fun eps => inversePolynomial (fun n => coeff n F) P eps) 1 := by
    have hc : (trunc (P + 1) F).coeff 0 = 0 := by
      rw [coeff_trunc, if_pos (Nat.succ_pos P), coeff_zero_eq_constantCoeff, h0]
    obtain ⟨K, e0, hK⟩ := hp
    refine ⟨K, e0, fun eps he => ?_⟩
    have h := hK eps he
    simp only [inversePolynomial, zero_add, sum_range_one, pow_zero, mul_one, hc, sub_zero,
      eval_trunc_eq_inversePolynomial] at h
    simpa only [inversePolynomial, pow_one] using h
  have h := hr.add hpoly
  simpa only [sub_add_cancel] using h

/-! ## Coefficients of products of series without constant term -/

/-- The coefficient of order `n` of `∏ Yᵢ^{αᵢ}` vanishes if some `αᵢ > n` and the `Yᵢ` have
no constant term. -/
theorem coeff_prod_pow_eq_zero {ι : Type*} (s : Finset ι) (Y : ι → PowerSeries ℝ)
    (α : ι → ℕ) (hY : ∀ i ∈ s, constantCoeff (Y i) = 0) {n : ℕ} {i : ι} (hi : i ∈ s)
    (hn : n < α i) : coeff n (∏ j ∈ s, Y j ^ α j) = 0 := by
  have hX : (X : PowerSeries ℝ) ∣ Y i := X_dvd_iff.mpr (hY i hi)
  have hd : (X : PowerSeries ℝ) ^ α i ∣ ∏ j ∈ s, Y j ^ α j :=
    (pow_dvd_pow_of_dvd hX (α i)).trans (dvd_prod_of_mem (fun j => Y j ^ α j) hi)
  obtain ⟨Z, hZ⟩ := hd
  rw [hZ, coeff_X_pow_mul', if_neg (by omega)]

/-- The truncation of a product of powers depends only on the truncations of the factors. -/
theorem trunc_prod_pow_trunc {ι : Type*} (s : Finset ι) (Y : ι → PowerSeries ℝ) (α : ι → ℕ)
    (n : ℕ) :
    trunc n (∏ i ∈ s, ((trunc n (Y i) : ℝ[X]) : PowerSeries ℝ) ^ α i) =
      trunc n (∏ i ∈ s, Y i ^ α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, ← trunc_trunc_mul_trunc, trunc_trunc_pow, ih,
      trunc_trunc_mul_trunc]

/-- Coefficients of products of powers depend only on the low coefficients of the factors. -/
theorem coeff_prod_pow_congr {ι : Type*} (s : Finset ι) (Y Y' : ι → PowerSeries ℝ)
    (α : ι → ℕ) {n : ℕ} (h : ∀ i ∈ s, ∀ j ≤ n, coeff j (Y i) = coeff j (Y' i)) :
    coeff n (∏ i ∈ s, Y i ^ α i) = coeff n (∏ i ∈ s, Y' i ^ α i) := by
  have ht : ∀ i ∈ s, trunc (n + 1) (Y i) = trunc (n + 1) (Y' i) := by
    intro i hi
    ext j
    simp only [coeff_trunc]
    split_ifs with hj
    · exact h i hi j (by omega)
    · rfl
  have hs : (∏ i ∈ s, ((trunc (n + 1) (Y i) : ℝ[X]) : PowerSeries ℝ) ^ α i) =
      ∏ i ∈ s, ((trunc (n + 1) (Y' i) : ℝ[X]) : PowerSeries ℝ) ^ α i :=
    prod_congr rfl fun i hi => by rw [ht i hi]
  have h1 := congrArg (fun p : ℝ[X] => p.coeff n) (trunc_prod_pow_trunc s Y α (n + 1))
  have h2 := congrArg (fun p : ℝ[X] => p.coeff n) (trunc_prod_pow_trunc s Y' α (n + 1))
  simp only [coeff_trunc, if_pos (Nat.lt_succ_self n)] at h1 h2
  rw [← h1, ← h2, hs]

end

end PGM
