import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseExpansion
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite arithmetic of inverse-power expansions

The estimates are at fixed order. Polynomial products are truncated only after
multiplication, so no convergence of an infinite formal series is required.
-/

namespace PGM

noncomputable section

open Filter Topology Finset
open scoped Polynomial

theorem IsInverseOrder.of_eventually_abs_le {f : ℝ → ℝ} {n : ℕ} {K : ℝ}
    (h : ∀ᶠ eps in atTop, |f eps| ≤ K * (eps⁻¹) ^ n) : IsInverseOrder f n := by
  obtain ⟨e0, he0⟩ := eventually_atTop.mp h
  exact ⟨K, e0, he0⟩

theorem IsInverseOrder.add {f g : ℝ → ℝ} {n : ℕ}
    (hf : IsInverseOrder f n) (hg : IsInverseOrder g n) :
    IsInverseOrder (fun eps => f eps + g eps) n := by
  obtain ⟨Kf, ef, hf⟩ := hf
  obtain ⟨Kg, eg, hg⟩ := hg
  refine ⟨Kf + Kg, max ef eg, fun eps heps => ?_⟩
  calc
    |f eps + g eps| ≤ |f eps| + |g eps| := abs_add_le _ _
    _ ≤ Kf * (eps⁻¹) ^ n + Kg * (eps⁻¹) ^ n :=
      add_le_add (hf eps ((le_max_left _ _).trans heps)) (hg eps ((le_max_right _ _).trans heps))
    _ = (Kf + Kg) * (eps⁻¹) ^ n := by ring

theorem IsInverseOrder.neg {f : ℝ → ℝ} {n : ℕ} (hf : IsInverseOrder f n) :
    IsInverseOrder (fun eps => -f eps) n := by
  simpa only [IsInverseOrder, abs_neg] using hf

theorem IsInverseOrder.sub {f g : ℝ → ℝ} {n : ℕ}
    (hf : IsInverseOrder f n) (hg : IsInverseOrder g n) :
    IsInverseOrder (fun eps => f eps - g eps) n := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsInverseOrder.mul {f g : ℝ → ℝ} {m n : ℕ}
    (hf : IsInverseOrder f m) (hg : IsInverseOrder g n) :
    IsInverseOrder (fun eps => f eps * g eps) (m + n) := by
  obtain ⟨Kf, ef, hKf, hef, hf⟩ := hf.nonneg_witness
  obtain ⟨Kg, eg, hKg, heg, hg⟩ := hg.nonneg_witness
  refine ⟨Kf * Kg, max ef eg, fun eps heps => ?_⟩
  have he1 : 1 ≤ eps := hef.trans ((le_max_left _ _).trans heps)
  rw [abs_mul, pow_add]
  calc
    |f eps| * |g eps| ≤ (Kf * (eps⁻¹) ^ m) * (Kg * (eps⁻¹) ^ n) :=
      mul_le_mul (hf eps ((le_max_left _ _).trans heps))
        (hg eps ((le_max_right _ _).trans heps)) (abs_nonneg _) (by positivity)
    _ = Kf * Kg * ((eps⁻¹) ^ m * (eps⁻¹) ^ n) := by ring

theorem IsInverseOrder.mul_bounded {f g : ℝ → ℝ} {n : ℕ}
    (hf : IsInverseOrder f n) (hg : ∃ B : ℝ, ∀ᶠ eps in atTop, |g eps| ≤ B) :
    IsInverseOrder (fun eps => f eps * g eps) n := by
  obtain ⟨B, hg⟩ := hg
  have hg' : IsInverseOrder g 0 := .of_eventually_abs_le (by simpa only [pow_zero, mul_one] using hg)
  simpa only [Nat.add_zero] using hf.mul hg'

theorem IsInverseOrder.const_mul {f : ℝ → ℝ} {n : ℕ} (hf : IsInverseOrder f n) (c : ℝ) :
    IsInverseOrder (fun eps => c * f eps) n := by
  have h := hf.mul_bounded ⟨|c|, Eventually.of_forall fun _ => le_rfl⟩
  simpa only [mul_comm] using h

theorem IsInverseOrder.pow {f : ℝ → ℝ} {n : ℕ} (hf : IsInverseOrder f n) (k : ℕ) :
    IsInverseOrder (fun eps => f eps ^ k) (n * k) := by
  induction k with
  | zero => exact ⟨1, 1, fun _ _ => by simp⟩
  | succ k ih => simpa only [pow_succ, Nat.mul_succ] using ih.mul hf

theorem HasInverseExpansionAtOrder.remainder {f : ℝ → ℝ} {a : ℕ → ℝ} {M : ℕ}
    (h : HasInverseExpansionAtOrder f a M) :
    IsInverseOrder (fun eps => f eps - inversePolynomial a M eps) (M + 1) := h

/-- Every polynomial supplies all fixed orders, including orders above its degree. -/
theorem polynomial_hasInverseExpansion (p : ℝ[X]) :
    HasInverseExpansion (fun eps => p.eval eps⁻¹) p.coeff := by
  intro M
  refine ⟨∑ k ∈ range (p.natDegree + 1), |p.coeff (M + 1 + k)|, 1, fun eps heps => ?_⟩
  have hep : 0 < eps := by linarith
  have hi0 : 0 ≤ eps⁻¹ := (inv_pos.mpr hep).le
  have hi1 : eps⁻¹ ≤ 1 := (inv_le_one₀ hep).mpr heps
  have heq : p.eval eps⁻¹ - inversePolynomial p.coeff M eps =
      ∑ k ∈ range (p.natDegree + 1), p.coeff (M + 1 + k) * (eps⁻¹) ^ (M + 1 + k) := by
    rw [Polynomial.eval_eq_sum_range' (n := (M + 1) + (p.natDegree + 1)) (by omega),
      sum_range_add, inversePolynomial]
    ring
  rw [heq, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hi0 _), pow_add]
  have hk : (eps⁻¹) ^ k ≤ 1 := pow_le_one₀ hi0 hi1
  have h := mul_le_mul_of_nonneg_left hk
    (mul_nonneg (abs_nonneg (p.coeff (M + 1 + k))) (pow_nonneg hi0 (M + 1)))
  simpa only [mul_one, mul_assoc] using h

/-- The finite expansion polynomial as an actual polynomial in one variable. -/
def inverseExpansionPolynomial (a : ℕ → ℝ) (M : ℕ) : ℝ[X] :=
  ∑ j ∈ range (M + 1), Polynomial.C (a j) * Polynomial.X ^ j

theorem eval_inverseExpansionPolynomial (a : ℕ → ℝ) (M : ℕ) (eps : ℝ) :
    (inverseExpansionPolynomial a M).eval eps⁻¹ = inversePolynomial a M eps := by
  simp [inverseExpansionPolynomial, inversePolynomial, Polynomial.eval_finsetSum]

theorem HasInverseExpansion.add {f g : ℝ → ℝ} {a b : ℕ → ℝ}
    (hf : HasInverseExpansion f a) (hg : HasInverseExpansion g b) :
    HasInverseExpansion (fun eps => f eps + g eps) (fun n => a n + b n) := by
  intro M
  have h := (hf M).remainder.add (hg M).remainder
  have he (eps : ℝ) : f eps + g eps - inversePolynomial (fun n => a n + b n) M eps =
      (f eps - inversePolynomial a M eps) + (g eps - inversePolynomial b M eps) := by
    simp only [inversePolynomial, add_mul, sum_add_distrib]
    ring
  simpa only [HasInverseExpansionAtOrder, IsInverseOrder, he] using h

theorem HasInverseExpansion.const_mul {f : ℝ → ℝ} {a : ℕ → ℝ}
    (hf : HasInverseExpansion f a) (c : ℝ) :
    HasInverseExpansion (fun eps => c * f eps) (fun n => c * a n) := by
  intro M
  have h := (hf M).remainder.const_mul c
  have he (eps : ℝ) : c * f eps - inversePolynomial (fun n => c * a n) M eps =
      c * (f eps - inversePolynomial a M eps) := by
    simp only [inversePolynomial, mul_assoc, ← mul_sum]
    ring
  simpa only [HasInverseExpansionAtOrder, IsInverseOrder, he] using h

/-- Multiplication preserves existence of a single compatible all-orders sequence. -/
theorem HasInverseExpansion.mul_exists {f g : ℝ → ℝ} {a b : ℕ → ℝ}
    (hf : HasInverseExpansion f a) (hg : HasInverseExpansion g b) :
    ∃! c : ℕ → ℝ, HasInverseExpansion (fun eps => f eps * g eps) c := by
  apply existsUnique_inverseExpansion_of_finite_orders
  intro M
  let pa := inverseExpansionPolynomial a M
  let pb := inverseExpansionPolynomial b M
  have hpa := polynomial_hasInverseExpansion pa
  have hpb := polynomial_hasInverseExpansion pb
  obtain ⟨Bpa, -, hbpa⟩ := (hpa 0).bounded
  obtain ⟨Bg, -, hbg⟩ := (hg 0).bounded
  have h₁ := (hf M).remainder.mul_bounded ⟨Bg, hbg⟩
  have h₂ := (hg M).remainder.mul_bounded ⟨Bpa, hbpa⟩
  have herr : IsInverseOrder (fun eps => f eps * g eps - (pa * pb).eval eps⁻¹) (M + 1) := by
    have he (eps : ℝ) : f eps * g eps - (pa * pb).eval eps⁻¹ =
        (f eps - inversePolynomial a M eps) * g eps +
          (g eps - inversePolynomial b M eps) * pa.eval eps⁻¹ := by
      rw [Polynomial.eval_mul, eval_inverseExpansionPolynomial, eval_inverseExpansionPolynomial]
      ring
    simpa only [he] using h₁.add h₂
  exact ⟨(pa * pb).coeff, ((polynomial_hasInverseExpansion (pa * pb)) M).transfer herr⟩

/-- Existence of an all-orders sequence, used for finite arithmetic. -/
def AdmitsInverseExpansion (f : ℝ → ℝ) : Prop := ∃ a, HasInverseExpansion f a

theorem AdmitsInverseExpansion.const (c : ℝ) : AdmitsInverseExpansion (fun _ => c) := by
  exact ⟨(Polynomial.C c).coeff, by simpa only [Polynomial.eval_C] using
    (polynomial_hasInverseExpansion (Polynomial.C c))⟩

theorem AdmitsInverseExpansion.add {f g : ℝ → ℝ}
    (hf : AdmitsInverseExpansion f) (hg : AdmitsInverseExpansion g) :
    AdmitsInverseExpansion (fun eps => f eps + g eps) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨_, ha.add hb⟩

theorem AdmitsInverseExpansion.const_mul {f : ℝ → ℝ}
    (hf : AdmitsInverseExpansion f) (c : ℝ) :
    AdmitsInverseExpansion (fun eps => c * f eps) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨_, ha.const_mul c⟩

theorem AdmitsInverseExpansion.mul {f g : ℝ → ℝ}
    (hf : AdmitsInverseExpansion f) (hg : AdmitsInverseExpansion g) :
    AdmitsInverseExpansion (fun eps => f eps * g eps) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  obtain ⟨c, hc, -⟩ := ha.mul_exists hb
  exact ⟨c, hc⟩

theorem AdmitsInverseExpansion.pow {f : ℝ → ℝ} (hf : AdmitsInverseExpansion f) (k : ℕ) :
    AdmitsInverseExpansion (fun eps => f eps ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using AdmitsInverseExpansion.const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem AdmitsInverseExpansion.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, AdmitsInverseExpansion (f i)) :
    AdmitsInverseExpansion (fun eps => ∑ i ∈ s, f i eps) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using AdmitsInverseExpansion.const 0
  | @insert i s hi ih =>
    simpa only [sum_insert hi] using
      (hf i (mem_insert_self _ _)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

/-- A finite geometric identity controls the reciprocal remainder. -/
theorem inverse_geometric_remainder (x c : ℝ) (hx : x ≠ 0) (hc : c ≠ 0) (M : ℕ) :
    x⁻¹ - (∑ k ∈ range (M + 1), (1 - x / c) ^ k) / c =
      (1 - x / c) ^ (M + 1) * x⁻¹ := by
  have h := geom_sum_mul_neg (1 - x / c) (M + 1)
  have he : 1 - (1 - x / c) = x / c := by ring
  rw [he] at h
  calc
    _ = (1 - (∑ k ∈ range (M + 1), (1 - x / c) ^ k) * (x / c)) * x⁻¹ := by
      field_simp
    _ = (1 - x / c) ^ (M + 1) * x⁻¹ := by rw [h]; ring

/-- A nonzero leading coefficient permits division at every fixed order. -/
theorem HasInverseExpansion.inv_exists {f : ℝ → ℝ} {a : ℕ → ℝ}
    (hf : HasInverseExpansion f a) (ha : a 0 ≠ 0) :
    ∃! b : ℕ → ℝ, HasInverseExpansion (fun eps => (f eps)⁻¹) b := by
  let h : ℝ → ℝ := fun eps => 1 - f eps / a 0
  have hexp : AdmitsInverseExpansion h := by
    have ht := (AdmitsInverseExpansion.const 1).add
      (AdmitsInverseExpansion.const_mul ⟨a, hf⟩ (-(a 0)⁻¹))
    convert ht using 1
    funext eps
    dsimp [h]
    ring
  have horder : IsInverseOrder h 1 := by
    have he : IsInverseOrder (fun eps => f eps - a 0) 1 := by
      simpa only [inversePolynomial, Nat.zero_add, sum_range_one, pow_zero, mul_one] using (hf 0).remainder
    have heq : h = fun eps => -(a 0)⁻¹ * (f eps - a 0) := by
      funext eps
      dsimp [h]
      field_simp
      ring
    rw [heq]
    exact he.const_mul _
  have hlim := (hf 0).tendsto_zero_order
  have hnonzero : ∀ᶠ eps in atTop, f eps ≠ 0 :=
    hlim.eventually (eventually_ne_nhds ha)
  have hinv := hlim.inv₀ ha
  have hbounded : ∃ B : ℝ, ∀ᶠ eps in atTop, |(f eps)⁻¹| ≤ B := by
    refine ⟨|(a 0)⁻¹| + 1, ?_⟩
    exact (hinv.abs.eventually (gt_mem_nhds (by linarith : |(a 0)⁻¹| < |(a 0)⁻¹| + 1))).mono
      fun _ hb => hb.le
  apply existsUnique_inverseExpansion_of_finite_orders
  intro M
  have hg : AdmitsInverseExpansion
      (fun eps => (∑ k ∈ range (M + 1), h eps ^ k) / a 0) := by
    have hs := AdmitsInverseExpansion.sum (range (M + 1)) (fun k _ => hexp.pow k)
    simpa only [div_eq_mul_inv, mul_comm] using hs.const_mul (a 0)⁻¹
  obtain ⟨b, hb⟩ := hg
  have herr : IsInverseOrder
      (fun eps => (f eps)⁻¹ - (∑ k ∈ range (M + 1), h eps ^ k) / a 0) (M + 1) := by
    obtain ⟨K, e0, hpow⟩ := (horder.pow (M + 1)).mul_bounded hbounded
    apply IsInverseOrder.of_eventually_abs_le (K := K)
    filter_upwards [hnonzero, eventually_ge_atTop e0] with eps hne heps
    rw [inverse_geometric_remainder _ _ hne ha M]
    simpa only [Nat.one_mul, h] using hpow eps heps
  exact ⟨b, (hb M).transfer herr⟩

theorem HasInverseExpansion.div_exists {f g : ℝ → ℝ} {a b : ℕ → ℝ}
    (hf : HasInverseExpansion f a) (hg : HasInverseExpansion g b) (hb : b 0 ≠ 0) :
    ∃! c : ℕ → ℝ, HasInverseExpansion (fun eps => f eps / g eps) c := by
  obtain ⟨d, hd, -⟩ := hg.inv_exists hb
  simpa only [div_eq_mul_inv] using hf.mul_exists hd

end

end PGM
