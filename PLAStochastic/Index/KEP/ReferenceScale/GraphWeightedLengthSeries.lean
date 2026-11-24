import PLAStochastic.Index.KEP.ReferenceScale.LongSecondGraphKernel
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Quantitative summation of the killed exterior lengths

The positive output exponent consumes only half the killed rate. The cost is
explicit in the inverse rate and in the band width, so it remains polynomial
when the killed rate is proportional to the inverse squared tolerance.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

theorem kep_summable_polynomial_exp {r : ℝ} (hr : 0 < r) (p : ℕ) :
    Summable (fun k : ℕ => (k + 1 : ℝ) ^ p * Real.exp (-r * k)) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul p hr)
  convert h.mul_left (Real.exp r) using 1 <;> first
  | rfl
  | (funext k
     rw [Nat.cast_add, Nat.cast_one, mul_left_comm, ← Real.exp_add]
     congr 2
     ring)

theorem kep_total_length_product (w : ℝ) (hw : 0 ≤ w) (i r L : ℕ) :
    w + (i + r + L : ℕ) + 1 ≤ (w + 1) * (i + 1 : ℝ) * (r + 1 : ℝ) * (L + 1 : ℝ) := by
  have hi : (0 : ℝ) ≤ i := by positivity
  have hr : (0 : ℝ) ≤ r := by positivity
  have hL : (0 : ℝ) ≤ L := by positivity
  push_cast
  nlinarith [mul_nonneg hi hr, mul_nonneg hi hL, mul_nonneg hr hL,
    mul_nonneg (mul_nonneg hi hr) hL, mul_nonneg hw hi, mul_nonneg hw hr,
    mul_nonneg hw hL, mul_nonneg hw (mul_nonneg hi hr),
    mul_nonneg hw (mul_nonneg hi hL), mul_nonneg hw (mul_nonneg hr hL),
    mul_nonneg hw (mul_nonneg (mul_nonneg hi hr) hL)]

theorem kep_graph_length_series {w r eta : ℝ} (hw : 0 ≤ w) (hr : 0 < r)
    (heta : eta ≤ r / 2) (p : ℕ) :
    let F := fun k : ℕ => (w + (k : ℝ) + 1) ^ p *
      Real.exp (eta * ((k : ℝ) + w)) * Real.exp (-r * k)
    Summable F ∧ (∑' k : ℕ, F k) ≤
      Real.exp (eta * w) * (w + 1) ^ p *
        ((p.factorial : ℝ) * Real.exp 1 * (1 + 4 / r) ^ (p + 1)) := by
  dsimp only
  let G := fun k : ℕ => (k + 1 : ℝ) ^ p * Real.exp (-(r / 2) * k)
  let A := Real.exp (eta * w) * (w + 1) ^ p
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsG : Summable G := kep_summable_polynomial_exp (by linarith) p
  have hb (k : ℕ) : (w + (k : ℝ) + 1) ^ p * Real.exp (eta * ((k : ℝ) + w)) *
      Real.exp (-r * k) ≤ A * G k := by
    have hlen : w + (k : ℝ) + 1 ≤ (w + 1) * (k + 1 : ℝ) := by
      nlinarith [mul_nonneg hw (Nat.cast_nonneg k)]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ w + (k : ℝ) + 1) hlen p
    have he : Real.exp (eta * ((k : ℝ) + w)) * Real.exp (-r * k) ≤
        Real.exp (eta * w) * Real.exp (-(r / 2) * k) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right heta (Nat.cast_nonneg k)]
    calc
      _ ≤ ((w + 1) * (k + 1 : ℝ)) ^ p *
          (Real.exp (eta * w) * Real.exp (-(r / 2) * k)) := by
        rw [mul_assoc]
        exact mul_le_mul hp he (by positivity) (by positivity)
      _ = A * G k := by dsimp [A, G]; rw [mul_pow]; ring
  have hsA := hsG.mul_left A
  have hsF := hsA.of_nonneg_of_le (fun k => by positivity) hb
  refine ⟨hsF, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, A * G k := hsF.tsum_le_tsum hb hsA
    _ = A * ∑' k : ℕ, G k := tsum_mul_left
    _ ≤ A * ((p.factorial : ℝ) * Real.exp 1 * (1 + 2 / (r / 2)) ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left (Real.tsum_polynomial_mul_exp_neg_le (by linarith) p) hA
    _ = _ := by dsimp [A]; congr 2; congr 2; field_simp; ring

theorem kep_graph_triple_series {w r eta : ℝ} (hw : 0 ≤ w) (hr : eta < r)
    (p : ℕ) {H : ℕ → ℝ} (hH : ∀ L, 0 ≤ H L)
    (hsH : Summable (fun L : ℕ => (L + 1 : ℝ) ^ p * Real.exp (eta * L) * H L)) :
    let F := fun z : ℕ × ℕ × ℕ => (w + (z.1 + z.2.1 + z.2.2 : ℕ) + 1) ^ p *
      Real.exp (eta * ((z.1 + z.2.1 + z.2.2 : ℕ) + w)) * H z.2.2 *
      Real.exp (-r * (z.1 + z.2.1 : ℕ))
    Summable F ∧ (∑' z : ℕ × ℕ × ℕ, F z) ≤
      (Real.exp (eta * w) * (w + 1) ^ p) *
        ((p.factorial : ℝ) * Real.exp 1 * (1 + 2 / (r - eta)) ^ (p + 1)) ^ 2 *
        (∑' L : ℕ, (L + 1 : ℝ) ^ p * Real.exp (eta * L) * H L) := by
  dsimp only
  let E := fun i : ℕ => (i + 1 : ℝ) ^ p * Real.exp (-(r - eta) * i)
  let K := fun L : ℕ => (L + 1 : ℝ) ^ p * Real.exp (eta * L) * H L
  let A := Real.exp (eta * w) * (w + 1) ^ p
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE (i : ℕ) : 0 ≤ E i := by dsimp [E]; positivity
  have hK (L : ℕ) : 0 ≤ K L := by dsimp [K]; exact mul_nonneg (by positivity) (hH L)
  have hsE : Summable E := kep_summable_polynomial_exp (by linarith) p
  have hsEK := hsE.mul_of_nonneg hsH hE hK
  have hsEEK := hsE.mul_of_nonneg hsEK hE (fun z => mul_nonneg (hE z.1) (hK z.2))
  have hb (z : ℕ × ℕ × ℕ) :
      (w + (z.1 + z.2.1 + z.2.2 : ℕ) + 1) ^ p *
        Real.exp (eta * ((z.1 + z.2.1 + z.2.2 : ℕ) + w)) * H z.2.2 *
        Real.exp (-r * (z.1 + z.2.1 : ℕ)) ≤ A * (E z.1 * (E z.2.1 * K z.2.2)) := by
    have hlen := pow_le_pow_left₀ (by positivity :
      0 ≤ w + (z.1 + z.2.1 + z.2.2 : ℕ) + 1)
        (kep_total_length_product w hw z.1 z.2.1 z.2.2) p
    calc
      _ ≤ ((w + 1) * (z.1 + 1 : ℝ) * (z.2.1 + 1 : ℝ) * (z.2.2 + 1 : ℝ)) ^ p *
          Real.exp (eta * ((z.1 + z.2.1 + z.2.2 : ℕ) + w)) * H z.2.2 *
          Real.exp (-r * (z.1 + z.2.1 : ℕ)) := by
        gcongr
        exact hH z.2.2
      _ = _ := by
        dsimp [A, E, K]
        simp only [mul_pow, Nat.cast_add]
        rw [show eta * (((z.1 : ℝ) + z.2.1 + z.2.2) + w) =
          eta * w + (-(r - eta) * z.1 + (-(r - eta) * z.2.1 + eta * z.2.2)) +
            r * ((z.1 : ℝ) + z.2.1) by ring]
        simp only [Real.exp_add]
        have he : Real.exp (r * ((z.1 : ℝ) + z.2.1)) *
            Real.exp (-r * ((z.1 : ℝ) + z.2.1)) = 1 := by rw [← Real.exp_add]; ring_nf; simp
        linear_combination ((w + 1) ^ p * (z.1 + 1 : ℝ) ^ p * (z.2.1 + 1 : ℝ) ^ p *
          (z.2.2 + 1 : ℝ) ^ p * Real.exp (eta * w) *
          Real.exp (-(r - eta) * z.1) * Real.exp (-(r - eta) * z.2.1) *
          Real.exp (eta * z.2.2) * H z.2.2) * he
  have hsA := hsEEK.mul_left A
  have hsF := hsA.of_nonneg_of_le (fun z => by
    exact mul_nonneg (mul_nonneg (by positivity) (hH z.2.2)) (by positivity)) hb
  refine ⟨hsF, ?_⟩
  have hsumE : (∑' i : ℕ, E i) ≤
      (p.factorial : ℝ) * Real.exp 1 * (1 + 2 / (r - eta)) ^ (p + 1) :=
    Real.tsum_polynomial_mul_exp_neg_le (by linarith) p
  have hsumE0 : 0 ≤ ∑' i : ℕ, E i := tsum_nonneg hE
  have hsumK0 : 0 ≤ ∑' L : ℕ, K L := tsum_nonneg hK
  calc
    _ ≤ ∑' z : ℕ × ℕ × ℕ, A * (E z.1 * (E z.2.1 * K z.2.2)) := hsF.tsum_le_tsum hb hsA
    _ = A * ((∑' i : ℕ, E i) * ((∑' i : ℕ, E i) * ∑' L : ℕ, K L)) := by
      rw [tsum_mul_left, ← hsE.tsum_mul_tsum hsEK hsEEK, ← hsE.tsum_mul_tsum hsH hsEK]
    _ = A * (∑' i : ℕ, E i) ^ 2 * (∑' L : ℕ, K L) := by ring
    _ ≤ _ := by gcongr

end

end PGM
