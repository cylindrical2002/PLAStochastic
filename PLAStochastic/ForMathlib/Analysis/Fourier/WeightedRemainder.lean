import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseExpansion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Exponentially weighted remainders from a uniform error and an envelope

The geometric-mean estimate is the pointwise-envelope version of the tail split
in (O21). It loses half the algebraic order and half the exponential rate. Both
budgets are chosen before the parameter tends to infinity.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace PGM

/-- The symmetric exponential envelope is integrable. -/
theorem integrable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|)) := by
  have hp := integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0
  have hn := integrableOn_exp_mul_Iic ha 0
  have hp' : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Ioi 0) :=
    hp.congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have hn' : IntegrableOn (fun x : ℝ => Real.exp (-a * |x|)) (Iic 0) :=
    hn.congr_fun (fun x hx => by simp [abs_of_nonpos (show x ≤ 0 from hx)]) measurableSet_Iic
  have hu := hn'.union hp'
  simpa only [Iic_union_Ioi, integrableOn_univ] using hu

/-- A uniform error and a pointwise envelope give an interpolated envelope. -/
theorem abs_le_geometric_envelope {y K B t θ : ℝ} {p : ℕ}
    (hK : 0 ≤ K) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hsmall : |y| ≤ K * t ^ (2 * p))
    (henv : |y| ≤ B * Real.exp (-θ)) :
    |y| ≤ (K + B) * t ^ p * Real.exp (-θ / 2) := by
  have hprod : |y| ^ 2 ≤ K * B * t ^ (2 * p) * Real.exp (-θ) := by
    calc
      |y| ^ 2 = |y| * |y| := pow_two _
      _ ≤ (K * t ^ (2 * p)) * (B * Real.exp (-θ)) :=
        mul_le_mul hsmall henv (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hsq : ((K + B) * t ^ p * Real.exp (-θ / 2)) ^ 2 =
      (K + B) ^ 2 * t ^ (2 * p) * Real.exp (-θ) := by
    have he : Real.exp (-θ / 2) ^ 2 = Real.exp (-θ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, mul_pow, he, ← pow_mul, Nat.mul_comm p 2]
  have hKB : K * B ≤ (K + B) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKB (pow_nonneg ht (2 * p))) (Real.exp_pos (-θ)).le
  have hnonneg : 0 ≤ (K + B) * t ^ p * Real.exp (-θ / 2) := by positivity
  rw [← hsq] at hh
  exact (sq_le_sq₀ (abs_nonneg y) hnonneg).mp (hprod.trans hh)

/-- A pointwise exponential bound pays every smaller exponential `L¹` weight. -/
theorem weighted_integrable_of_envelope {f : ℝ → ℝ} {B θ η : ℝ}
    (hf : AEStronglyMeasurable f) (_hB : 0 ≤ B) (hη : η < θ)
    (hb : ∀ x, |f x| ≤ B * Real.exp (-θ * |x|)) :
    Integrable (fun x => Real.exp (η * |x|) * f x) ∧
      (∫ x, Real.exp (η * |x|) * |f x|) ≤
        B * ∫ x : ℝ, Real.exp (-(θ - η) * |x|) := by
  have hI := (integrable_exp_neg_abs (show 0 < θ - η by linarith)).const_mul B
  have hbound (x : ℝ) :
      |Real.exp (η * |x|) * f x| ≤ B * Real.exp (-(θ - η) * |x|) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (η * |x|) * (B * Real.exp (-θ * |x|)) :=
        mul_le_mul_of_nonneg_left (hb x) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hi : Integrable (fun x => Real.exp (η * |x|) * f x) :=
    hI.mono' ((by fun_prop : Continuous fun x : ℝ => Real.exp (η * |x|)).aestronglyMeasurable.mul hf)
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ x, |Real.exp (η * |x|) * f x| := by
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ ∫ x, B * Real.exp (-(θ - η) * |x|) := integral_mono hi.abs hI hbound
    _ = _ := integral_const_mul _ _

/-- With a fixed envelope, twice the uniform accuracy gives the desired weighted accuracy. -/
theorem weighted_inverseOrder_of_uniform {R : ℝ → ℝ → ℝ} {θ η : ℝ} {p : ℕ}
    (hη : η < θ / 2)
    (hsmall : ∃ K eps₀ : ℝ, ∀ eps ≥ eps₀, ∀ x, |R eps x| ≤ K * (eps⁻¹) ^ (2 * p))
    (henv : ∃ B eps₀ : ℝ, ∀ eps ≥ eps₀,
      AEStronglyMeasurable (R eps) ∧ ∀ x, |R eps x| ≤ B * Real.exp (-θ * |x|)) :
    IsInverseOrder (fun eps => ∫ x, Real.exp (η * |x|) * |R eps x|) p := by
  obtain ⟨K, eK, hK⟩ := hsmall
  obtain ⟨B, eB, hB⟩ := henv
  let J := ∫ x : ℝ, Real.exp (-(θ / 2 - η) * |x|)
  have hJ : 0 ≤ J := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨(|K| + |B|) * J, max 1 (max eK eB), fun eps heps => ?_⟩
  have he1 : 1 ≤ eps := (le_max_left _ _).trans heps
  have heK : eK ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans heps)
  have heB : eB ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans heps)
  have ht : 0 ≤ eps⁻¹ := by positivity
  have hm := (hB eps heB).1
  have hb (x : ℝ) : |R eps x| ≤
      ((|K| + |B|) * (eps⁻¹) ^ p) * Real.exp (-(θ / 2) * |x|) := by
    have hs := (hK eps heK x).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg ht _))
    have he := ((hB eps heB).2 x).trans
      (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le)
    have he' : |R eps x| ≤ |B| * Real.exp (-(θ * |x|)) := by simpa only [neg_mul] using he
    rw [show -(θ / 2) * |x| = -(θ * |x|) / 2 by ring]
    exact abs_le_geometric_envelope (abs_nonneg K) (abs_nonneg B) ht hs he'
  have hi := weighted_integrable_of_envelope hm (by positivity) hη hb
  rw [abs_of_nonneg (integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
  convert hi.2 using 1
  dsimp [J]
  ring

end PGM
