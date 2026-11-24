import PLAStochastic.Index.CEPS.Jets.Consistency
import PLAStochastic.ForMathlib.Analysis.Complex.Hadamard
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc

/-! # The removable quadratic cumulant unit and its finite cumulant-jet polynomial

The scaled root equation uses this genuine holomorphic unit. Its finite
polynomial reads only cumulants through order `N + 2`.
-/

noncomputable section
open Complex Set Metric MeasureTheory Finset
open PGM.WienerHopf
namespace PGM

def cepsCgfUnit (ρW : Measure ℝ) (s : ℂ) : ℂ := hadamard2 (cepsCgf ρW) 0 s

def cepsCgfJetPolynomial (p : ℕ → ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), ((j + 2).factorial : ℂ)⁻¹ * s ^ j *
    (p (cepsJetCode (.inl j)) : ℂ)

theorem cepsCgfJetPolynomial_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) :
    cepsCgfJetPolynomial p N = cepsCgfJetPolynomial p' N := by
  funext s
  apply sum_congr rfl
  intro j hj
  rw [hp (cepsJetCode (.inl j)) (cepsJetCode_lt_cepsJetDim
    (by have := mem_range.mp hj; simp only [cepsJetWeight]; omega))]

theorem cepsCgfJetPolynomial_differentiable (p : ℕ → ℝ) (N : ℕ) :
    Differentiable ℂ (cepsCgfJetPolynomial p N) := by
  unfold cepsCgfJetPolynomial
  fun_prop

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCgfUnit_zero : cepsCgfUnit ρW 0 = (cepsStepVar ρW : ℂ) / 2 := by
  rw [cepsCgfUnit, hadamard2_zero, deriv_deriv_cepsCgf_zero hW hθ hD]

include hW hθ hD in
theorem cepsCgfUnit_differentiableOn :
    DifferentiableOn ℂ (cepsCgfUnit ρW) (ball 0 (cepsCgfRadius D θ)) := by
  have hd := differentiableOn_hadamard2 (differentiableOn_cepsCgf hW hθ hD)
  exact hd.comp ((differentiableOn_const (0 : ℂ)).prodMk differentiableOn_id)
    (fun s hs => by
      change ‖(0 : ℂ)‖ + ‖s‖ < cepsCgfRadius D θ
      simpa only [norm_zero, zero_add] using mem_ball_zero_iff.mp hs)

include hW hθ hD in
theorem cepsCgf_eq_mul_unit {s : ℂ} (hs : s ∈ ball (0 : ℂ) (cepsCgfRadius D θ)) :
    cepsCgf ρW s = s ^ 2 * cepsCgfUnit ρW s := by
  have hh := hadamard2_spec isOpen_ball (differentiableOn_cepsCgf hW hθ hD)
    (b := 0) (u := s) (fun t ht => by
      rw [zero_add, mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg s) ht.2).trans_lt (mem_ball_zero_iff.mp hs))
  simpa only [cepsCgfUnit, zero_add, cepsCgf_zero hW,
    deriv_cepsCgf_zero hW hθ hD, zero_mul] using hh

include hW hθ hD in
theorem cepsCgfUnit_eq_div {s : ℂ} (hs : s ∈ ball (0 : ℂ) (cepsCgfRadius D θ))
    (hs0 : s ≠ 0) : cepsCgfUnit ρW s = cepsCgf ρW s / s ^ 2 := by
  rw [cepsCgf_eq_mul_unit hW hθ hD hs]
  field_simp

include hW hθ hD in
theorem complexTaylorSum_cepsCgf_eq_jetPolynomial (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (s : ℂ) :
    complexTaylorSum (cepsCgf ρW) (N + 3) 0 s = s ^ 2 * cepsCgfJetPolynomial (cepsJet f) N s := by
  unfold complexTaylorSum cepsCgfJetPolynomial
  simp only [sub_zero]
  rw [show N + 3 = (N + 2) + 1 by omega, sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul,
    iteratedDeriv_zero, cepsCgf_zero hW, add_zero]
  rw [show N + 2 = (N + 1) + 1 by omega, sum_range_succ']
  simp only [zero_add, iteratedDeriv_one, deriv_cepsCgf_zero hW hθ hD, mul_zero, add_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [show j + 1 + 1 = j + 2 by omega, cepsJet_cumulant_eq hW hθ hD hfW]
  rw [pow_add]
  ring

include hW hθ hD in
theorem cepsCgfUnit_jet_taylor_le (hfW : ∀ y, fW y = f (1 - y)) (N : ℕ)
    {s : ℂ} (hs : s ∈ ball (0 : ℂ) (cepsCgfRadius D θ / 2)) :
    ‖cepsCgfUnit ρW s - cepsCgfJetPolynomial (cepsJet f) N s‖ ≤
      (((N + 3).factorial : ℝ) * (3 / 4) / (cepsCgfRadius D θ / 4) ^ (N + 3)) *
        ‖s‖ ^ (N + 1) := by
  have hR := cepsCgfRadius_pos hD hθ
  by_cases hs0 : s = 0
  · subst s
    rw [cepsCgfUnit_zero hW hθ hD]
    have hj := cepsJet_cumulant_eq hW hθ hD hfW 0
    simp only [zero_add, iteratedDeriv_succ, iteratedDeriv_zero,
      deriv_deriv_cepsCgf_zero hW hθ hD] at hj
    simp [cepsCgfJetPolynomial, sum_range_succ', ← hj, Nat.factorial]
    ring
  · have hsR := ball_subset_ball (half_le_self hR.le) hs
    have ht := norm_sub_complexTaylorSum_le_of_ball (N + 3) hR
      (differentiableOn_cepsCgf hW hθ hD)
      (fun w hw => norm_cepsCgf_le hW hθ hD (mem_ball_zero_iff.mp hw).le) hs
    rw [complexTaylorSum_cepsCgf_eq_jetPolynomial hW hθ hD hfW] at ht
    simp only [sub_zero] at ht
    rw [cepsCgfUnit_eq_div hW hθ hD hsR hs0,
      show cepsCgf ρW s / s ^ 2 - cepsCgfJetPolynomial (cepsJet f) N s =
        (cepsCgf ρW s - s ^ 2 * cepsCgfJetPolynomial (cepsJet f) N s) / s ^ 2 by
          field_simp, norm_div, norm_pow]
    apply (div_le_div_of_nonneg_right ht (sq_nonneg ‖s‖)).trans_eq
    rw [show N + 3 = (N + 1) + 2 by omega, pow_add]
    have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs0
    field_simp
    ring

end PGM
