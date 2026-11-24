import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc

/-! # Derivative bounds from a complex disc and rightward function values -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem norm_deriv_le_of_disc_and_right_values {F : ℂ → ℂ} {z : ℂ} {R M A₀ A₁ s : ℝ}
    (hR : 0 < R) (hd : DifferentiableOn ℂ F (ball z R))
    (hM : ∀ ζ ∈ ball z R, ‖F ζ‖ ≤ M) (hs : 0 < s) (hsR : s < R / 2)
    (h₀ : ‖F z‖ ≤ A₀) (h₁ : ‖F (z + (s : ℂ))‖ ≤ A₁) :
    ‖deriv F z‖ ≤ (A₀ + A₁) / s + (32 * M / R ^ 2) * s := by
  have hmem : z + (s : ℂ) ∈ ball z (R / 2) := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
      abs_of_pos hs] using hsR
  have ht := norm_sub_complexTaylorSum_le_of_ball 2 hR hd hM hmem
  have he : complexTaylorSum F 2 z (z + (s : ℂ)) = F z + (s : ℂ) * deriv F z := by
    simp [complexTaylorSum, Finset.sum_range_succ, iteratedDeriv_one]
  rw [he, show F (z + (s : ℂ)) - (F z + (s : ℂ) * deriv F z) =
      F (z + (s : ℂ)) - F z - (s : ℂ) * deriv F z by ring] at ht
  simp only [Nat.factorial_two, Nat.cast_ofNat, add_sub_cancel_left, norm_real,
    Real.norm_eq_abs, abs_of_pos hs] at ht
  have ht' : ‖F (z + (s : ℂ)) - F z - (s : ℂ) * deriv F z‖ ≤ (32 * M / R ^ 2) * s ^ 2 :=
    ht.trans_eq (by field_simp; ring)
  have heq : (s : ℂ) * deriv F z = (F (z + (s : ℂ)) - F z) -
      (F (z + (s : ℂ)) - F z - (s : ℂ) * deriv F z) := by ring
  have hn : s * ‖deriv F z‖ ≤ A₀ + A₁ + (32 * M / R ^ 2) * s ^ 2 := by
    have hnorm : ‖(s : ℂ) * deriv F z‖ = s * ‖deriv F z‖ := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs]
    rw [← hnorm, heq]
    exact (norm_sub_le _ _).trans ((add_le_add ((norm_sub_le _ _).trans (add_le_add h₁ h₀))
      ht').trans_eq (by ring))
  apply le_of_mul_le_mul_left (a := s) _ hs
  exact hn.trans_eq (by field_simp)

theorem norm_deriv_le_decay_of_disc_and_right_values {F : ℂ → ℂ} {z : ℂ} {R M A t : ℝ}
    (hR : 0 < R) (ht : 0 ≤ t) (hd : DifferentiableOn ℂ F (ball z R))
    (hM : ∀ ζ ∈ ball z R, ‖F ζ‖ ≤ M)
    (hA : ∀ s ∈ Icc (0 : ℝ) (R / 4), ‖F (z + (s : ℂ))‖ ≤ A * Real.exp (-t)) :
    ‖deriv F z‖ ≤ (8 * (A + M) / R) * Real.exp (-t / 2) := by
  let e := Real.exp (-t / 2)
  let s := R / 4 * e
  have he : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs : 0 < s := mul_pos (by positivity) he
  have hsle : s ≤ R / 4 := by dsimp [s]; nlinarith
  have hsR : s < R / 2 := by linarith
  have h₀ : ‖F z‖ ≤ A * Real.exp (-t) := by
    simpa only [ofReal_zero, add_zero] using hA 0 ⟨le_rfl, by positivity⟩
  have h₁ := hA s ⟨hs.le, hsle⟩
  have hexp : Real.exp (-t) = e ^ 2 := by
    dsimp [e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (norm_deriv_le_of_disc_and_right_values hR hd hM hs hsR h₀ h₁).trans_eq
  rw [hexp]
  dsimp only [s, e]
  field_simp
  ring

end PGM
