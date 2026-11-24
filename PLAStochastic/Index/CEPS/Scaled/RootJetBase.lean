import PLAStochastic.Index.CEPS.Scaled.RootImplicit

/-! # Variance determination and nondegeneracy of the leading scaled root -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v D' θ' v' : ℝ} {ρW ρW' : Measure ℝ} {fW fW' f f' : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsStepVar_eq_of_cumulantJet_eq (hW' : IsStepLaw ρW' fW' D' θ' v') (hθ' : 0 < θ') (hD' : 0 < D')
    (hfW : ∀ y, fW y = f (1 - y)) (hfW' : ∀ y, fW' y = f' (1 - y))
    (hp : cepsJet f (cepsJetCode (.inl 0)) = cepsJet f' (cepsJetCode (.inl 0))) :
    cepsStepVar ρW = cepsStepVar ρW' := by
  have h1 := cepsJet_cumulant_eq hW hθ hD hfW 0
  have h2 := cepsJet_cumulant_eq hW' hθ' hD' hfW' 0
  simp only [zero_add, iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_deriv_cepsCgf_zero hW hθ hD] at h1
  simp only [zero_add, iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_deriv_cepsCgf_zero hW' hθ' hD'] at h2
  exact_mod_cast h1.trans ((congrArg (fun a : ℝ => (a : ℂ)) hp).trans h2.symm)

include hW hθ hD in
theorem cepsCgfUnit_difference_le_of_cumulantJets (hW' : IsStepLaw ρW' fW' D' θ' v')
    (hθ' : 0 < θ') (hD' : 0 < D')
    (hfW : ∀ y, fW y = f (1 - y)) (hfW' : ∀ y, fW' y = f' (1 - y)) (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → cepsJet f i = cepsJet f' i) :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 < R ∧ ∀ s ∈ ball (0 : ℂ) R,
      ‖cepsCgfUnit ρW' s - cepsCgfUnit ρW s‖ ≤ K * ‖s‖ ^ (N + 1) := by
  let K1 : ℝ := ((N + 3).factorial : ℝ) * (3 / 4) / (cepsCgfRadius D θ / 4) ^ (N + 3)
  let K2 : ℝ := ((N + 3).factorial : ℝ) * (3 / 4) / (cepsCgfRadius D' θ' / 4) ^ (N + 3)
  have hR := cepsCgfRadius_pos hD hθ
  have hR' := cepsCgfRadius_pos hD' hθ'
  refine ⟨K1 + K2, min (cepsCgfRadius D θ / 2) (cepsCgfRadius D' θ' / 2),
    by dsimp [K1, K2]; positivity, lt_min (half_pos hR) (half_pos hR'), ?_⟩
  intro s hs
  have h1 := cepsCgfUnit_jet_taylor_le hW hθ hD hfW N (ball_subset_ball (min_le_left _ _) hs)
  have h2 := cepsCgfUnit_jet_taylor_le hW' hθ' hD' hfW' N (ball_subset_ball (min_le_right _ _) hs)
  rw [← cepsCgfJetPolynomial_congr N hp] at h2
  calc
    _ ≤ ‖cepsCgfUnit ρW' s - cepsCgfJetPolynomial (cepsJet f) N s‖ +
        ‖cepsCgfUnit ρW s - cepsCgfJetPolynomial (cepsJet f) N s‖ := by
      have ht := norm_sub_le_norm_sub_add_norm_sub (cepsCgfUnit ρW' s)
        (cepsCgfJetPolynomial (cepsJet f) N s) (cepsCgfUnit ρW s)
      simpa only [norm_sub_rev] using ht
    _ ≤ K2 * ‖s‖ ^ (N + 1) + K1 * ‖s‖ ^ (N + 1) := add_le_add h2 h1
    _ = _ := by ring

include hW hθ hD in
theorem cepsScaledSignedRoot_zero_origin (sign : ℂ) :
    cepsScaledSignedRoot D θ ρW 0 0 sign = fun _ => 0 := by
  funext b
  have hm : cepsMorseRoot D θ ρW (0 : ℂ) (0 : ℂ) = 0 := by
    rw [cepsMorseRoot_zero hW hθ hD (by simpa using cepsChartMu_pos hD hθ),
      cepsMorseCenter_at_zero hW hθ hD]
  simp [cepsScaledSignedRoot, cepsScaledRootCoordinate, cepsScaledMorseRadicand, hm]
  by_cases hb : b = 0
  · rw [hb, dslope_same, deriv_const]
  · rw [dslope_of_ne _ hb, slope_def_field]
    simp

include dom hW hθ hD in
theorem cepsScaledSignedRoot_zero_gap_ne (lam : ℝ) {z sign : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) (hsign : sign ^ 2 = 1) :
    (lam : ℂ) + 2 * cepsScaledSignedRoot D θ ρW lam z sign 0 * cepsCgfUnit ρW 0 ≠ 0 := by
  have hv := cepsStepVar_pos hW hθ hD
  have hv0 : (cepsStepVar ρW : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have hs0 : sign ≠ 0 := by intro he; simp [he] at hsign
  have hsqrt : Complex.sqrt (2 / (cepsStepVar ρW : ℂ)) ≠ 0 := by
    intro he
    have ht := sqrt_sq_eq (2 / (cepsStepVar ρW : ℂ))
    rw [he, zero_pow (by norm_num : 2 ≠ 0)] at ht
    exact (div_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hv0) ht.symm
  have hrad := slitPlane_ne_zero
    (cepsScaledMorseRadicand_mem_slitPlane dom hW hθ hD lam hz hne
      (mem_ball_self (radicandScaleRadius_budget dom hW hθ hD lam).1))
  rw [cepsScaledMorseRadicand_zero hW hθ hD] at hrad
  have hcoord : Complex.sqrt (z + (lam : ℂ) ^ 2 / (2 * (cepsStepVar ρW : ℂ))) ≠ 0 := by
    intro he
    have ht := sqrt_sq_eq (z + (lam : ℂ) ^ 2 / (2 * (cepsStepVar ρW : ℂ)))
    rw [he, zero_pow (by norm_num : 2 ≠ 0)] at ht
    exact hrad ht.symm
  rw [cepsScaledSignedRoot_zero dom hW hθ hD lam hz sign, cepsCgfUnit_zero hW hθ hD]
  have hid : (lam : ℂ) + 2 *
      (-(lam : ℂ) / (cepsStepVar ρW : ℂ) + sign * Complex.sqrt (2 / (cepsStepVar ρW : ℂ)) *
        Complex.sqrt (z + (lam : ℂ) ^ 2 / (2 * (cepsStepVar ρW : ℂ)))) *
        ((cepsStepVar ρW : ℂ) / 2) =
      (cepsStepVar ρW : ℂ) * sign * Complex.sqrt (2 / (cepsStepVar ρW : ℂ)) *
        Complex.sqrt (z + (lam : ℂ) ^ 2 / (2 * (cepsStepVar ρW : ℂ))) := by
    field_simp
    ring
  rw [hid]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hv0 hs0) hsqrt) hcoord

end PGM
