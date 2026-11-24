import PLAStochastic.Index.CEPS.Scaled.RootJetModel

/-! # The finite Newton model recovers the genuine scaled-root Taylor jets -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries Asymptotics
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsCumulantRootBase_cepsJet (hfW : ∀ y, fW y = f (1 - y))
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (sign : ℂ) :
    cepsCumulantRootBase (cepsJet f) lam z sign = cepsScaledSignedRoot D θ ρW lam z sign 0 := by
  have hj := cepsJet_cumulant_eq hW hθ hD hfW 0
  simp only [zero_add, iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_deriv_cepsCgf_zero hW hθ hD] at hj
  rw [cepsScaledSignedRoot_zero dom hW hθ hD lam hz sign]
  simp only [cepsCumulantRootBase, ← hj]

include dom hW hθ hD in
theorem cepsCumulantRootGap_cepsJet (hfW : ∀ y, fW y = f (1 - y))
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (sign : ℂ) :
    cepsCumulantRootGap (cepsJet f) lam z sign = (lam : ℂ) +
      2 * cepsScaledSignedRoot D θ ρW lam z sign 0 * cepsCgfUnit ρW 0 := by
  have hj := cepsJet_cumulant_eq hW hθ hD hfW 0
  simp only [zero_add, iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_deriv_cepsCgf_zero hW hθ hD] at hj
  rw [cepsCumulantRootGap, cepsCumulantRootBase_cepsJet dom hW hθ hD hfW lam hz sign,
    ← hj, cepsCgfUnit_zero hW hθ hD]
  ring

include hW hθ hD in
theorem cepsCgfJetPolynomial_cepsJet_zero (hfW : ∀ y, fW y = f (1 - y)) (N : ℕ) :
    cepsCgfJetPolynomial (cepsJet f) N 0 = cepsCgfUnit ρW 0 := by
  have ht := cepsCgfUnit_jet_taylor_le hW hθ hD hfW N
    (mem_ball_self (half_pos (cepsCgfRadius_pos hD hθ)))
  have he : cepsCgfUnit ρW 0 - cepsCgfJetPolynomial (cepsJet f) N 0 = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [norm_zero, zero_pow (by omega : N + 1 ≠ 0), mul_zero] using ht
  exact (sub_eq_zero.mp he).symm

include dom hW hθ hD in
theorem cepsCumulantRootModel_cepsJet_zero (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) (k : ℕ) :
    cepsCumulantRootModel (cepsJet f) N lam z sign k 0 =
      cepsScaledSignedRoot D θ ρW lam z sign 0 := by
  have he0 := mem_of_mem_nhds
    (cepsScaledSignedRoot_unit_equation_eventually dom hW hθ hD lam hz hsign)
  simp only [Set.mem_ofPred_eq, zero_mul, mul_one, add_zero] at he0
  induction k with
  | zero => exact cepsCumulantRootBase_cepsJet dom hW hθ hD hfW lam hz sign
  | succ k ih =>
    simp only [cepsCumulantRootModel, quadraticNewtonStep, ih, zero_mul,
      cepsCgfJetPolynomial_cepsJet_zero hW hθ hD hfW N, add_zero, mul_one, he0,
      sub_self, zero_div, sub_zero]

include hW hθ hD in
theorem cepsCgfJetPolynomial_cepsJet_isBigO (hfW : ∀ y, fW y = f (1 - y)) (N : ℕ) :
    (fun s => cepsCgfJetPolynomial (cepsJet f) N s - cepsCgfUnit ρW s) =O[𝓝 0]
      (fun s : ℂ => s ^ (N + 1)) := by
  refine isBigO_iff.mpr ⟨((N + 3).factorial : ℝ) * (3 / 4) /
    (cepsCgfRadius D θ / 4) ^ (N + 3), ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) (half_pos (cepsCgfRadius_pos hD hθ))] with s hs
  rw [norm_pow, norm_sub_rev]
  exact cepsCgfUnit_jet_taylor_le hW hθ hD hfW N hs

include dom hW hθ hD in
theorem cepsCumulantRootModel_actual_isBigO (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1)
    (hne : lam ≠ 0 ∨ z ≠ 0) (k : ℕ) :
    (fun b => cepsScaledSignedRoot D θ ρW lam z sign b -
      cepsCumulantRootModel (cepsJet f) N lam z sign k b) =O[𝓝 0]
        (fun b : ℂ => b ^ (min (k + 1) (N + 1))) := by
  let ξ := cepsScaledSignedRoot D θ ρW lam z sign
  have ha := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
  have hH : AnalyticAt ℂ (cepsCgfUnit ρW) 0 :=
    (cepsCgfUnit_differentiableOn hW hθ hD).analyticOnNhd isOpen_ball 0
      (mem_ball_self (cepsCgfRadius_pos hD hθ))
  have hgap := cepsScaledSignedRoot_zero_gap_ne dom hW hθ hD lam hz hne hsign
  have hunit := cepsCgfJetPolynomial_cepsJet_isBigO hW hθ hD hfW N
  have he := cepsScaledSignedRoot_unit_equation_eventually dom hW hθ hD lam hz hsign
  induction k with
  | zero =>
    have ht := ha.differentiableAt.hasDerivAt.isBigO_sub
    simpa only [cepsCumulantRootModel,
      cepsCumulantRootBase_cepsJet dom hW hθ hD hfW lam hz sign, sub_zero,
      show min (0 + 1) (N + 1) = 1 by omega, pow_one] using! ht
  | succ k ih =>
    have hg : AnalyticAt ℂ (cepsCumulantRootModel (cepsJet f) N lam z sign k) 0 :=
      (cepsCumulantRootModel_differentiable (cepsJet f) N lam z sign k).analyticAt 0
    have hzero := (cepsCumulantRootModel_cepsJet_zero dom hW hθ hD hfW N lam hz hsign k).symm
    have hslope := cepsNormal_analyticAt_moving_dslope_of_analyticAt hH
      ((analyticAt_id (𝕜 := ℂ)).mul hg) ((analyticAt_id (𝕜 := ℂ)).mul ha)
      (by simp) (by simp)
    have ht := quadraticNewtonStep_improves_order ha hg hH hslope hzero hgap he
      N (min (k + 1) (N + 1)) hunit ih
    rw [← cepsCumulantRootGap_cepsJet dom hW hθ hD hfW lam hz sign] at ht
    simpa only [cepsCumulantRootModel,
      show min (min (k + 1) (N + 1) + 1) (N + 1) = min (k + 1 + 1) (N + 1) by omega] using ht

include dom hW hθ hD in
theorem cepsScaledSignedRoot_taylorJets_eq_model (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1)
    (hne : lam ≠ 0 ∨ z ≠ 0) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (cepsScaledSignedRoot D θ ρW lam z sign) 0) =
      coeff j (complexTaylorSeries (cepsCumulantRootModel (cepsJet f) N lam z sign N) 0) := by
  have ha := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
  have hg := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z sign N).analyticAt 0
  have ht := cepsCumulantRootModel_actual_isBigO dom hW hθ hD hfW N lam hz hsign hne N
  simp only [min_self] at ht
  exact complexTaylorSeries_coeff_eq_of_isBigO ha hg N ht

include dom hW hθ hD in
theorem cepsScaledSignedRoot_taylorJets_eq_finite_model (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (cepsScaledSignedRoot D θ ρW lam z sign) 0) =
      coeff j (complexTaylorSeries (cepsCumulantRootModel (cepsJet f) N lam z sign N) 0) := by
  by_cases hne : lam ≠ 0 ∨ z ≠ 0
  · exact cepsScaledSignedRoot_taylorJets_eq_model dom hW hθ hD hfW N lam hz hsign hne
  · have hlam : lam = 0 := not_ne_iff.mp (fun h => hne (Or.inl h))
    have hz0 : z = 0 := not_ne_iff.mp (fun h => hne (Or.inr h))
    subst lam
    subst z
    rw [cepsScaledSignedRoot_zero_origin hW hθ hD, cepsCumulantRootModel_origin]
    exact fun _ _ => rfl

end PGM
