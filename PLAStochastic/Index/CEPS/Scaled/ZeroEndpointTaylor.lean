import PLAStochastic.Index.CEPS.Scaled.ZeroEndpointJets

/-! # True zero-endpoint Taylor remainders with finite jet coefficients -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledZeroEndpoint_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (n : ℕ) (hn : n ≤ N + 2) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.zeroEndpointScaleRadius / 2)) :
    ‖cepsScaledZeroEndpoint dom ρW b -
      complexTaylorSum (cepsScaledSurrogateZeroEndpoint dom ρW N) n 0 b‖ ≤
      (((n.factorial : ℝ) * dom.zeroEndpointPolynomialBound N M /
          (dom.zeroEndpointScaleRadius / 4) ^ n) +
        8 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀) * |b| ^ n := by
  have hbn : |b| < dom.zeroEndpointScaleRadius / 2 := by
    simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs] using hb
  have hR : dom.zeroEndpointScaleRadius ≤ dom.μ₀ / 8 := min_le_right _ _
  have hR1 : dom.zeroEndpointScaleRadius ≤ 1 := min_le_left _ _
  have hbμ : |b| < dom.μ₀ / 4 := by linarith [dom.μ₀_pos]
  have hb1 : |b| ≤ 1 := by linarith
  have hM0 : 0 ≤ M := (cepsSobolev_nonneg m η fW).trans hM
  have hK : 0 ≤ 8 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀ := by
    unfold CepsCanonDomain.canonDriftCoeffBound
    have := dom.jetC_nonneg hD N
    have := dom.c₀_pos
    positivity
  have hA := cepsScaledSurrogateZeroEndpoint_approx dom hW hθ hD hf hη hM N hN hbμ
  have hT := cepsScaledSurrogateZeroEndpoint_taylor_le dom hW hθ hD hf hη hM N
    (by omega) n hb
  rw [norm_real, Real.norm_eq_abs] at hT
  have hpow : |b| ^ (N + 2) ≤ |b| ^ n := pow_le_pow_of_le_one (abs_nonneg b) hb1 hn
  calc
    _ ≤ ‖cepsScaledZeroEndpoint dom ρW b - cepsScaledSurrogateZeroEndpoint dom ρW N b‖ +
        ‖cepsScaledSurrogateZeroEndpoint dom ρW N b -
          complexTaylorSum (cepsScaledSurrogateZeroEndpoint dom ρW N) n 0 b‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (8 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀) * |b| ^ n +
        ((n.factorial : ℝ) * dom.zeroEndpointPolynomialBound N M /
          (dom.zeroEndpointScaleRadius / 4) ^ n) * |b| ^ n :=
      add_le_add (hA.trans (mul_le_mul_of_nonneg_left hpow hK)) hT
    _ = _ := by ring

theorem cepsZeroEndpointJetTaylor_congr {p p' : ℕ → ℝ} (N n : ℕ)
    (hp : ∀ i, i < cepsJetDim (N + 1) → p i = p' i) :
    complexTaylorSum (cepsZeroEndpointJetPolynomial p N) n =
      complexTaylorSum (cepsZeroEndpointJetPolynomial p' N) n := by
  rw [cepsZeroEndpointJetPolynomial_congr N hp]

include hθ hD in
/-- The neighbourhood is selected before the law, order and Sobolev budget. -/
theorem cepsScaledZeroEndpoint_jet_approx :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η ηW M : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      CepsSobolevClass m ηW fW → 2 * dom.c₀ ≤ ηW → cepsSobolev m ηW fW ≤ M →
      ∀ N : ℕ, N + 2 ≤ m → ∀ b : ℝ, |b| < dom.μ₀ / 4 →
        ‖cepsScaledZeroEndpoint dom ρW b - cepsZeroEndpointJetPolynomial (cepsJet f) N b‖ ≤
          (8 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀) * |b| ^ (N + 2) := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogateZeroEndpoint_eq_jetPolynomial dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η ηW M hW hfW hneg hη hf hclose hfWsob hηW hM N hN b hb
  rw [← he hW hfW hneg hη hf hclose N hN]
  exact cepsScaledSurrogateZeroEndpoint_approx dom hW hθ hD hfWsob hηW hM N hN hb

include hθ hD in
theorem cepsScaledZeroEndpoint_jet_taylor_le :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η ηW M : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      CepsSobolevClass m ηW fW → 2 * dom.c₀ ≤ ηW → cepsSobolev m ηW fW ≤ M →
      ∀ N : ℕ, N + 2 ≤ m → ∀ n : ℕ, n ≤ N + 2 → ∀ b : ℝ,
        (b : ℂ) ∈ ball (0 : ℂ) (dom.zeroEndpointScaleRadius / 2) →
        ‖cepsScaledZeroEndpoint dom ρW b -
          complexTaylorSum (cepsZeroEndpointJetPolynomial (cepsJet f) N) n 0 b‖ ≤
          (((n.factorial : ℝ) * dom.zeroEndpointPolynomialBound N M /
              (dom.zeroEndpointScaleRadius / 4) ^ n) +
            8 * dom.canonDriftCoeffBound (N + 1) M / dom.c₀) * |b| ^ n := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogateZeroEndpoint_eq_jetPolynomial dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η ηW M hW hfW hneg hη hf hclose hfWsob hηW hM N hN n hn b hb
  rw [← he hW hfW hneg hη hf hclose N hN]
  exact cepsScaledZeroEndpoint_taylor_le dom hW hθ hD hfWsob hηW hM N hN n hn hb

end PGM
