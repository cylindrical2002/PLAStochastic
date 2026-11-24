import PLAStochastic.Index.CEPS.Final.EndpointInputs

/-! # Endpoint scale coefficients on the reference polydisc and strip -/

noncomputable section
open Complex Metric Set Filter Topology
namespace PGM

/-- On a polydisc of radius `≤ V₀/16` around a real vector of variance `V₀ > 0`, the variance
coordinate satisfies the cone conditions of the complex budgets. -/
theorem cepsBall_variance_conditions {d : ℕ} (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩) {R : ℝ}
    (hR : R ≤ p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16) {q : Fin d → ℂ}
    (hq : q ∈ ball (fun i => (p₀ i : ℂ)) R) :
    ‖q‖ ≤ ‖(fun i => (p₀ i : ℂ))‖ + R ∧
    p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 2 ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re ∧
    ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ 2 * p₀ ⟨cepsJetCode (.inl 0), hcode⟩ ∧
    |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
      (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 := by
  set c₀ : Fin d → ℂ := fun i => (p₀ i : ℂ)
  set V₀ := p₀ ⟨cepsJetCode (.inl 0), hcode⟩
  have hVq : ‖cepsComplexJetPad d q (cepsJetCode (.inl 0)) - (V₀ : ℂ)‖ < R := by
    have h := cepsComplexJetPad_variance_sub_le hcode q c₀
    rw [cepsComplexJetPad_apply c₀ hcode] at h
    exact h.trans_lt (by simpa [dist_eq_norm] using hq)
  have hre := Complex.abs_re_le_norm (cepsComplexJetPad d q (cepsJetCode (.inl 0)) - (V₀ : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  have him := Complex.abs_im_le_norm (cepsComplexJetPad d q (cepsJetCode (.inl 0)) - (V₀ : ℂ))
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  have hn := norm_le_insert' (cepsComplexJetPad d q (cepsJetCode (.inl 0))) (V₀ : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV] at hn
  have h1 := (abs_le.mp (hre.trans hVq.le)).1
  refine ⟨by linarith [norm_le_insert' q c₀, (mem_ball_iff_norm.mp hq).le], by linarith,
    by linarith, by linarith⟩

/-- Endpoint scale coefficients: joint analyticity and the stretched frequency bound. -/
theorem cepsEndpoint_coeff {d j : ℕ} (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩) (hE : CepsStripEndpointBudget d j) :
    ∃ δ K c : ℝ, ∃ e : ℕ, 0 < δ ∧ 0 < c ∧ 0 ≤ K ∧ ∀ R : ℝ,
      R ≤ p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16 → ∀ q ∈ ball (fun i => (p₀ i : ℂ)) R, ∀ z : ℂ,
        -δ ≤ z.re →
        AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => cepsKernelEndpointCoeffC d j v.1 v.2) (q, z) ∧
        ‖cepsKernelEndpointCoeffC d j q z‖ ≤ K * (1 + ‖z‖) ^ e * Real.exp (-c * Real.sqrt ‖z‖) := by
  set V₀ := p₀ ⟨cepsJetCode (.inl 0), hcode⟩
  set c₀ : Fin d → ℂ := fun i => (p₀ i : ℂ)
  obtain ⟨δ, δb, K, c, e, hδ, hδb, hc, hB⟩ :=
    hE (‖c₀‖ + V₀ / 16) (V₀ / 2) (2 * V₀) (by positivity) (by positivity) (by linarith)
  refine ⟨δ, |K| * (4 / δb) ^ j * 2 ^ e, c, e + j, hδ, hc, by positivity, fun R hR q hq z hz => ?_⟩
  obtain ⟨hq1, hq2, hq3, hq4⟩ := cepsBall_variance_conditions p₀ hcode hV hR hq
  have hq1' : ‖q‖ ≤ ‖c₀‖ + V₀ / 16 := hq1.trans (by linarith)
  have h := cepsScaleCoeff_of_sqrt_family (F := fun q z b =>
      cepsComplexKernelMarkedEndpointJetModel (cepsComplexJetPad d q) j z b)
    (q := q) (z := z) hδb (fun b hb => hB q hq1' hq2 hq3 hq4 z b hz hb) j
  refine ⟨h.1, h.2.trans ?_⟩
  have hs := one_add_sqrt_le ‖z‖ (norm_nonneg z)
  have h1 : 0 ≤ 1 + Real.sqrt ‖z‖ := by positivity
  have h2 : (2 * (1 + Real.sqrt ‖z‖) / δb) ^ j ≤ (4 / δb) ^ j * (1 + ‖z‖) ^ j := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδb]
    linarith
  have h3 : (1 + Real.sqrt ‖z‖) ^ e ≤ 2 ^ e * (1 + ‖z‖) ^ e := by
    rw [← mul_pow]; exact pow_le_pow_left₀ h1 hs e
  have hE0 : 0 ≤ Real.exp (-c * Real.sqrt ‖z‖) := (Real.exp_pos _).le
  calc K * (1 + Real.sqrt ‖z‖) ^ e * Real.exp (-c * Real.sqrt ‖z‖) *
        (2 * (1 + Real.sqrt ‖z‖) / δb) ^ j
      ≤ |K| * (2 ^ e * (1 + ‖z‖) ^ e) * Real.exp (-c * Real.sqrt ‖z‖) *
        ((4 / δb) ^ j * (1 + ‖z‖) ^ j) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self K) h3
          (by positivity) (abs_nonneg K)) hE0) h2 (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; ring

end PGM
