import PLAStochastic.Index.CEPS.Final.KernelPipelineSetup

/-! # `Ĝ_j` as a kernel of the analytic pipeline -/

noncomputable section
open Complex Metric Set Filter Topology MeasureTheory Finset
namespace PGM

theorem cepsKernelGk_pipeline (h : CepsKernelPackages) (j : ℕ) :
    ∃ (R δ K c : ℝ) (e : ℕ) (g : ℝ → ℝ)
      (E : (Fin (cepsJetDim (4 * (j + 1))) → ℂ) → ℂ → ℂ)
      (H : (Fin (cepsJetDim (4 * (j + 1))) → ℂ) → ℝ → ℂ → ℂ),
      CepsAnalyticPipeline volume (cepsJetDim (4 * (j + 1))) (cepsJetLaw cepsLambda) R δ K c e g E H ∧
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ p : ℕ → ℝ,
        (∀ i : Fin (cepsJetDim (4 * (j + 1))), |p i - cepsJetLaw cepsLambda i| ≤ ρ₀) → ∀ y : ℝ,
          cepsKernelGk j p y = E (fun i => (p i : ℂ)) (Complex.I * y) -
            ∫ lam, H (fun i => (p i : ℂ)) lam (Complex.I * y) := by
  set d := cepsJetDim (4 * (j + 1)) with hd
  have hcode := cepsJetCode_variance_lt j
  have hV := cepsRefJets_variance_pos j
  obtain ⟨G, hc₀, hR, hMH⟩ := exists_cepsGlueData (cepsRefJets d) hcode hV (h.pair d (j + 1))
    (h.central d (j + 1) _ (cepsRefJets_pad_variance_pos j))
  obtain ⟨δf, δbf, hδf, hδbf, hf⟩ := (h.bridge d (j + 1)).at (cepsRefJets d) hcode hV G.hF₀
  obtain ⟨δE, KE, cE, eE, hδE, hcE, hKE, hEc⟩ := cepsEndpoint_coeff (cepsRefJets d) hcode hV
    (h.endpoint d j)
  obtain ⟨KD, δD, eD, hδD, hKD, hHb⟩ := G.integrand_norm_le (h.discount d j) hMH
  set δ := min (min G.δ δE) δf / 2 with hδ
  have hδ0 : 0 < δ := by have := G.hδ; positivity
  have hδG : δ < G.δ := by
    have := min_le_left (min G.δ δE) δf; have := min_le_left G.δ δE; linarith [G.hδ]
  have hδE' : δ < δE := by
    have := min_le_left (min G.δ δE) δf; have := min_le_right G.δ δE; linarith
  have hδf' : δ < δf := by have := min_le_right (min G.δ δE) δf; linarith
  have hball : ∀ q, q ∈ ball (fun i : Fin d => (cepsJetLaw cepsLambda i : ℂ)) G.R →
      q ∈ ball G.c₀ G.R := fun q hq => by rw [hc₀]; exact hq
  have hzre : ∀ z : ℂ, |z.re| < δ → -δ < z.re := fun z hz => (abs_lt.mp hz).1
  refine ⟨G.R, δ, max KE 1, min cE G.c, max eE (eD + G.e + j), G.integrandEnvelope j KD δD,
    cepsKernelEndpointCoeffC d j, cepsKernelPairIntegrand G j,
    { R_pos := G.hR
      δ_pos := hδ0
      K_pos := lt_of_lt_of_le one_pos (le_max_right _ _)
      c_pos := lt_min hcE G.hc
      g_integrable := G.integrandEnvelope_integrable j KD δD
      E_analytic := fun q hq z hz =>
        (hEc G.R hR q (by rw [← hc₀]; exact hball q hq) z (by linarith [hzre z hz])).1
      E_bound := fun q hq z hz =>
        ((hEc G.R hR q (by rw [← hc₀]; exact hball q hq) z (by linarith [hzre z hz])).2).trans
          (cepsPipelineWeight_mono hKE (le_max_left _ _) (le_max_left _ _) (min_le_left _ _) z)
      H_analytic := Eventually.of_forall fun lam q hq z hz =>
        G.integrand_analyticAt le_rfl (h.discount d j) (hball q hq) lam
          (by linarith [hzre z hz])
      H_bound := Eventually.of_forall fun lam q hq z hz => by
        refine (hHb q (hball q hq) lam z (by linarith [hzre z hz])).trans ?_
        have hg := G.integrandEnvelope_nonneg j hKD hδD hMH lam
        have hw := cepsPipelineWeight_mono (K₁ := 1) (K₂ := 1) zero_le_one le_rfl
          (le_max_right eE (eD + G.e + j)) (min_le_right cE G.c) z
        simp only [one_mul] at hw
        exact mul_le_mul_of_nonneg_left hw hg
      H_measurable := fun q hq z hz => by
        unfold cepsKernelPairIntegrand
        refine Finset.aestronglyMeasurable_fun_sum _ fun x _ => ?_
        exact (G.glued_aestronglyMeasurable (cepsRefJets d) hcode hV hc₀ hR hδbf hf (hball q hq)
          (by linarith [hzre z hz]) (by linarith [hzre z hz]) x.2).const_mul _ },
    min (G.R / 2) (cepsJetLaw cepsLambda (cepsJetCode (.inl 0)) / 2),
    lt_min (half_pos G.hR) (half_pos cepsJetLaw_cepsLambda_variance_pos), fun p hp y => ?_⟩
  obtain ⟨hq, hpV⟩ := cepsRef_box_facts hd G hc₀ hR hp
  exact G.cepsKernelGk_eq_integrand le_rfl (cepsRefJets d) hcode hV hc₀ hR hMH hδf hδbf hf hq hpV y

end PGM
