import PLAStochastic.Index.CEPS.Final.KernelPipelineSetup

/-! # Box Taylor representation of the mean coefficients `C_k` -/

noncomputable section
open Complex Metric Set Filter Topology MeasureTheory Finset
namespace PGM

theorem abs_re_sub_sum_le {d N : ℕ} (w : ℂ) (T : (Fin d → ℕ) → ℂ) (y : Fin d → ℝ) :
    |w.re - ∑ α ∈ cepsTaylorBox d N, (T α).re * cepsMonomial y α| ≤
      ‖w - ∑ α ∈ cepsTaylorBox d N, T α * (cepsMonomial y α : ℂ)‖ := by
  have e : w.re - ∑ α ∈ cepsTaylorBox d N, (T α).re * cepsMonomial y α =
      (w - ∑ α ∈ cepsTaylorBox d N, T α * (cepsMonomial y α : ℂ)).re := by
    simp [Complex.sub_re, Complex.re_sum, Complex.mul_re]
  rw [e]
  exact Complex.abs_re_le_norm _

theorem cepsKernelCs_rep (h : CepsKernelPackages) (k : ℕ) :
    ∃ d : ℕ, ∃ T : (Fin d → ℕ) → ℝ, ∀ N : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧
      ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - cepsJetLaw cepsLambda i| ≤ ρ) →
        |cepsKernelCs k p - ∑ α ∈ cepsTaylorBox d N,
            T α * cepsMonomial (fun i : Fin d => p i - cepsJetLaw cepsLambda i) α| ≤
          K * (∑ i : Fin d, |p i - cepsJetLaw cepsLambda i|) ^ (N + 1) := by
  set d := cepsJetDim (4 * (k + 1)) with hd
  have hcode := cepsJetCode_variance_lt k
  have hV := cepsRefJets_variance_pos k
  obtain ⟨G, hc₀, hR, hMH⟩ := exists_cepsGlueData (cepsRefJets d) hcode hV (h.pair d (k + 1))
    (h.central d (k + 1) _ (cepsRefJets_pad_variance_pos k))
  obtain ⟨δf, δbf, hδf, hδbf, hf⟩ := (h.bridge d (k + 1)).at (cepsRefJets d) hcode hV G.hF₀
  set δ := min G.δ δf / 2 with hδ
  have hδ0 : 0 < δ := by have := G.hδ; positivity
  have hδG : δ < G.δ := by have := min_le_left G.δ δf; linarith [G.hδ]
  have hδf' : δ < δf := by have := min_le_right G.δ δf; linarith
  have hball : ∀ q, q ∈ ball (fun i : Fin d => (cepsJetLaw cepsLambda i : ℂ)) G.R →
      q ∈ ball G.c₀ G.R := fun q hq => by rw [hc₀]; exact hq
  have hzre : ∀ z : ℂ, |z.re| < δ → -δ < z.re := fun z hz => (abs_lt.mp hz).1
  let H : (Fin d → ℂ) → ℝ → ℂ → ℂ := fun q lam z =>
    cepsGluedPairCoeff d (k + 1) k G.H G.lc G.zc q lam z
  have hP : CepsAnalyticPipeline volume d (cepsJetLaw cepsLambda) G.R δ 1 G.c (G.e + k)
      (G.gluedEnvelope k) (fun _ _ => (0 : ℂ)) H :=
    { R_pos := G.hR
      δ_pos := hδ0
      K_pos := one_pos
      c_pos := G.hc
      g_integrable := G.gluedEnvelope_integrable k
      E_analytic := fun _ _ _ _ => analyticAt_const
      E_bound := fun _ _ z _ => by simp only [norm_zero]; positivity
      H_analytic := Eventually.of_forall fun lam q hq z hz =>
        G.glued_analyticAt (by omega) (hball q hq) lam (by linarith [hzre z hz])
      H_bound := Eventually.of_forall fun lam q hq z hz =>
        G.glued_norm_le (hball q hq) lam (by linarith [hzre z hz]) hMH
      H_measurable := fun q hq z hz =>
        G.glued_aestronglyMeasurable (cepsRefJets d) hcode hV hc₀ hR hδbf hf (hball q hq)
          (by linarith [hzre z hz]) (by linarith [hzre z hz]) k }
  let Φ : (ℕ → ℝ) → ℝ → ℂ := fun p y => -∫ lam, H (fun i => (p i : ℂ)) lam (Complex.I * y)
  set ρ₀ := min (G.R / 2) (cepsJetLaw cepsLambda (cepsJetCode (.inl 0)) / 2)
  have hρ₀ : 0 < ρ₀ := lt_min (half_pos G.hR) (half_pos cepsJetLaw_cepsLambda_variance_pos)
  obtain ⟨T₁, hT₁⟩ := hP.scalar_re_of_eq hρ₀ (Φ := Φ) (fun p _ y => by simp [Φ]) 0 (-1)
    (S := fun p => (∫ lam, H (fun i => (p i : ℂ)) lam 0).re) (fun p _ => by simp [Φ])
  obtain ⟨TZ, hTZ⟩ := cepsZeroEndpointCoeff_jetScal k (d := d)
    (cepsJetDim_monotone (by omega))
  refine ⟨d, fun α => (TZ α).re + T₁ α, fun N => ?_⟩
  obtain ⟨ρ₁, K₁, hρ₁, H₁⟩ := hT₁ N
  obtain ⟨ρZ, KZ, hρZ, HZ⟩ := hTZ N
  refine ⟨min ρ₀ (min ρ₁ ρZ), KZ + K₁, lt_min hρ₀ (lt_min hρ₁ hρZ), fun p hp => ?_⟩
  have hp₀ : ∀ i : Fin d, |p i - cepsJetLaw cepsLambda i| ≤ ρ₀ := fun i => (hp i).trans (min_le_left _ _)
  have hp₁ : ∀ i : Fin d, |p i - cepsJetLaw cepsLambda i| ≤ ρ₁ :=
    fun i => (hp i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hpZ : ∀ i : Fin d, |p i - cepsJetLaw cepsLambda i| ≤ ρZ :=
    fun i => (hp i).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hq, hpV⟩ := cepsRef_box_facts hd G hc₀ hR hp₀
  have hCs := G.cepsKernelCs_eq_glued le_rfl (cepsRefJets d) hcode hV hc₀ hR hMH hδf hδbf hf hq hpV
  rw [hCs, Complex.add_re]
  have e1 := abs_re_sub_sum_le (N := N) (cepsScaleCoeff k (cepsZeroEndpointJetPolynomial p k)) TZ
    (fun i : Fin d => p i - cepsJetLaw cepsLambda i)
  have e2 := H₁ p hp₁
  have hsum : ∑ α ∈ cepsTaylorBox d N, ((TZ α).re + T₁ α) *
      cepsMonomial (fun i : Fin d => p i - cepsJetLaw cepsLambda i) α =
      ∑ α ∈ cepsTaylorBox d N, (TZ α).re * cepsMonomial (fun i : Fin d => p i - cepsJetLaw cepsLambda i) α +
      ∑ α ∈ cepsTaylorBox d N, T₁ α * cepsMonomial (fun i : Fin d => p i - cepsJetLaw cepsLambda i) α := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun α _ => by ring
  rw [hsum]
  calc _ = |((cepsScaleCoeff k (cepsZeroEndpointJetPolynomial p k)).re -
          ∑ α ∈ cepsTaylorBox d N, (TZ α).re * cepsMonomial (fun i : Fin d => p i - cepsJetLaw cepsLambda i) α) +
        ((∫ lam, H (cepsJetEmbed d p) lam 0).re -
          ∑ α ∈ cepsTaylorBox d N, T₁ α * cepsMonomial (fun i : Fin d => p i - cepsJetLaw cepsLambda i) α)| := by
        congr 1; simp only [H]; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ KZ * (∑ i : Fin d, |p i - cepsJetLaw cepsLambda i|) ^ (N + 1) +
        K₁ * (∑ i : Fin d, |p i - cepsJetLaw cepsLambda i|) ^ (N + 1) :=
        add_le_add (e1.trans (HZ p hpZ)) e2
    _ = _ := by ring

end PGM
