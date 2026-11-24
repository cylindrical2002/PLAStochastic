import PLAStochastic.Index.CEPS.Final.GluedPair

/-! # Constructing the gluing data from the outer and central kernel results

The outer strip budget of the Newton pair (package S) and the central exact-root kernel
(package M) are stated here as hypotheses in exactly their proved forms; the radii of
`CepsGlueData` are chosen from them around a real reference vector with positive variance.
-/

noncomputable section
open Complex Metric Set Filter Topology
namespace PGM

/-- The outer strip budget of the Newton subtracted pair, as proved in `Strip/`. -/
def CepsStripPairBudget (d N : ℕ) : Prop :=
  ∀ M vlo vhi F₀ : ℝ, 0 ≤ M → 0 < vlo → vlo ≤ vhi → 0 < F₀ →
    ∃ δ δb K c : ℝ, ∃ e : ℕ, 0 < δ ∧ 0 < δb ∧ 0 < c ∧
      ∀ q : Fin d → ℂ, ‖q‖ ≤ M → vlo ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re →
        ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ vhi →
        |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
          (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 →
        ∀ (lam : ℝ) (z b : ℂ), -δ ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ →
          ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δb →
          AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d v.1) N lam v.2.1 v.2.2) (q, z, b) ∧
          ‖cepsComplexKernelSubtractedPairJetModel (cepsComplexJetPad d q) N lam z b‖ ≤
            K * (1 + |lam| + Real.sqrt ‖z‖) ^ e * Real.exp (-c * (|lam| + Real.sqrt ‖z‖))

/-- The central exact-root kernel at a real reference vector, as proved in `Central/`. -/
def CepsCentralPairKernel (d N : ℕ) (p₀ : Fin d → ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : (Fin d → ℂ) × ℂ × ℂ × ℂ → ℂ,
    AnalyticAt ℂ H ((fun i => (p₀ i : ℂ)), 0, 0, 0) ∧
    ∀ (q : Fin d → ℂ) (lam : ℝ) (z : ℂ),
      (q, (lam : ℂ), z, (0 : ℂ)) ∈ ball ((fun i => (p₀ i : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ)) ρ →
      z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0 →
      ∀ n ≤ N, iteratedDeriv n (fun b => cepsComplexKernelPairJetModel (cepsComplexJetPad d q) N lam z b) 0 =
        iteratedDeriv n (fun b => H (q, (lam : ℂ), z, b)) 0

theorem cepsComplexJetPad_variance_sub_le {d : ℕ} (hcode : cepsJetCode (.inl 0) < d)
    (q c₀ : Fin d → ℂ) :
    ‖cepsComplexJetPad d q (cepsJetCode (.inl 0)) - cepsComplexJetPad d c₀ (cepsJetCode (.inl 0))‖ ≤
      ‖q - c₀‖ := by
  rw [cepsComplexJetPad_apply q hcode, cepsComplexJetPad_apply c₀ hcode]
  exact norm_le_pi_norm (q - c₀) _

theorem exists_cepsGlueData {d N : ℕ} (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩)
    (hS : CepsStripPairBudget d N) (hM : CepsCentralPairKernel d N p₀) :
    ∃ G : CepsGlueData d N, G.c₀ = (fun i => (p₀ i : ℂ)) ∧
      G.R ≤ p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16 ∧ 0 ≤ G.MH := by
  set c₀ : Fin d → ℂ := fun i => (p₀ i : ℂ) with hc₀
  set V₀ := p₀ ⟨cepsJetCode (.inl 0), hcode⟩ with hV₀
  set u₀ : (Fin d → ℂ) × ℂ × ℂ × ℂ := (c₀, 0, 0, 0) with hu₀
  obtain ⟨ρ, hρ, H, hHa, hHeq⟩ := hM
  obtain ⟨r₁, hr₁, hHan⟩ := hHa.exists_ball_analyticOnNhd
  set r := min r₁ ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrr₁ : r < r₁ := by have := min_le_left r₁ ρ; linarith
  have hrρ : r < ρ := by have := min_le_right r₁ ρ; linarith
  have hcont : ContinuousOn H (closedBall u₀ r) := fun u hu =>
    (hHan u (mem_ball.mpr ((mem_closedBall.mp hu).trans_lt hrr₁))).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall u₀ r).exists_bound_of_continuousOn hcont
  set MH := max C 0
  set R := min (r / 2) (V₀ / 16) with hR
  set zc := r / 4 with hzc
  set lc := min (min 1 (r / 2)) (Real.sqrt (V₀ * zc / 2)) with hlc
  set F₀ := min lc (Real.sqrt zc) with hF₀
  have hR0 : 0 < R := lt_min (by positivity) (by positivity)
  have hzc0 : 0 < zc := by positivity
  have hlc0 : 0 < lc := lt_min (lt_min one_pos (by positivity)) (Real.sqrt_pos.mpr (by positivity))
  have hF0 : 0 < F₀ := lt_min hlc0 (Real.sqrt_pos.mpr hzc0)
  obtain ⟨δ, δb, K, c, e, hδ, hδb, hc, hout⟩ :=
    hS (‖c₀‖ + R) (V₀ / 2) (2 * V₀) F₀ (by positivity) (by positivity) (by linarith) hF0
  have hVq : ∀ q ∈ ball c₀ R, ‖cepsComplexJetPad d q (cepsJetCode (.inl 0)) - (V₀ : ℂ)‖ < R := by
    intro q hq
    have h := cepsComplexJetPad_variance_sub_le hcode q c₀
    rw [cepsComplexJetPad_apply c₀ hcode] at h
    exact h.trans_lt (by simpa [dist_eq_norm] using hq)
  have hRV : R ≤ V₀ / 16 := min_le_right _ _
  have hVre : ∀ q ∈ ball c₀ R, 15 * V₀ / 16 ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re := by
    intro q hq
    have h := (hVq q hq)
    have h2 := Complex.abs_re_le_norm (cepsComplexJetPad d q (cepsJetCode (.inl 0)) - (V₀ : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    linarith [(abs_le.mp (h2.trans h.le)).1]
  have hVim : ∀ q ∈ ball c₀ R, |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤ R := by
    intro q hq
    have h2 := Complex.abs_im_le_norm (cepsComplexJetPad d q (cepsJetCode (.inl 0)) - (V₀ : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h2
    exact h2.trans (hVq q hq).le
  have hVnorm : ∀ q ∈ ball c₀ R, ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ 2 * V₀ := by
    intro q hq
    have h := norm_le_insert' (cepsComplexJetPad d q (cepsJetCode (.inl 0))) (V₀ : ℂ)
    have h3 := (hVq q hq).le
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV] at h
    linarith
  refine ⟨{
    c₀ := c₀, H := H, r := r, MH := MH, R := R, lc := lc, zc := zc, F₀ := F₀, δ := δ, δb := δb,
    K := K, c := c, e := e, hr := hr0, hR := hR0, hRr := min_le_left _ _, hlc := hlc0,
    hlc1 := (min_le_left _ _).trans (min_le_left _ _),
    hlcr := (min_le_left _ _).trans (min_le_right _ _), hzc := hzc0,
    hzcr := by rw [hzc]; linarith, hF₀ := hF0, hF₀lc := min_le_left _ _,
    hF₀zc := by
      have h := min_le_right lc (Real.sqrt zc)
      calc F₀ ^ 2 ≤ Real.sqrt zc ^ 2 := pow_le_pow_left₀ hF0.le h 2
        _ = zc := Real.sq_sqrt hzc0.le,
    hδ := hδ, hδb := hδb, hc := hc, hK := ?_, merge := ?_, outer := ?_,
    central_an := fun u hu => hHan u (ball_subset_ball hrr₁.le hu),
    central_bd := fun u hu => (hC u (ball_subset_closedBall hu)).trans (le_max_left _ _),
    central_eq := fun q lam z hmem => hHeq q lam z (ball_subset_ball hrρ.le hmem) }, rfl, hRV,
    le_max_right _ _⟩
  · -- `K ≥ 0` from the bound at an admissible point
    have hq₀ : c₀ ∈ ball c₀ R := mem_ball_self hR0
    obtain ⟨-, hb⟩ := hout c₀ (by linarith [norm_nonneg c₀, hR0])
      (by linarith [hVre c₀ hq₀]) (hVnorm c₀ hq₀)
      (by linarith [hVim c₀ hq₀, hVre c₀ hq₀, hRV]) F₀ 0 0 (by simp [hδ.le])
      (by simp [abs_of_pos hF0]) (by simp [hδb.le])
    have h0 := (norm_nonneg _).trans hb
    by_contra hK
    have : K * (1 + |F₀| + Real.sqrt ‖(0 : ℂ)‖) ^ e * Real.exp (-c * (|F₀| + Real.sqrt ‖(0 : ℂ)‖)) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (not_le.mp hK) (by positivity)) (Real.exp_pos _)
    linarith
  · intro q hq lam hl
    have hVn : 15 * V₀ / 16 ≤ ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ :=
      (hVre q hq).trans (Complex.re_le_norm _)
    have hl2 : lam ^ 2 < V₀ * zc / 2 := by
      have h1 : |lam| < Real.sqrt (V₀ * zc / 2) := hl.trans_le (min_le_right _ _)
      have h2 := pow_lt_pow_left₀ h1 (abs_nonneg lam) (two_ne_zero)
      rwa [sq_abs, Real.sq_sqrt (by positivity)] at h2
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_ofNat,
      div_lt_iff₀ (mul_pos two_pos (lt_of_lt_of_le (by positivity) hVn))]
    nlinarith [hV, hzc0]
  · intro q hq lam z b hz hF hb
    have hq' : ‖q‖ ≤ ‖c₀‖ + R := by
      linarith [norm_le_insert' q c₀, (mem_ball_iff_norm.mp hq).le]
    have h := hout q hq' (by linarith [hVre q hq]) (hVnorm q hq)
      (by linarith [hVim q hq, hVre q hq, hRV]) lam z b hz hF
      (by simpa only [cepsDriftFreqSize, add_assoc] using hb)
    simpa only [cepsDriftFreqSize, add_assoc] using h

end PGM
