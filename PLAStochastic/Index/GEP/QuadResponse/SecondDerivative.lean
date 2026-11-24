import PLAStochastic.Index.GEP.PointwiseSmall.Interpolation

/-!
# WP4 leaf `QuadResponse`: second derivatives from `DiscInterp`, and one-sided Taylor

* `quad_interp_shift`: `DiscInterp` applied to `z ↦ f(z + s)` bounds `f'(s)` for `s ∈ [0, R/16]`;
* `quad_deriv_cauchy`: the Cauchy estimate `‖f'‖ ≤ 4M/R` on the half disc;
* `quad_second_deriv`: applying `quad_interp_shift` to `f'` on the half disc bounds `f''` on
  `[0, R/32]` by `K δ₁ (1 + log(M₁/δ₁))²`, `δ₁ = K δ (1 + log(M/δ))²/(R/2)` the bound of `f'` on the
  segment and `M₁ = max (4M/R) δ₁` its bound on the half disc;
* `quad_taylor`: `‖f'(0)‖ ≤ ‖f(u) - f(0)‖/u + u sup_{[0,u]} ‖f''‖` (PD §7).
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter Topology Metric

/-- **Interpolation at interior points** of the segment. -/
theorem quad_interp_shift {KI : ℝ}
    (hKI : ∀ (f : ℂ → ℂ) (R M δ : ℝ), 0 < R → 0 < δ → δ ≤ M →
      DifferentiableOn ℂ f (ball 0 R) → (∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) →
      (∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖f t‖ ≤ δ) →
        ‖deriv f 0‖ ≤ KI * δ * (1 + Real.log (M / δ)) ^ 2 / R)
    {f : ℂ → ℂ} {R M δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδM : δ ≤ M)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hb : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M)
    (hs : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖f t‖ ≤ δ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ R / 16) :
    ‖deriv f s‖ ≤ KI * δ * (1 + Real.log (M / δ)) ^ 2 / (R / 2) := by
  set g : ℂ → ℂ := fun z => f (z + s) with hg
  have hsub : ∀ z ∈ ball (0 : ℂ) (R / 2), z + (s : ℂ) ∈ ball (0 : ℂ) R := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖z + (s : ℂ)‖ ≤ ‖z‖ + ‖(s : ℂ)‖ := norm_add_le _ _
      _ < R / 2 + R / 2 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
          linarith
      _ = R := by ring
  have hgd : DifferentiableOn ℂ g (ball 0 (R / 2)) := by
    intro z hz
    have h1 : DifferentiableAt ℂ f (z + s) :=
      hf.differentiableAt (isOpen_ball.mem_nhds (hsub z hz))
    exact (h1.comp z (differentiableAt_id.add_const (s : ℂ))).differentiableWithinAt
  have hgb : ∀ z ∈ ball (0 : ℂ) (R / 2), ‖g z‖ ≤ M := fun z hz => hb _ (hsub z hz)
  have hgs : ∀ t : ℝ, 0 ≤ t → t ≤ R / 2 / 8 → ‖g t‖ ≤ δ := by
    intro t ht0 ht1
    have e : g t = f ((t + s : ℝ) : ℂ) := by simp only [hg, Complex.ofReal_add]
    rw [e]
    exact hs (t + s) (by linarith) (by linarith)
  have h := hKI g (R / 2) M δ (by positivity) hδ hδM hgd hgb hgs
  have hdg : deriv g 0 = deriv f s := by
    simp only [hg]
    rw [deriv_comp_add_const, zero_add]
  rwa [hdg] at h

/-- **The Cauchy estimate** for `f'` on the half disc. -/
theorem quad_deriv_cauchy {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hb : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) :
    ∀ z ∈ ball (0 : ℂ) (R / 2), ‖deriv f z‖ ≤ M / (R / 4) := by
  intro z hz
  have hsub : closedBall z (R / 4) ⊆ ball 0 R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖w‖ = ‖w - z + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ < R := by linarith
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
    (hf.diffContOnCl_ball hsub) fun w hw => hb w (hsub (sphere_subset_closedBall hw))

/-- **The second derivative on `[0, R/32]`** from two applications of `DiscInterp`. -/
theorem quad_second_deriv (hI : DiscInterp) :
    ∃ KI : ℝ, 0 < KI ∧ ∀ (f : ℂ → ℂ) (R M δ : ℝ), 0 < R → 0 < δ → δ ≤ M →
      DifferentiableOn ℂ f (ball 0 R) → (∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ M) →
      (∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖f t‖ ≤ δ) →
      ∀ s : ℝ, 0 ≤ s → s ≤ R / 32 →
        ‖deriv (deriv f) s‖ ≤ KI * (KI * δ * (1 + Real.log (M / δ)) ^ 2 / (R / 2)) *
          (1 + Real.log (max (M / (R / 4)) (KI * δ * (1 + Real.log (M / δ)) ^ 2 / (R / 2)) /
            (KI * δ * (1 + Real.log (M / δ)) ^ 2 / (R / 2)))) ^ 2 / (R / 4) := by
  obtain ⟨KI, hKI, hI⟩ := hI
  refine ⟨KI, hKI, fun f R M δ hR hδ hδM hf hb hs s hs0 hs1 => ?_⟩
  have hlog : 0 ≤ Real.log (M / δ) := Real.log_nonneg ((one_le_div hδ).2 hδM)
  have hδ₁0 : 0 < KI * δ * (1 + Real.log (M / δ)) ^ 2 / (R / 2) := by positivity
  have hf' : DifferentiableOn ℂ (deriv f) (ball 0 (R / 2)) :=
    ((hf.analyticOnNhd isOpen_ball).deriv.differentiableOn).mono (ball_subset_ball (by linarith))
  have hb' : ∀ z ∈ ball (0 : ℂ) (R / 2), ‖deriv f z‖ ≤
      max (M / (R / 4)) (KI * δ * (1 + Real.log (M / δ)) ^ 2 / (R / 2)) := fun z hz =>
    (quad_deriv_cauchy hR hf hb z hz).trans (le_max_left _ _)
  have hs' : ∀ t : ℝ, 0 ≤ t → t ≤ R / 2 / 8 →
      ‖deriv f t‖ ≤ KI * δ * (1 + Real.log (M / δ)) ^ 2 / (R / 2) := fun t ht0 ht1 =>
    quad_interp_shift hI hR hδ hδM hf hb hs ht0 (by linarith)
  have h := quad_interp_shift hI (by positivity : 0 < R / 2) hδ₁0 (le_max_right _ _) hf' hb' hs'
    hs0 (by linarith)
  rwa [show R / 2 / 2 = R / 4 by ring] at h

/-- **One-sided Taylor**: `‖f'(0)‖ ≤ ‖f(u) - f(0)‖/u + C u` if `‖f''‖ ≤ C` on `[0, u]`. -/
theorem quad_taylor {H : ℂ → ℂ} {R u C : ℝ} (hu : 0 < u) (huR : u < R)
    (hH : DifferentiableOn ℂ H (ball 0 R))
    (hC : ∀ s : ℝ, 0 ≤ s → s ≤ u → ‖deriv (deriv H) s‖ ≤ C) :
    ‖deriv H 0‖ ≤ ‖H u - H 0‖ / u + C * u := by
  have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ u → (t : ℂ) ∈ ball (0 : ℂ) R := by
    intro t ht0 ht1
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith
  have hH' : DifferentiableOn ℂ (deriv H) (ball 0 R) :=
    (hH.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 le_rfl hu.le)
  -- the derivative `g(t) = H'(t)` on `[0, u]`
  have hg : ∀ t ∈ Icc (0 : ℝ) u, HasDerivWithinAt (fun t : ℝ => deriv H t)
      (deriv (deriv H) t) (Icc 0 u) t := fun t ht =>
    ((hH'.differentiableAt (isOpen_ball.mem_nhds (hmem t ht.1 ht.2))).hasDerivAt.comp_ofReal
      ).hasDerivWithinAt
  have hgb := norm_image_sub_le_of_norm_deriv_le_segment' hg (fun t ht => hC t ht.1 ht.2.le)
  -- `k(t) = H(t) - H(0) - t H'(0)`
  have hk : ∀ t ∈ Icc (0 : ℝ) u, HasDerivWithinAt
      (fun t : ℝ => H t - H 0 - (t : ℂ) * deriv H 0) (deriv H t - deriv H 0) (Icc 0 u) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => H t) (deriv H t) t :=
      (hH.differentiableAt (isOpen_ball.mem_nhds (hmem t ht.1 ht.2))).hasDerivAt.comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * deriv H 0) (deriv H 0) t := by
      have := ((hasDerivAt_id t).ofReal_comp).mul_const (deriv H 0)
      simpa using this
    exact ((h1.sub_const (H 0)).sub h2).hasDerivWithinAt
  have hkb := norm_image_sub_le_of_norm_deriv_le_segment' hk (C := C * u) (fun t ht => by
    have h := hgb t (Ico_subset_Icc_self ht)
    simp only [Complex.ofReal_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left ht.2.le hC0))
  have hku := hkb u ⟨hu.le, le_rfl⟩
  simp only [Complex.ofReal_zero, zero_mul, sub_zero, sub_self] at hku
  -- conclude
  have hu' : ‖(u : ℂ) * deriv H 0‖ = u * ‖deriv H 0‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have h3 : ‖(u : ℂ) * deriv H 0‖ ≤ ‖H u - H 0‖ + C * u * u := by
    calc ‖(u : ℂ) * deriv H 0‖ = ‖(H u - H 0) - (H u - H 0 - (u : ℂ) * deriv H 0)‖ := by
          congr 1; ring
      _ ≤ ‖H u - H 0‖ + ‖H u - H 0 - (u : ℂ) * deriv H 0‖ := norm_sub_le _ _
      _ ≤ ‖H u - H 0‖ + C * u * u := by gcongr
  rw [hu'] at h3
  calc ‖deriv H 0‖ = u * ‖deriv H 0‖ / u := (mul_div_cancel_left₀ _ hu.ne').symm
    _ ≤ (‖H u - H 0‖ + C * u * u) / u := by gcongr
    _ = ‖H u - H 0‖ / u + C * u := by
        rw [add_div, mul_div_assoc, div_self hu.ne', mul_one]

end

end PGM
