import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.ThreePointConstraints

/-!
# An active three-point facet fixes the actual band path

Positive physical lengths make the fitting slope and local intercept unique
on either oriented active facet. Therefore feasibility of the complete prefix
is exactly survival of one specified residual path in the strip `[0, 2*eps]`.
No choice of a different fitting line remains in that path event.
-/

namespace PGM
noncomputable section
open Set

/-- Rigidity on the positively oriented active facet. Each term in the displayed
weighted error identity is nonnegative, forcing all three contacts. -/
theorem kernel_facet_fit_unique_pos {L M A B eps a b : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hfacet : fluxSignedWidth L M A B = eps) (hb : |b| ≤ eps)
    (hm : |L - (a * A + b)| ≤ eps) (he : |L + M - (a * (A + B) + b)| ≤ eps) :
    a = fluxSlope L M A B ∧ b = eps := by
  have hAB : 0 < A + B := add_pos hA hB
  have hlin : L * B - M * A = 2 * (A + B) * eps := by
    have h := (div_eq_iff (ne_of_gt (mul_pos (by norm_num) hAB))).mp hfacet
    nlinarith [h]
  have hzero : B * (eps - b) + (A + B) * (eps - (L - (a * A + b))) +
      A * (eps + (L + M - (a * (A + B) + b))) = 0 := by
    calc _ = 2 * (A + B) * eps - (L * B - M * A) := by ring
         _ = 0 := by rw [hlin]; ring
  have h₀ : 0 ≤ B * (eps - b) := mul_nonneg hB.le (by linarith [(abs_le.mp hb).2])
  have h₁ : 0 ≤ (A + B) * (eps - (L - (a * A + b))) :=
    mul_nonneg hAB.le (by linarith [(abs_le.mp hm).2])
  have h₂ : 0 ≤ A * (eps + (L + M - (a * (A + B) + b))) :=
    mul_nonneg hA.le (by linarith [(abs_le.mp he).1])
  have hz₀ : B * (eps - b) = 0 := by linarith
  have hz₂ : A * (eps + (L + M - (a * (A + B) + b))) = 0 := by linarith
  have hb' : b = eps := by
    have h := (mul_eq_zero.mp hz₀).resolve_left (ne_of_gt hB)
    linarith
  have he' := (mul_eq_zero.mp hz₂).resolve_left (ne_of_gt hA)
  refine ⟨?_, hb'⟩
  unfold fluxSlope
  apply (eq_div_iff (ne_of_gt hAB)).mpr
  linarith

/-- Both facet orientations give the same chord slope and the signed extremal
local intercept. The physical spacings are strictly positive. -/
theorem kernel_facet_fit_unique {L M A B eps σ a b : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hσ : σ = 1 ∨ σ = -1) (hfacet : fluxSignedWidth L M A B = σ * eps)
    (hb : |b| ≤ eps) (hm : |L - (a * A + b)| ≤ eps)
    (he : |L + M - (a * (A + B) + b)| ≤ eps) :
    a = fluxSlope L M A B ∧ b = σ * eps := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hfacet ⊢
    exact kernel_facet_fit_unique_pos hA hB hfacet hb hm he
  · have hn : fluxSignedWidth (-L) (-M) A B = eps := by
      have hh : fluxSignedWidth (-L) (-M) A B = -fluxSignedWidth L M A B := by
        unfold fluxSignedWidth
        ring
      rw [hh, hfacet]
      ring
    have hbn : |-b| ≤ eps := by simpa only [abs_neg] using hb
    have hmn : |-L - ((-a) * A + (-b))| ≤ eps := by
      convert hm using 1
      rw [← abs_neg]
      congr 1
      ring
    have hen : |-L + -M - ((-a) * (A + B) + (-b))| ≤ eps := by
      convert he using 1
      rw [← abs_neg]
      congr 1
      ring
    obtain ⟨ha', hb'⟩ := kernel_facet_fit_unique_pos hA hB hn hbn hmn hen
    have hs : fluxSlope (-L) (-M) A B = -fluxSlope L M A B := by
      unfold fluxSlope
      ring
    rw [hs] at ha'
    exact ⟨neg_inj.mp ha', by linarith⟩

/-- Rigidity for an actual fitting line on an active ordered triple of keys. -/
theorem kernel_prefix_facet_line_unique {eps σ : ℝ} {p : ℕ → ℝ} {k r s t : ℕ}
    (hrs : r < s) (hst : s < t) (htk : t ≤ k) (hA : p r < p s) (hB : p s < p t)
    (hσ : σ = 1 ∨ σ = -1)
    (hfacet : fluxSignedWidth ((s : ℝ) - r) ((t : ℝ) - s)
      (p s - p r) (p t - p s) = σ * eps)
    {a b : ℝ} (hfit : ∀ j < k + 1, |(j : ℝ) - (a * p j + b)| ≤ eps) :
    a = fluxSlope ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) ∧
      b = σ * eps + r - a * p r := by
  have hb : |a * p r + b - r| ≤ eps := by
    convert hfit r (by omega) using 1
    rw [← abs_neg]
    congr 1
    ring
  have hm : |((s : ℝ) - r) - (a * (p s - p r) + (a * p r + b - r))| ≤ eps := by
    convert hfit s (by omega) using 1
    congr 1
    ring
  have he : |((s : ℝ) - r) + ((t : ℝ) - s) -
      (a * ((p s - p r) + (p t - p s)) + (a * p r + b - r))| ≤ eps := by
    convert hfit t (by omega) using 1
    congr 1
    ring
  obtain ⟨ha, hb'⟩ := kernel_facet_fit_unique (sub_pos.mpr hA) (sub_pos.mpr hB) hσ hfacet hb hm he
  exact ⟨ha, by linarith⟩

/-- The residual path selected by the active facet, translated into `[0,2eps]`. -/
def kernelFacetBandCoord (eps σ : ℝ) (p : ℕ → ℝ) (r s t j : ℕ) : ℝ :=
  ((j : ℝ) - r) -
    fluxSlope ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) * (p j - p r) +
      (eps - σ * eps)

theorem kernelFacetBandCoord_eq_residual (eps σ : ℝ) (p : ℕ → ℝ) (r s t j : ℕ) :
    kernelFacetBandCoord eps σ p r s t j =
      ((j : ℝ) - (fluxSlope ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) * p j +
        (σ * eps + r - fluxSlope ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) * p r))) + eps := by
  unfold kernelFacetBandCoord
  ring

/-- On an active facet, the original prefix feasible event is exactly one
specified full-path band event. Strict key order supplies both nonzero spacings. -/
theorem kernel_prefix_facet_band_iff {eps σ : ℝ} {p : ℕ → ℝ} {k r s t : ℕ}
    (hrs : r < s) (hst : s < t) (htk : t ≤ k)
    (hp : ∀ i j, i < j → j ≤ k → p i < p j) (hσ : σ = 1 ∨ σ = -1)
    (hfacet : fluxSignedWidth ((s : ℝ) - r) ((t : ℝ) - s)
      (p s - p r) (p t - p s) = σ * eps) :
    prefixAffineFeasible eps p (k + 1) ↔
      ∀ j ≤ k, kernelFacetBandCoord eps σ p r s t j ∈ Icc 0 (2 * eps) := by
  constructor
  · rintro ⟨a, b, hfit⟩
    obtain ⟨ha, hb⟩ := kernel_prefix_facet_line_unique hrs hst htk
      (hp r s hrs (by omega)) (hp s t hst htk) hσ hfacet hfit
    intro j hj
    rw [kernelFacetBandCoord_eq_residual, ← ha, ← hb]
    obtain ⟨hl, hu⟩ := abs_le.mp (hfit j (by omega))
    exact ⟨by linarith, by linarith⟩
  · intro hband
    refine ⟨fluxSlope ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s),
      σ * eps + r - fluxSlope ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) * p r, ?_⟩
    intro j hj
    have h := hband j (by omega)
    rw [kernelFacetBandCoord_eq_residual] at h
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Specialization to the actual positive-gap prefix sums. -/
theorem kernel_gap_prefix_facet_band_iff {eps σ : ℝ} {g : ℕ → ℝ} {k r s t : ℕ}
    (hg : ∀ j < k, 0 < g j) (hrs : r < s) (hst : s < t) (htk : t ≤ k)
    (hσ : σ = 1 ∨ σ = -1)
    (hfacet : fluxSignedWidth ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s) = σ * eps) :
    prefixAffineFeasible eps (gapKeys g) (k + 1) ↔
      ∀ j ≤ k, kernelFacetBandCoord eps σ (gapKeys g) r s t j ∈ Icc 0 (2 * eps) :=
  kernel_prefix_facet_band_iff hrs hst htk (cert_gapKeys_lt hg) hσ hfacet

/-- The exact same identification after the original one-coordinate gap update. -/
theorem kernel_updated_gap_prefix_facet_band_iff {eps σ x : ℝ} {g : ℕ → ℝ} {k i r s t : ℕ}
    (hx : 0 < x) (hg : ∀ j < k, j ≠ i → 0 < g j)
    (hrs : r < s) (hst : s < t) (htk : t ≤ k) (hσ : σ = 1 ∨ σ = -1)
    (hfacet : fluxSignedWidth ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys (Function.update g i x) s - gapKeys (Function.update g i x) r)
      (gapKeys (Function.update g i x) t - gapKeys (Function.update g i x) s) = σ * eps) :
    prefixAffineFeasible eps (gapKeys (Function.update g i x)) (k + 1) ↔
      ∀ j ≤ k, kernelFacetBandCoord eps σ (gapKeys (Function.update g i x)) r s t j ∈ Icc 0 (2 * eps) := by
  apply kernel_gap_prefix_facet_band_iff ?_ hrs hst htk hσ hfacet
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa using hx
  · simpa only [Function.update_of_ne hji] using hg j hj hji

/-- Ordered rank indices and physical keys give a strictly positive selected slope. -/
theorem kernel_facet_slope_pos {p : ℕ → ℝ} {r s t : ℕ} (hrs : r < s) (hst : s < t)
    (hA : p r < p s) (hB : p s < p t) :
    0 < fluxSlope ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) := by
  have hrt : (r : ℝ) < t := by exact_mod_cast lt_trans hrs hst
  unfold fluxSlope
  apply div_pos <;> linarith

/-- The active triple becomes the three prescribed strip contacts. For the
positive orientation they are `0,2eps,0`, and for the negative orientation
they are `2eps,0,2eps`. -/
theorem kernel_facet_band_contacts {eps σ : ℝ} {p : ℕ → ℝ} {r s t : ℕ}
    (hA : p r < p s) (hB : p s < p t)
    (hfacet : fluxSignedWidth ((s : ℝ) - r) ((t : ℝ) - s)
      (p s - p r) (p t - p s) = σ * eps) :
    kernelFacetBandCoord eps σ p r s t r = eps - σ * eps ∧
      kernelFacetBandCoord eps σ p r s t s = eps + σ * eps ∧
      kernelFacetBandCoord eps σ p r s t t = eps - σ * eps := by
  have hAB : (p s - p r) + (p t - p s) ≠ 0 :=
    ne_of_gt (add_pos (sub_pos.mpr hA) (sub_pos.mpr hB))
  have hc := flux_chord_residuals (L := (s : ℝ) - r) (M := (t : ℝ) - s) hAB
  rw [hfacet] at hc
  refine ⟨by simp [kernelFacetBandCoord], ?_, ?_⟩
  · unfold kernelFacetBandCoord
    nlinarith [hc.1]
  · unfold kernelFacetBandCoord
    nlinarith [hc.2]

/-- Exact one-step residual increments of the selected band path. -/
theorem kernelFacetBandCoord_step (eps σ : ℝ) (p : ℕ → ℝ) (r s t j : ℕ) :
    kernelFacetBandCoord eps σ p r s t (j + 1) =
      kernelFacetBandCoord eps σ p r s t j + 1 -
        fluxSlope ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) * (p (j + 1) - p j) := by
  unfold kernelFacetBandCoord
  push_cast
  ring

/-- For original gap keys the step is exactly `1 - a*g(j)`. -/
theorem kernel_gap_facet_band_step (eps σ : ℝ) (g : ℕ → ℝ) (r s t j : ℕ) :
    kernelFacetBandCoord eps σ (gapKeys g) r s t (j + 1) =
      kernelFacetBandCoord eps σ (gapKeys g) r s t j + 1 -
        fluxSlope ((s : ℝ) - r) ((t : ℝ) - s)
          (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s) * g j := by
  rw [kernelFacetBandCoord_step]
  have h : gapKeys g (j + 1) - gapKeys g j = g j := by simp [gapKeys, Finset.sum_range_succ]
  rw [h]

end
end PGM
