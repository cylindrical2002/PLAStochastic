import PLAStochastic.Index.CEPS.Contour.Regularity

/-!
# X9: C-3(c) and C-4 for `dom.canonL` under an arbitrary Sobolev weight

For `f_W ∈ CepsSobolevClass m η` with any `η > 0` (no `2 c₀ ≤ η`), the statements of WP3's
`contDiffOn_cepsCanonL_mu`, `iteratedDeriv_cepsCanonL_mu`, the jet bounds, the mixed bounds
`norm_mixed_cepsCanonL_le`, `cepsCanonL_transport_of_sobolev` and
`hasDerivAt_cepsCanonR_mu_of_sobolev` hold for the same values `dom.canonL`, on the line
`Re s = (dom.contour η hη).c₀ = min c₀ (η/2)` and the parameter ranges of `dom.contour η hη`
(constants depending only on `dom` and `η`).
-/

noncomputable section

open MeasureTheory Set Complex
open PGM.WienerHopf

namespace PGM

namespace CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

variable {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW) (hη : 0 < η)
include hf

theorem iteratedDeriv_canonL_mu_contour {q : ℂ} (hq : ‖q‖ ≤ (dom.contour η hη).q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re < (dom.contour η hη).c₀) {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.contour η hη).μ₀ / 4) :
    iteratedDeriv (n + 1) (fun t' : ℝ => dom.canonL ρW t' q ζ) t =
      cepsCanonLJet D θ ρW (dom.contour η hη).c₀ n t q ζ :=
  dom.iteratedDeriv_canonL_mu_shrink hW hθ hD (lt_min dom.c₀_pos (half_pos hη))
    (min_le_left _ _) hf (dom.two_contour_c₀_le hη) hq hζ hn ht

/-- **C-3(c) for any `η > 0`.** -/
theorem contDiffOn_canonL_mu_contour (hm : 2 ≤ m) {q : ℂ}
    (hq : ‖q‖ ≤ (dom.contour η hη).q₀ / 2) {ζ : ℂ} (hζ : ζ.re < (dom.contour η hη).c₀) :
    ContDiffOn ℝ (m - 2 : ℕ) (fun t' : ℝ => dom.canonL ρW t' q ζ)
      (Ioo (-((dom.contour η hη).μ₀ / 4)) ((dom.contour η hη).μ₀ / 4)) :=
  dom.contDiffOn_canonL_mu_shrink hW hθ hD (lt_min dom.c₀_pos (half_pos hη))
    (min_le_left _ _) hf hm (dom.two_contour_c₀_le hη) hq hζ

theorem norm_iteratedDeriv_canonL_mu_le_contour {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.contour η hη).μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ (dom.contour η hη).q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re < (dom.contour η hη).c₀) :
    ‖iteratedDeriv (n + 1) (fun t' : ℝ => dom.canonL ρW t' q ζ) t‖ ≤
      (2 * Real.pi)⁻¹ * ((dom.contour η hη).jetC n * (cepsSobolev m η fW + 1)) *
        (Real.pi / (dom.contour η hη).c₀ + Real.pi / ((dom.contour η hη).c₀ - ζ.re)) :=
  dom.norm_iteratedDeriv_canonL_mu_le_shrink hW hθ hD (lt_min dom.c₀_pos (half_pos hη))
    (min_le_left _ _) hf (dom.two_contour_c₀_le hη) hn ht hq hζ

/-- **C-3(c), uniform jet bound for any `η > 0`.** -/
theorem norm_iteratedDeriv_canonL_mu_le_uniform_contour {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.contour η hη).μ₀ / 4) {q : ℂ} (hq : ‖q‖ ≤ (dom.contour η hη).q₀ / 2)
    {ζ : ℂ} (hζ : ζ.re ≤ (dom.contour η hη).c₀ / 2) :
    ‖iteratedDeriv (n + 1) (fun t' : ℝ => dom.canonL ρW t' q ζ) t‖ ≤
      3 * ((dom.contour η hη).jetC n * (cepsSobolev m η fW + 1)) /
        (2 * (dom.contour η hη).c₀) :=
  dom.norm_iteratedDeriv_canonL_mu_le_uniform_shrink hW hθ hD (lt_min dom.c₀_pos (half_pos hη))
    (min_le_left _ _) hf (dom.two_contour_c₀_le hη) hn ht hq hζ

/-- **C-3(c), mixed bounds for any `η > 0`.** -/
theorem norm_mixed_canonL_le_contour {n : ℕ} (hn : n + 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.contour η hη).μ₀ / 4) {ζ₀ q₁ : ℂ} (hζ₀ : ‖ζ₀‖ ≤ (dom.contour η hη).c₀ / 4)
    (hq₁ : ‖q₁‖ ≤ (dom.contour η hη).q₀ / 4) (l k : ℕ) :
    ‖iteratedDeriv k (fun q => iteratedDeriv l (fun ζ =>
        iteratedDeriv (n + 1) (fun t' : ℝ => dom.canonL ρW t' q ζ) t) ζ₀) q₁‖ ≤
      k.factorial * (l.factorial * (3 * ((dom.contour η hη).jetC n *
        (cepsSobolev m η fW + 1)) / (2 * (dom.contour η hη).c₀)) /
          ((dom.contour η hη).c₀ / 8) ^ l) / ((dom.contour η hη).q₀ / 8) ^ k :=
  dom.norm_mixed_canonL_le_shrink hW hθ hD (lt_min dom.c₀_pos (half_pos hη))
    (min_le_left _ _) hf (dom.two_contour_c₀_le hη) hn ht hζ₀ hq₁ l k

/-- **C-4 for any `η > 0`.** -/
theorem canonL_transport_contour (hm : 2 ≤ m) {t : ℝ} (ht : |t| < (dom.contour η hη).μ₀ / 2)
    {q : ℂ} (hq : ‖q‖ < (dom.contour η hη).q₀ / 4) {ζ : ℂ}
    (hζ : ζ.re < (dom.contour η hη).c₀) :
    deriv (fun t' : ℝ => dom.canonL ρW t' q ζ) t +
        ζ * deriv (fun q' : ℂ => dom.canonL ρW t q' ζ) q =
      deriv (fun t' : ℝ => dom.canonL ρW t' q 0) t :=
  dom.canonL_transport_shrink hW hθ hD (lt_min dom.c₀_pos (half_pos hη))
    (min_le_left _ _) hf hm (dom.two_contour_c₀_le hη) ht hq hζ

/-- **C-4, remainder form for any `η > 0`.** -/
theorem hasDerivAt_canonR_mu_contour (hm : 2 ≤ m) {t : ℝ}
    (ht : |t| < (dom.contour η hη).μ₀ / 2) {q : ℂ} (hq : ‖q‖ < (dom.contour η hη).q₀ / 4)
    {ζ : ℂ} (hζ : ζ.re < (dom.contour η hη).c₀) :
    HasDerivAt (fun t' : ℝ => dom.canonL ρW t' q ζ - dom.canonL ρW t' q 0)
      (-(ζ * deriv (fun q' : ℂ => dom.canonL ρW t q' ζ) q)) t :=
  dom.hasDerivAt_canonR_mu_shrink hW hθ hD (lt_min dom.c₀_pos (half_pos hη))
    (min_le_left _ _) hf hm (dom.two_contour_c₀_le hη) ht hq hζ

end

end CepsCanonDomain

end PGM
