import PLAStochastic.Index.CEPS.Canonical.TransportIdentity
import PLAStochastic.Index.CEPS.Canonical.LineDecay

/-!
# CEPS WP3, lemma C-4 in the Sobolev class

The transport identity `∂_μ L(ζ) + ζ ∂_q L(ζ) = ∂_μ ℓ` and its remainder form
`∂_μ (L(ζ) - ℓ) = -ζ ∂_q L(ζ)`, with the line decay hypothesis discharged by
`f_W ∈ CepsSobolevClass m η`, `m ≥ 2`, `2 c₀ ≤ η`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

omit hθ hD in
theorem line_decay_of_sobolev {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m)
    (hη : 2 * dom.c₀ ≤ η) {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) (y : ℝ) :
    ‖stepTransform ρW (c + y * I)‖ ≤ 2 * cepsSobolev m η fW / (1 + y ^ 2) := by
  have hc0 := dom.c₀_pos
  exact norm_stepTransform_line_le_of_sobolev hW hf hm
    (by rw [abs_of_pos (by linarith)]; linarith) y

/-- **C-4 (Sobolev class).** -/
theorem cepsCanonL_transport_of_sobolev {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η) {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| < dom.μ₀ / 2) {q : ℂ}
    (hq : ‖q‖ < dom.q₀ / 4) {ζ : ℂ} (hζ : ζ.re < c) :
    deriv (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ) t +
        ζ * deriv (fun q' : ℂ => cepsCanonL D θ ρW γ c t q' ζ) q =
      deriv (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q 0) t :=
  dom.cepsCanonL_transport hW hθ hD hγ1 hγ2 hc1 hc2
    (dom.line_decay_of_sobolev hW hf hm hη hc1 hc2) ht hq hζ

/-- **C-4, remainder form (Sobolev class).** `∂_μ (L(ζ) - ℓ) = -ζ ∂_q L(ζ)`. -/
theorem hasDerivAt_cepsCanonR_mu_of_sobolev {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η) {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {t : ℝ} (ht : |t| < dom.μ₀ / 2) {q : ℂ}
    (hq : ‖q‖ < dom.q₀ / 4) {ζ : ℂ} (hζ : ζ.re < c) :
    HasDerivAt (fun t' : ℝ => cepsCanonL D θ ρW γ c t' q ζ - cepsCanonL D θ ρW γ c t' q 0)
      (-(ζ * deriv (fun q' : ℂ => cepsCanonL D θ ρW γ c t q' ζ) q)) t :=
  dom.hasDerivAt_cepsCanonR_mu hW hθ hD hγ1 hγ2 hc1 hc2
    (dom.line_decay_of_sobolev hW hf hm hη hc1 hc2) ht hq hζ

end

end CepsCanonDomain

end PGM
