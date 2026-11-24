import PLAStochastic.Index.CEPS.Final.IntegrandMeasurability

/-! # The low-band coefficient through the glued integrand

On the reference polydisc, at real jet vectors with positive variance, `cepsKernelGk j p y` is
the endpoint scale coefficient minus the drift integral of the glued integrand: the glued and
Newton coefficients differ only at zero drift on the imaginary axis.
-/

noncomputable section
open Complex Metric Set Filter Topology MeasureTheory Finset
namespace PGM

namespace CepsGlueData

variable {d N : ℕ} (G : CepsGlueData d N)

theorem cepsComplexJetPad_cepsJetEmbed_variance {d : ℕ} (hcode : cepsJetCode (.inl 0) < d)
    (p : ℕ → ℝ) :
    cepsComplexJetPad d (cepsJetEmbed d p) (cepsJetCode (.inl 0)) = (p (cepsJetCode (.inl 0)) : ℂ) := by
  rw [cepsComplexJetPad_cepsJetEmbed]
  simp [cepsJetTruncate, hcode]

/-- The glued coefficient is drift integrable on the imaginary axis and integrates to the
Newton drift integral at real vectors with positive variance. -/
theorem integral_glued_eq (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩) (hc₀ : G.c₀ = fun i => (p₀ i : ℂ))
    (hR : G.R ≤ p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16) (hMH : 0 ≤ G.MH) {δf δbf : ℝ}
    (hδf : 0 < δf) (hδbf : 0 < δbf) (hf : CepsBridgeStripAt d N p₀ hcode G.F₀ δf δbf)
    {p : ℕ → ℝ} (hq : cepsJetEmbed d p ∈ ball G.c₀ G.R) (hpV : 0 < p (cepsJetCode (.inl 0)))
    (y : ℝ) {n : ℕ} (hn : n ≤ N) :
    Integrable (fun lam => cepsGluedPairCoeff d N n G.H G.lc G.zc (cepsJetEmbed d p) lam (I * y)) ∧
    ∫ lam, cepsGluedPairCoeff d N n G.H G.lc G.zc (cepsJetEmbed d p) lam (I * y) =
      ∫ lam, cepsKernelPairCoeffC d N n (cepsJetEmbed d p) lam (I * y) := by
  have hz : -G.δ ≤ (I * (y : ℂ)).re := by simp [G.hδ.le]
  have hzf : -δf ≤ (I * (y : ℂ)).re := by simp [hδf.le]
  have hm := G.glued_aestronglyMeasurable p₀ hcode hV hc₀ hR hδbf hf hq hz hzf n
  have hint : Integrable (fun lam => cepsGluedPairCoeff d N n G.H G.lc G.zc (cepsJetEmbed d p) lam (I * y)) := by
    refine ((G.gluedEnvelope_integrable n).mul_const ((1 + ‖I * (y : ℂ)‖) ^ (G.e + n) *
      Real.exp (-G.c * Real.sqrt ‖I * (y : ℂ)‖))).mono' hm (Eventually.of_forall fun lam => ?_)
    exact G.glued_norm_le hq lam hz hMH
  refine ⟨hint, integral_congr_ae ?_⟩
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with lam hlam
  refine G.glued_eq_of_ne hq lam ?_ hn
  rw [cepsComplexJetPad_cepsJetEmbed_variance hcode p]
  exact cepsMerger_ne_of_imaginary hpV hlam y

/-- `Ĝ_j` as endpoint coefficient minus the drift integral of the glued integrand. -/
theorem cepsKernelGk_eq_integrand {j : ℕ} (G : CepsGlueData d (j + 1))
    (hd : cepsJetDim (4 * (j + 1)) ≤ d) (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩) (hc₀ : G.c₀ = fun i => (p₀ i : ℂ))
    (hR : G.R ≤ p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16) (hMH : 0 ≤ G.MH) {δf δbf : ℝ}
    (hδf : 0 < δf) (hδbf : 0 < δbf) (hf : CepsBridgeStripAt d (j + 1) p₀ hcode G.F₀ δf δbf)
    {p : ℕ → ℝ} (hq : cepsJetEmbed d p ∈ ball G.c₀ G.R) (hpV : 0 < p (cepsJetCode (.inl 0)))
    (y : ℝ) :
    cepsKernelGk j p y = cepsKernelEndpointCoeffC d j (cepsJetEmbed d p) (I * y) -
      ∫ lam, cepsKernelPairIntegrand G j (cepsJetEmbed d p) lam (I * y) := by
  rw [cepsKernelGk_eq_complex hd p y]
  congr 1
  unfold cepsKernelPairIntegrand
  have hI (x : ℕ × ℕ) (hx : x ∈ antidiagonal j) := G.integral_glued_eq p₀ hcode hV hc₀ hR hMH hδf hδbf
    hf hq hpV y (n := x.2) (by have := mem_antidiagonal.mp hx; omega)
  rw [integral_finsetSum _ fun x hx => (hI x hx).1.const_mul _]
  refine sum_congr rfl fun x hx => ?_
  rw [integral_const_mul, (hI x hx).2]

/-- The mean coefficient through the glued pair coefficient at zero frequency. -/
theorem cepsKernelCs_eq_glued {k : ℕ} (G : CepsGlueData d (k + 1))
    (hd : cepsJetDim (4 * (k + 1)) ≤ d) (p₀ : Fin d → ℝ) (hcode : cepsJetCode (.inl 0) < d)
    (hV : 0 < p₀ ⟨cepsJetCode (.inl 0), hcode⟩) (hc₀ : G.c₀ = fun i => (p₀ i : ℂ))
    (hR : G.R ≤ p₀ ⟨cepsJetCode (.inl 0), hcode⟩ / 16) (hMH : 0 ≤ G.MH) {δf δbf : ℝ}
    (hδf : 0 < δf) (hδbf : 0 < δbf) (hf : CepsBridgeStripAt d (k + 1) p₀ hcode G.F₀ δf δbf)
    {p : ℕ → ℝ} (hq : cepsJetEmbed d p ∈ ball G.c₀ G.R) (hpV : 0 < p (cepsJetCode (.inl 0))) :
    cepsKernelCs k p = (cepsScaleCoeff k (cepsZeroEndpointJetPolynomial p k) +
      ∫ lam, cepsGluedPairCoeff d (k + 1) k G.H G.lc G.zc (cepsJetEmbed d p) lam 0).re := by
  rw [cepsKernelCs_eq_complex hd p]
  have h := (G.integral_glued_eq p₀ hcode hV hc₀ hR hMH hδf hδbf hf hq hpV 0 (n := k)
    (by omega)).2
  simp only [Complex.ofReal_zero, mul_zero] at h
  rw [h]

end CepsGlueData

end PGM
