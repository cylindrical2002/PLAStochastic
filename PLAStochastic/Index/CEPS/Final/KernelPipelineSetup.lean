import PLAStochastic.Index.CEPS.Final.KernelGlueIdentity
import PLAStochastic.Index.CEPS.Final.MeanEndpointTaylor
import PLAStochastic.Index.CEPS.Final.Pipeline

/-! # The analytic pipeline data of the kernel coefficients

The outer strip budgets and the central exact-root kernel (packages S and M) are bundled in
`CepsKernelPackages` in their proved forms. From them, for every order, the concrete low-band
coefficient `cepsKernelGk j` and the drift integral of the mean coefficient `cepsKernelCs k`
are written as kernels of `CepsAnalyticPipeline` on a box around the reference jets.
-/

noncomputable section
open Complex Metric Set Filter Topology MeasureTheory Finset
namespace PGM

/-- The kernel results of packages S and M, in their proved forms. -/
structure CepsKernelPackages : Prop where
  pair : ∀ d N : ℕ, CepsStripPairBudget d N
  endpoint : ∀ d N : ℕ, CepsStripEndpointBudget d N
  discount : ∀ d N : ℕ, CepsDiscountBudget d N
  bridge : ∀ d N : ℕ, CepsStripBridgeAnalytic d N
  central : ∀ (d N : ℕ) (p₀ : Fin d → ℝ),
    0 < (cepsComplexJetPad d (fun i => (p₀ i : ℂ)) (cepsJetCode (.inl 0))).re →
      CepsCentralPairKernel d N p₀

theorem cepsJetCode_variance_lt (j : ℕ) : cepsJetCode (.inl 0) < cepsJetDim (4 * (j + 1)) :=
  cepsJetCode_lt_cepsJetDim (show cepsJetWeight (.inl 0) ≤ 4 * (j + 1) by simp [cepsJetWeight])

theorem cepsPipelineWeight_mono {K₁ K₂ c₁ c₂ : ℝ} {e₁ e₂ : ℕ} (hK₁ : 0 ≤ K₁) (hK : K₁ ≤ K₂)
    (he : e₁ ≤ e₂) (hc : c₂ ≤ c₁) (z : ℂ) :
    K₁ * (1 + ‖z‖) ^ e₁ * Real.exp (-c₁ * Real.sqrt ‖z‖) ≤
      K₂ * (1 + ‖z‖) ^ e₂ * Real.exp (-c₂ * Real.sqrt ‖z‖) := by
  have h1 : (1 + ‖z‖) ^ e₁ ≤ (1 + ‖z‖) ^ e₂ := pow_le_pow_right₀ (by linarith [norm_nonneg z]) he
  have h2 : Real.exp (-c₁ * Real.sqrt ‖z‖) ≤ Real.exp (-c₂ * Real.sqrt ‖z‖) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg ‖z‖])
  exact mul_le_mul (mul_le_mul hK h1 (by positivity) (hK₁.trans hK)) h2 (by positivity)
    (by positivity [(hK₁.trans hK)])

namespace CepsGlueData

variable {d N : ℕ} (G : CepsGlueData d N)

theorem integrandEnvelope_nonneg (j : ℕ) {KD δD : ℝ} (hKD : 0 ≤ KD) (hδD : 0 < δD)
    (hMH : 0 ≤ G.MH) (lam : ℝ) : 0 ≤ G.integrandEnvelope j KD δD lam := by
  unfold integrandEnvelope
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (by positivity) (G.gluedEnvelope_nonneg x.2 lam hMH)

end CepsGlueData

/-- The reference jets restricted to the first `d` coordinates. -/
def cepsRefJets (d : ℕ) : Fin d → ℝ := fun i => cepsJetLaw cepsLambda i

theorem cepsRefJets_variance_pos (j : ℕ) :
    0 < cepsRefJets (cepsJetDim (4 * (j + 1))) ⟨cepsJetCode (.inl 0), cepsJetCode_variance_lt j⟩ :=
  cepsJetLaw_cepsLambda_variance_pos

theorem cepsRefJets_pad_variance_pos (j : ℕ) :
    0 < (cepsComplexJetPad (cepsJetDim (4 * (j + 1)))
      (fun i => (cepsRefJets (cepsJetDim (4 * (j + 1))) i : ℂ)) (cepsJetCode (.inl 0))).re := by
  rw [cepsComplexJetPad_apply _ (cepsJetCode_variance_lt j)]
  simpa using cepsRefJets_variance_pos j

/-- A real box around the reference jets lies in the gluing polydisc and keeps the variance
positive. -/
theorem cepsRef_box_facts {d j : ℕ} (hd : d = cepsJetDim (4 * (j + 1))) (G : CepsGlueData d N)
    (hc₀ : G.c₀ = fun i => (cepsRefJets d i : ℂ))
    (hR : G.R ≤ cepsJetLaw cepsLambda (cepsJetCode (.inl 0)) / 16) {p : ℕ → ℝ}
    (hp : ∀ i : Fin d, |p i - cepsJetLaw cepsLambda i| ≤ min (G.R / 2)
      (cepsJetLaw cepsLambda (cepsJetCode (.inl 0)) / 2)) :
    cepsJetEmbed d p ∈ ball G.c₀ G.R ∧ 0 < p (cepsJetCode (.inl 0)) := by
  subst hd
  have hV := cepsJetLaw_cepsLambda_variance_pos
  constructor
  · have h := cepsPipelineEmb_mem_ball (d := cepsJetDim (4 * (j + 1))) (p₀ := cepsJetLaw cepsLambda)
      (p := p) (R := G.R) (by positivity [G.hR]) (lt_of_le_of_lt (min_le_left _ _) (half_lt_self G.hR)) hp
    rw [hc₀]
    exact h
  · have h := hp ⟨cepsJetCode (.inl 0), cepsJetCode_variance_lt j⟩
    have h2 := (abs_le.mp (h.trans (min_le_right _ _))).1
    simp only at h2
    linarith

end PGM
