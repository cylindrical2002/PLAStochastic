import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfCenterLift

/-! # Coherent scalar and functional critical centers for the actual finite cumulant function -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem exists_cepsComplexCgfJetModel_functional_critical_center (d N : ℕ)
    (p₀ : Fin d → ℂ) (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0) :
    ∃ η : (Fin d → ℂ) × ℂ → ℂ, ∃ Η : (Fin d → ℂ) × C(K, ℂ) → C(K, ℂ),
      AnalyticAt ℂ η (p₀, 0) ∧ η (p₀, 0) = 0 ∧
      AnalyticAt ℂ Η (p₀, 0) ∧ Η (p₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
        deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k,
        deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (Η u k) + u.2 k = 0) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k, Η u k = η (u.1, u.2 k)) ∧
      (∀ᶠ p in 𝓝 p₀, η (p, 0) = 0) := by
  let E := Fin d → ℂ
  obtain ⟨g, G, hg, hg₀, hG, hG₀, hr, hGr, he, hl⟩ :=
    exists_cepsComplexCgfJetModel_derivative_inverse_lift (K := K) d N p₀ hV
  let L : E × ℂ →L[ℂ] E × ℂ :=
    (ContinuousLinearMap.fst ℂ E ℂ).prod (-ContinuousLinearMap.snd ℂ E ℂ)
  let M : E × C(K, ℂ) →L[ℂ] E × C(K, ℂ) :=
    (ContinuousLinearMap.fst ℂ E C(K, ℂ)).prod (-ContinuousLinearMap.snd ℂ E C(K, ℂ))
  have hL₀ : L (p₀, 0) = (p₀, 0) := by simp [L]
  have hM₀ : M (p₀, 0) = (p₀, 0) := by simp [M]
  have htL : Tendsto L (𝓝 (p₀, (0 : ℂ))) (𝓝 (p₀, (0 : ℂ))) := by
    simpa only [hL₀] using L.continuous.continuousAt.tendsto (x := (p₀, 0))
  have htM : Tendsto M (𝓝 (p₀, (0 : C(K, ℂ)))) (𝓝 (p₀, (0 : C(K, ℂ)))) := by
    simpa only [hM₀] using M.continuous.continuousAt.tendsto (x := (p₀, 0))
  have hg' : AnalyticAt ℂ g (L (p₀, 0)) := by simpa only [hL₀] using hg
  have hG' : AnalyticAt ℂ G (M (p₀, 0)) := by simpa only [hM₀] using hG
  let η := g ∘ L
  let Η := G ∘ M
  refine ⟨η, Η, hg'.comp (L.analyticAt _), by simpa [η, hL₀] using hg₀,
    hG'.comp (M.analyticAt _), by simpa [Η, hM₀] using hG₀, ?_, ?_, ?_, ?_⟩
  · filter_upwards [htL.eventually hr] with u hu
    change deriv (cepsComplexCgfJetModel (cepsComplexJetPad d (L u).1) N) (g (L u)) = (L u).2 at hu
    have h : deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) = -u.2 := by
      simpa [η, L] using hu
    rw [h]
    exact neg_add_cancel _
  · filter_upwards [htM.eventually hGr] with u hu
    intro k
    have h : deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (Η u k) = -u.2 k := by
      simpa [Η, M] using hu k
    rw [h]
    exact neg_add_cancel _
  · filter_upwards [htM.eventually he] with u hu
    intro k
    simpa [Η, η, M, L] using hu k
  · have hm : AnalyticAt ℂ (fun p : E => (p, (0 : ℂ))) p₀ :=
      analyticAt_id.prod analyticAt_const
    filter_upwards [hm.continuousAt.tendsto.eventually hl] with p hp
    change g (p, deriv (cepsComplexCgfJetModel (cepsComplexJetPad d p) N) 0) = 0 at hp
    simpa [η, L, cepsComplexCgfJetModel_deriv_zero] using hp

end PGM
