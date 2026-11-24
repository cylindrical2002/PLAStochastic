import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfCriticalData

/-! # Actual finite cumulant critical values and their drift derivatives -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def cepsComplexCgfJetMinimum (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (u : (Fin d → ℂ) × ℂ) : ℂ :=
  cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N (η u) + u.2 * η u

def cepsContinuousCgfJetMinimum (d N : ℕ)
    (Η : (Fin d → ℂ) × C(K, ℂ) → C(K, ℂ)) (u : (Fin d → ℂ) × C(K, ℂ)) : C(K, ℂ) :=
  cepsContinuousCgfJetModel (cepsComplexJetPad d u.1) N (Η u) + u.2 * Η u

theorem cepsContinuousCgfJetMinimum_analyticAt {d N : ℕ}
    {Η : (Fin d → ℂ) × C(K, ℂ) → C(K, ℂ)} {u : (Fin d → ℂ) × C(K, ℂ)}
    (hΗ : AnalyticAt ℂ Η u) : AnalyticAt ℂ (cepsContinuousCgfJetMinimum d N Η) u := by
  apply (cepsContinuousCgfJetModel_analyticAt (p := fun v => cepsComplexJetPad d v.1)
    (S := Η) (x := u) _ hΗ N).add (analyticAt_snd.mul hΗ)
  intro i
  simpa only [Function.comp_apply] using!
    (cepsComplexJetPad_analyticAt d i u.1).comp (x := u)
      (f := (Prod.fst : (Fin d → ℂ) × C(K, ℂ) → Fin d → ℂ)) analyticAt_fst

omit [CompactSpace K] in
theorem cepsContinuousCgfJetMinimum_apply (d N : ℕ)
    (η : (Fin d → ℂ) × ℂ → ℂ) (Η : (Fin d → ℂ) × C(K, ℂ) → C(K, ℂ))
    (u : (Fin d → ℂ) × C(K, ℂ)) (k : K) (he : Η u k = η (u.1, u.2 k)) :
    cepsContinuousCgfJetMinimum d N Η u k = cepsComplexCgfJetMinimum d N η (u.1, u.2 k) := by
  simp [cepsContinuousCgfJetMinimum, cepsComplexCgfJetMinimum, cepsContinuousCgfJetModel_apply, he]

theorem cepsComplexCgfJetMinimum_analyticAt {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {u : (Fin d → ℂ) × ℂ} (hη : AnalyticAt ℂ η u) :
    AnalyticAt ℂ (cepsComplexCgfJetMinimum d N η) u := by
  apply (cepsComplexCgfJetModel_analyticAt (p := fun v => cepsComplexJetPad d v.1)
    (s := η) (x := u) _ hη N).add (analyticAt_snd.mul hη)
  intro i
  simpa only [Function.comp_apply] using!
    (cepsComplexJetPad_analyticAt d i u.1).comp (x := u)
      (f := (Prod.fst : (Fin d → ℂ) × ℂ → Fin d → ℂ)) analyticAt_fst

theorem cepsComplexCgfJetMinimum_deriv_eventually {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0))
    (hc : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0) :
    ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (fun t => cepsComplexCgfJetMinimum d N η (u.1, t)) u.2 = η u := by
  filter_upwards [hη.eventually_analyticAt, hc] with u hu hc
  have hηs : AnalyticAt ℂ (fun t : ℂ => η (u.1, t)) u.2 := hu.curry_right
  have hF : AnalyticAt ℂ (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) :=
    cepsComplexCgfJetModel_analyticAt (p := fun _ : ℂ => cepsComplexJetPad d u.1)
      (s := id) (x := η u) (fun _ => analyticAt_const) analyticAt_id N
  have hd := (hF.differentiableAt.hasDerivAt.comp u.2 hηs.differentiableAt.hasDerivAt).add
    ((hasDerivAt_id u.2).mul hηs.differentiableAt.hasDerivAt)
  have hv : deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) *
        deriv (fun t => η (u.1, t)) u.2 +
        (1 * η u + u.2 * deriv (fun t => η (u.1, t)) u.2) = η u := by
    linear_combination deriv (fun t => η (u.1, t)) u.2 * hc
  calc
    deriv (fun t => cepsComplexCgfJetMinimum d N η (u.1, t)) u.2 =
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) *
        deriv (fun t => η (u.1, t)) u.2 +
        (1 * η u + u.2 * deriv (fun t => η (u.1, t)) u.2) := by
      simpa only [cepsComplexCgfJetMinimum, Pi.add_def, Pi.mul_def, Function.comp_def, id_eq]
        using! hd.deriv
    _ = η u := hv

theorem cepsComplexCgfJetCenter_hasDerivAt_zero {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) (hη₀ : η (p₀, 0) = 0)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0)
    (hc : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0) :
    HasDerivAt (fun t : ℂ => η (p₀, t))
      (-(cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)))⁻¹) 0 := by
  let V := cepsComplexJetPad d p₀ (cepsJetCode (.inl 0))
  let a : ℂ → ℂ := fun t => η (p₀, t)
  have ha : AnalyticAt ℂ a 0 := hη.curry_right
  have ha₀ : a 0 = 0 := hη₀
  have hF : HasDerivAt (deriv (cepsComplexCgfJetModel (cepsComplexJetPad d p₀) N)) V (a 0) := by
    simpa only [ha₀] using cepsComplexCgfJetModel_deriv_hasDerivAt_zero (cepsComplexJetPad d p₀) N
  have hd := (hF.comp 0 ha.differentiableAt.hasDerivAt).add (hasDerivAt_id (0 : ℂ))
  have hm : AnalyticAt ℂ (fun t : ℂ => (p₀, t)) 0 := analyticAt_const.prod analyticAt_id
  have he : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝 0]
      (fun t => deriv (cepsComplexCgfJetModel (cepsComplexJetPad d p₀) N) (a t) + t) := by
    filter_upwards [hm.continuousAt.tendsto.eventually hc] with t ht
    exact ht.symm
  have he' : V * deriv a 0 + 1 = 0 :=
    (hd.congr_of_eventuallyEq he).unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
  have hda : deriv a 0 = -V⁻¹ := by
    have he'' : V * deriv a 0 = -1 := eq_neg_of_add_eq_zero_left he'
    calc
      deriv a 0 = V⁻¹ * (V * deriv a 0) := by
        rw [← mul_assoc, inv_mul_cancel₀ hV, one_mul]
      _ = -V⁻¹ := by rw [he'']; ring
  simpa only [hda] using ha.differentiableAt.hasDerivAt

theorem cepsComplexCgfJetMinimum_deriv_hasDerivAt_zero {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) (hη₀ : η (p₀, 0) = 0)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0)
    (hc : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0) :
    HasDerivAt (deriv (fun t => cepsComplexCgfJetMinimum d N η (p₀, t)))
      (-(cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)))⁻¹) 0 := by
  have hm : AnalyticAt ℂ (fun t : ℂ => (p₀, t)) 0 := analyticAt_const.prod analyticAt_id
  have he : deriv (fun t => cepsComplexCgfJetMinimum d N η (p₀, t)) =ᶠ[𝓝 0]
      (fun t => η (p₀, t)) := by
    filter_upwards [hm.continuousAt.tendsto.eventually
      (cepsComplexCgfJetMinimum_deriv_eventually hη hc)] with t ht
    exact ht
  exact (cepsComplexCgfJetCenter_hasDerivAt_zero hη hη₀ hV hc).congr_of_eventuallyEq he

end PGM
