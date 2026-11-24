import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfCriticalData
import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfFunctionalUnit
import PLAStochastic.ForMathlib.Analysis.Complex.CompactMorseInverse

/-! # Actual finite-input Morse roots with spatially varying functional drift -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

set_option maxHeartbeats 800000 in
/-- Genuine roots of the finite cumulant polynomial in the signed Morse variable,
jointly with every finite input coordinate and the drift. The functional drift and
signed root coordinate need not be constant on the compact set. -/
theorem exists_cepsComplexCgfJetModel_morse_root (d N : ℕ) (p₀ : Fin d → ℂ)
    (s₀ : ℂ) (hs₀ : s₀ ≠ 0)
    (hsq : s₀ ^ 2 = cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) / 2) :
    ∃ η : (Fin d → ℂ) × ℂ → ℂ, ∃ Η : (Fin d → ℂ) × C(K, ℂ) → C(K, ℂ),
    ∃ Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ,
    ∃ Τ : ((Fin d → ℂ) × C(K, ℂ)) × C(K, ℂ) → C(K, ℂ),
      AnalyticAt ℂ η (p₀, 0) ∧ η (p₀, 0) = 0 ∧
      AnalyticAt ℂ Η (p₀, 0) ∧ Η (p₀, 0) = 0 ∧
      AnalyticAt ℂ Θ ((p₀, 0), 0) ∧ Θ ((p₀, 0), 0) = 0 ∧
      HasDerivAt (fun t : ℂ => Θ ((p₀, 0), t)) s₀⁻¹ 0 ∧
      AnalyticAt ℂ Τ ((p₀, 0), 0) ∧ Τ ((p₀, 0), 0) = 0 ∧
      (∀ᶠ u in 𝓝 ((p₀, (0 : ℂ)), (0 : ℂ)),
        cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N (Θ u) + u.1.2 * Θ u =
        cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N (η u.1) +
          u.1.2 * η u.1 + u.2 ^ 2) ∧
      (∀ᶠ u in 𝓝 ((p₀, (0 : C(K, ℂ))), (0 : C(K, ℂ))), ∀ k,
        cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N (Τ u k) + u.1.2 k * Τ u k =
        cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N (Η u.1 k) +
          u.1.2 k * Η u.1 k + (u.2 k) ^ 2) ∧
      (∀ᶠ u in 𝓝 ((p₀, (0 : C(K, ℂ))), (0 : C(K, ℂ))), ∀ k,
        Τ u k = Θ ((u.1.1, u.1.2 k), u.2 k)) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k, Η u k = η (u.1, u.2 k)) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
        deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k,
        deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (Η u k) + u.2 k = 0) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), Θ (u, 0) = η u) ∧
      (∀ᶠ p in 𝓝 p₀, η (p, 0) = 0) := by
  let E := Fin d → ℂ
  let F := E × C(K, ℂ)
  have hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0 := by
    intro h
    have hz : s₀ ^ 2 = 0 := by simpa [h] using hsq
    exact pow_ne_zero 2 hs₀ hz
  obtain ⟨η, Η, hη, hη₀, hΗ, hΗ₀, hc, hC, he, hz⟩ :=
    exists_cepsComplexCgfJetModel_functional_critical_center (K := K) d N p₀ hV
  let U : (E × ℂ) × ℂ → ℂ := fun u =>
    cepsComplexCgfJetUnit (cepsComplexJetPad d u.1.1) N (η u.1) u.2
  let W : F × C(K, ℂ) → C(K, ℂ) :=
    cepsContinuousCgfFunctionalJetUnit (fun u => cepsComplexJetPad d u.1.1) N
      (fun u => Η u.1) Prod.snd
  have hηf : AnalyticAt ℂ (fun u : (E × ℂ) × ℂ => η u.1) ((p₀, 0), 0) :=
    by simpa only [Function.comp_apply] using!
      hη.comp (x := ((p₀, 0), 0)) (f := (Prod.fst : (E × ℂ) × ℂ → E × ℂ)) analyticAt_fst
  have hmap : AnalyticAt ℂ (fun u : (E × ℂ) × ℂ => ((u.1.1, η u.1), u.2))
      ((p₀, 0), 0) :=
    ((analyticAt_fst.comp analyticAt_fst).prod hηf).prod analyticAt_snd
  have hU : AnalyticAt ℂ U ((p₀, 0), 0) := by
    have hu : AnalyticAt ℂ (fun v : (E × ℂ) × ℂ =>
        cepsComplexCgfJetUnit (cepsComplexJetPad d v.1.1) N v.1.2 v.2)
        ((p₀, η (p₀, 0)), 0) := by
      simpa only [hη₀] using cepsComplexCgfJetUnit_pad_analyticAt d N ((p₀, 0), 0)
    simpa only [Function.comp_apply] using!
      hu.comp (x := ((p₀, 0), 0))
        (f := fun u : (E × ℂ) × ℂ => ((u.1.1, η u.1), u.2)) hmap
  have hU₀ : U ((p₀, 0), 0) = s₀ ^ 2 := by
    simp only [U, hη₀, cepsComplexCgfJetUnit_zero]
    exact hsq.symm
  have hp : ∀ (v : F × C(K, ℂ)) i,
      AnalyticAt ℂ (fun u : F × C(K, ℂ) => cepsComplexJetPad d u.1.1 i) v := by
    intro v i
    simpa only [Function.comp_apply] using!
      (cepsComplexJetPad_analyticAt d i v.1.1).comp (x := v)
        (f := fun u : F × C(K, ℂ) => u.1.1) (analyticAt_fst.comp analyticAt_fst)
  have hΗf : AnalyticAt ℂ (fun u : F × C(K, ℂ) => Η u.1) ((p₀, 0), 0) := by
    simpa only [Function.comp_apply] using!
      hΗ.comp (x := ((p₀, 0), 0)) (f := (Prod.fst : F × C(K, ℂ) → F)) analyticAt_fst
  have hW : AnalyticAt ℂ W ((p₀, 0), 0) :=
    cepsContinuousCgfFunctionalJetUnit_analyticAt (hp _) hΗf analyticAt_snd
  have hW₀ : W ((p₀, 0), 0) = ContinuousMap.const K (s₀ ^ 2) := by
    unfold W
    rw [cepsContinuousCgfFunctionalJetUnit_zero (A := fun u : F × C(K, ℂ) => Η u.1)
      (X := Prod.snd) (u := ((p₀, 0), 0)) (hp _) hΗ₀ rfl]
    exact congrArg (ContinuousMap.const K) hsq.symm
  have hWe : ∀ᶠ u in 𝓝 ((p₀, (0 : C(K, ℂ))), (0 : C(K, ℂ))), ∀ k,
      W u k = U (compactParameterEvalCLM k u.1, u.2 k) := by
    filter_upwards [continuousAt_fst.tendsto.eventually he] with u hu
    intro k
    change cepsContinuousCgfFunctionalJetUnit (fun v : F × C(K, ℂ) => cepsComplexJetPad d v.1.1)
      N (fun v => Η v.1) Prod.snd u k = _
    rw [cepsContinuousCgfFunctionalJetUnit_apply (hp u) k]
    change cepsComplexCgfJetUnit (cepsComplexJetPad d u.1.1) N (Η u.1 k) (u.2 k) =
      cepsComplexCgfJetUnit (cepsComplexJetPad d u.1.1) N (η (u.1.1, u.1.2 k)) (u.2 k)
    rw [hu k]
  obtain ⟨r, R, hr, hr₀, hdr, hR, hR₀, hrr, hRR, hRe, hrz⟩ :=
    exists_analytic_compact_morse_inverse_oriented
      (E := E × ℂ) (F := F) (K := K)
      (L := fun k => compactParameterEvalCLM (E := E) k)
      (U := U) (W := W) (s₀ := s₀)
      (p₀ := (p₀, 0)) (P₀ := (p₀, 0))
      (fun _ => rfl)
      (fun k => compactParameterEvalCLM_norm_le_one k) hs₀ hU hU₀ hW hW₀ hWe
  let Θ : (E × ℂ) × ℂ → ℂ := fun u => η u.1 + r u
  let Τ : F × C(K, ℂ) → C(K, ℂ) := fun u => Η u.1 + R u
  have hdΘ : HasDerivAt (fun t : ℂ => Θ ((p₀, 0), t)) s₀⁻¹ 0 := by
    have hm : HasDerivAt (fun t : ℂ => ((p₀, (0 : ℂ)), t)) (0, 1) 0 :=
      (hasDerivAt_const 0 (p₀, (0 : ℂ))).prodMk (hasDerivAt_id 0)
    simpa [Θ] using! (hdr.comp_hasDerivAt 0 hm).const_add (η (p₀, 0))
  refine ⟨η, Η, Θ, Τ, hη, hη₀, hΗ, hΗ₀, hηf.add hr, by simp [Θ, hη₀, hr₀],
    hdΘ, hΗf.add hR, by simp [Τ, hΗ₀, hR₀], ?_, ?_, ?_, he, hc, hC, ?_, hz⟩
  · filter_upwards [hrr, continuousAt_fst.tendsto.eventually hc] with u hu hc
    change (r u) ^ 2 * cepsComplexCgfJetUnit (cepsComplexJetPad d u.1.1) N (η u.1) (r u) =
      u.2 ^ 2 at hu
    change deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N) (η u.1) + u.1.2 = 0 at hc
    change cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N (η u.1 + r u) +
      u.1.2 * (η u.1 + r u) = _
    rw [cepsComplexCgfJetUnit_spec]
    linear_combination (r u) * hc + hu
  · filter_upwards [hRR, continuousAt_fst.tendsto.eventually hC] with u hu hc
    intro k
    have hj := congrArg (fun S : C(K, ℂ) => S k) hu
    change (R u k) ^ 2 * W (u.1, R u) k = (u.2 k) ^ 2 at hj
    unfold W at hj
    rw [cepsContinuousCgfFunctionalJetUnit_apply (hp (u.1, R u)) k] at hj
    change cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N (Η u.1 k + R u k) +
      u.1.2 k * (Η u.1 k + R u k) = _
    rw [cepsComplexCgfJetUnit_spec]
    linear_combination (R u k) * hc k + hj
  · filter_upwards [hRe, continuousAt_fst.tendsto.eventually he] with u hu he
    intro k
    simp only [Τ, Θ, ContinuousMap.add_apply, he k, hu k]
    rfl
  · filter_upwards [hrz] with u hu
    change r (u, 0) = 0 at hu
    simp [Θ, hu]

end PGM
