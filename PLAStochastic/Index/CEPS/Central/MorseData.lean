import PLAStochastic.Index.CEPS.Central.MorseDescent
import PLAStochastic.Index.CEPS.Scaled.ComplexJetMorseScaleEquation
import PLAStochastic.Index.CEPS.Scaled.ComplexJetMorseRoot

/-! # Local Morse data at every input near the reference input

The critical center `η` and the signed Morse root `Θ` produced at the reference input
satisfy their defining identities on genuine neighborhoods, so the same local data hold at
every nearby finite input `q`. There the radial derivative `τ` of the Morse root satisfies
`τ² V(q) / 2 = 1`, which fixes the zero-scale value of the scaled Morse roots. -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

/-- Local Morse data for the finite cumulant polynomial at the input `p`. -/
structure CepsCentralMorseData (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ) (p : Fin d → ℂ) : Prop where
  hη : AnalyticAt ℂ η (p, 0)
  hΘ : AnalyticAt ℂ Θ ((p, 0), 0)
  hV : cepsComplexJetPad d p (cepsJetCode (.inl 0)) ≠ 0
  hc : ∀ᶠ u in 𝓝 (p, (0 : ℂ)),
    deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0
  hz : ∀ᶠ u in 𝓝 (p, (0 : ℂ)), Θ (u, 0) = η u
  hηz : ∀ᶠ p' in 𝓝 p, η (p', 0) = 0
  hroot : ∀ᶠ u in 𝓝 ((p, (0 : ℂ)), (0 : ℂ)),
    cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N (Θ u) + u.1.2 * Θ u =
      cepsComplexCgfJetMinimum d N η u.1 + u.2 ^ 2

variable {d N : ℕ} {η : (Fin d → ℂ) × ℂ → ℂ} {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ}

/-- The Morse data propagate from the reference input to all nearby inputs. -/
theorem CepsCentralMorseData.eventually {p₀ : Fin d → ℂ}
    (h : CepsCentralMorseData d N η Θ p₀) :
    ∀ᶠ q in 𝓝 p₀, CepsCentralMorseData d N η Θ q := by
  have hm : Continuous (fun q : Fin d → ℂ => (q, (0 : ℂ))) := continuous_id.prodMk continuous_const
  have hm' : Continuous (fun q : Fin d → ℂ => ((q, (0 : ℂ)), (0 : ℂ))) := hm.prodMk continuous_const
  have tm : Tendsto (fun q : Fin d → ℂ => (q, (0 : ℂ))) (𝓝 p₀) (𝓝 (p₀, 0)) :=
    hm.continuousAt.tendsto
  have tm' : Tendsto (fun q : Fin d → ℂ => ((q, (0 : ℂ)), (0 : ℂ))) (𝓝 p₀) (𝓝 ((p₀, 0), 0)) :=
    hm'.continuousAt.tendsto
  have hV : ∀ᶠ q in 𝓝 p₀, cepsComplexJetPad d q (cepsJetCode (.inl 0)) ≠ 0 :=
    (cepsComplexJetPad_continuous d _).continuousAt.eventually_ne h.hV
  filter_upwards [tm.eventually h.hη.eventually_analyticAt, tm'.eventually h.hΘ.eventually_analyticAt,
    hV, tm.eventually h.hc.eventually_nhds, tm.eventually h.hz.eventually_nhds,
    h.hηz.eventually_nhds, tm'.eventually h.hroot.eventually_nhds] with q h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The genuine reference Morse data produced by the actual finite cumulant Morse root. -/
theorem exists_cepsCentralMorseData (d N : ℕ) (p₀ : Fin d → ℂ)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0) :
    ∃ η : (Fin d → ℂ) × ℂ → ℂ, ∃ Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ,
      CepsCentralMorseData d N η Θ p₀ := by
  let s₀ := Complex.sqrt (cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) / 2)
  have hsq : s₀ ^ 2 = cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) / 2 := sqrt_sq_eq _
  have hs₀ : s₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsq
    exact div_ne_zero hV two_ne_zero hsq.symm
  obtain ⟨η, -, Θ, -, hη, -, -, -, hΘ, -, -, -, -, hroot, -, -, -, hc, -, hz, hηz⟩ :=
    exists_cepsComplexCgfJetModel_morse_root (K := PUnit.{1}) d N p₀ s₀ hs₀ hsq
  exact ⟨η, Θ, hη, hΘ, hV, hc, hz, hηz, hroot⟩

/-! ## Consequences at a single input -/

namespace CepsCentralMorseData

variable {q : Fin d → ℂ}

theorem center_zero (h : CepsCentralMorseData d N η Θ q) : η (q, 0) = 0 := h.hηz.self_of_nhds

theorem root_zero (h : CepsCentralMorseData d N η Θ q) : Θ ((q, 0), 0) = 0 :=
  h.hz.self_of_nhds.trans h.center_zero

/-- The radial derivative of the Morse root at the critical point. -/
def tau (_h : CepsCentralMorseData d N η Θ q) : ℂ := deriv (fun t : ℂ => Θ ((q, 0), t)) 0

theorem tau_sq (h : CepsCentralMorseData d N η Θ q) :
    h.tau ^ 2 * (cepsComplexJetPad d q (cepsJetCode (.inl 0)) / 2) = 1 := by
  let θ : ℂ → ℂ := fun t => Θ ((q, 0), t)
  let P : ℂ → ℂ := cepsCgfComplexJetPolynomial (cepsComplexJetPad d q) N
  have hline : AnalyticAt ℂ (fun t : ℂ => ((q, (0 : ℂ)), t)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hθ : AnalyticAt ℂ θ 0 := h.hΘ.comp_of_eq hline rfl
  have hθ0 : θ 0 = 0 := h.root_zero
  have tline : Tendsto (fun t : ℂ => ((q, (0 : ℂ)), t)) (𝓝 0) (𝓝 ((q, 0), 0)) :=
    hline.continuousAt.tendsto
  have heq : ∀ᶠ t in 𝓝 (0 : ℂ), θ t ^ 2 * P (θ t) = t ^ 2 := by
    filter_upwards [tline.eventually h.hroot] with t ht
    change cepsComplexCgfJetModel (cepsComplexJetPad d q) N (θ t) + 0 * θ t =
      cepsComplexCgfJetMinimum d N η (q, 0) + t ^ 2 at ht
    simp only [cepsComplexCgfJetMinimum, h.center_zero, cepsComplexCgfJetModel, zero_mul,
      add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at ht
    exact ht
  let θ₁ : ℂ → ℂ := dslope θ 0
  have hfac : ∀ t, θ t = t * θ₁ t := by
    intro t
    have hs := sub_smul_dslope θ 0 t
    rw [hθ0, sub_zero, sub_zero, smul_eq_mul] at hs
    exact hs.symm
  let φ : ℂ → ℂ := fun t => θ₁ t ^ 2 * P (θ t)
  have hθ₁c : ContinuousAt θ₁ 0 := continuousAt_dslope_same.mpr hθ.differentiableAt
  have hPc : ContinuousAt (fun t => P (θ t)) 0 := by
    have hpi : ∀ i, AnalyticAt ℂ (fun _ : ℂ => cepsComplexJetPad d q i) 0 :=
      fun _ => analyticAt_const
    exact (cepsCgfComplexJetPolynomial_analyticAt hpi hθ N).continuousAt
  have hφc : ContinuousAt φ 0 := (hθ₁c.pow 2).mul hPc
  have hφ1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), φ t = 1 := by
    filter_upwards [nhdsWithin_le_nhds heq, self_mem_nhdsWithin] with t ht hne
    have hne' : t ^ 2 ≠ 0 := pow_ne_zero 2 hne
    have ht' : t ^ 2 * φ t = t ^ 2 * 1 := by
      calc t ^ 2 * φ t = (t * θ₁ t) ^ 2 * P (θ t) := by simp only [φ]; ring
        _ = θ t ^ 2 * P (θ t) := by rw [← hfac t]
        _ = t ^ 2 * 1 := by rw [ht, mul_one]
    exact mul_left_cancel₀ hne' ht'
  have hlim : Tendsto φ (𝓝[≠] (0 : ℂ)) (𝓝 1) :=
    tendsto_const_nhds.congr' (hφ1.mono fun _ ht => ht.symm)
  have hlim' : Tendsto φ (𝓝[≠] (0 : ℂ)) (𝓝 (φ 0)) := hφc.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : φ 0 = 1 := tendsto_nhds_unique hlim' hlim
  have hP0 : P 0 = cepsComplexJetPad d q (cepsJetCode (.inl 0)) / 2 :=
    cepsCgfComplexJetPolynomial_zero _ N
  simp only [φ, θ₁, dslope_same, hθ0, hP0] at h1
  exact h1

theorem tau_ne_zero (h : CepsCentralMorseData d N η Θ q) : h.tau ≠ 0 := by
  intro h0
  have := h.tau_sq
  rw [h0] at this
  simp at this

theorem hasDerivAt_tau (h : CepsCentralMorseData d N η Θ q) :
    HasDerivAt (fun t : ℂ => Θ ((q, 0), t)) (h.tau⁻¹)⁻¹ 0 := by
  rw [inv_inv]
  have hline : AnalyticAt ℂ (fun t : ℂ => ((q, (0 : ℂ)), t)) 0 :=
    analyticAt_const.prod analyticAt_id
  exact (h.hΘ.comp_of_eq hline rfl).differentiableAt.hasDerivAt

/-- Zero-scale value of the scaled Morse roots at the input `q`. -/
theorem scaleRoot_zero (h : CepsCentralMorseData d N η Θ q) (lam r : ℂ) :
    cepsComplexJetMorseScaleRoot d Θ q lam r 0 =
      -lam / cepsComplexJetPad d q (cepsJetCode (.inl 0)) + r * h.tau := by
  rw [cepsComplexJetMorseScaleRoot_zero h.hΘ h.hη h.center_zero h.hV h.hc h.hz h.hasDerivAt_tau,
    div_inv_eq_mul]

theorem scaleRoot_equation (h : CepsCentralMorseData d N η Θ q) (lam r : ℂ) :
    ∀ᶠ u in 𝓝 (((q, lam), r), (0 : ℂ)),
      (cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2) ^ 2 *
          cepsCgfComplexJetPolynomial (cepsComplexJetPad d u.1.1.1) N
            (u.2 * cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2) +
        u.1.1.2 * cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2 =
      u.1.1.2 ^ 2 * cepsComplexCgfJetMinimumUnit d N η (u.1.1.1, u.2 * u.1.1.2) +
        u.1.2 ^ 2 :=
  cepsComplexJetMorseScaleRoot_equation_eventually h.hΘ h.hη h.hz h.hηz h.hc h.hroot lam r

theorem square_zero (h : CepsCentralMorseData d N η Θ q) (lam z : ℂ) :
    cepsComplexJetMorseSquare d N η q lam z 0 =
      z + lam ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) :=
  cepsComplexJetMorseSquare_zero h.hη h.center_zero h.hV h.hc lam z

end CepsCentralMorseData

end PGM
