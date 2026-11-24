import PLAStochastic.Index.CEPS.Canonical.RootSymHolo

/-!
# CEPS WP3, lemma C-4 (algebraic part): transport identities for the roots and for `F`

Each root `β` of `ψ_μ(β) = q` satisfies `∂_μ β = -β ∂_q β` (differentiate `ψ_μ(β) = q` in `μ` and
in `q`). For the symmetric functions `S = β₊ + β₋`, `P = β₊ β₋` this gives, on the whole region
`V = {‖μ‖ < μ_c, ‖q - m(μ)‖ < r₁²}` (also at the double root, by continuity in `q`):

  `S_μ = P_q - S S_q`,  `P_μ = -P S_q`   (`cepsRootSum_transport`),

and therefore, for `F = d (s² - γ²)/(s² - S s + P)`,

  `∂_μ F + s ∂_q F = S_q · F`   (`cepsF_transport`),

i.e. `(∂_μ + s ∂_q) log F = S_q` (blueprint (Q4)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- The region `V = {‖μ‖ < μ_c, ‖q - m(μ)‖ < r₁²}`. -/
def cepsSPRegion (D θ : ℝ) (ρW : Measure ℝ) : Set (ℂ × ℂ) :=
  {x | ‖x.1‖ < cepsChartMu D θ ∧ ‖x.2 - cepsMorseMin D θ ρW x.1‖ < cepsChartRho D θ ^ 2}

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

/-- Any square root `σ` (`σ² = w`) gives the same value of an even function. -/
theorem even_comp_eq_of_sq_eq {E : Type*} {Ψ : ℂ → E} (heven : ∀ ρ, Ψ (-ρ) = Ψ ρ) {σ w : ℂ}
    (hσ : σ ^ 2 = w) : Ψ σ = Ψ (Complex.sqrt w) := by
  have h : σ ^ 2 = Complex.sqrt w ^ 2 := by rw [hσ, sqrt_sq_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
  · rw [h']
  · rw [h', heven]

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem isOpen_cepsSPRegion : IsOpen (cepsSPRegion D θ ρW) :=
  CepsCanonDomain.isOpen_SP_region hW hθ hD

omit hW hθ hD in
/-- A local holomorphic square root near `w₀ ≠ 0`. -/
theorem exists_local_sqrt {w₀ : ℂ} (hw₀ : w₀ ≠ 0) :
    ∃ σ : ℂ → ℂ, (∀ w, σ w ^ 2 = w) ∧ (∀ w, ‖σ w‖ = Real.sqrt ‖w‖) ∧
      DifferentiableAt ℂ σ w₀ := by
  rcases mem_slitPlane_or_neg_mem hw₀ with hs | hs
  · exact ⟨Complex.sqrt, sqrt_sq_eq, norm_sqrt, differentiableAt_sqrt hs⟩
  · refine ⟨fun w => I * Complex.sqrt (-w), I_mul_sqrt_neg_sq, fun w => ?_, ?_⟩
    · rw [norm_mul, norm_I, one_mul, norm_sqrt, norm_neg]
    · exact ((differentiableAt_sqrt hs).comp w₀ differentiableAt_id.neg).const_mul I

/-- Root transport at a simple-root point. -/
theorem cepsRootSum_transport_of_ne {μ q : ℂ} (hx : (μ, q) ∈ cepsSPRegion D θ ρW)
    (hne : q - cepsMorseMin D θ ρW μ ≠ 0) :
    deriv (fun μ' => cepsRootSum D θ ρW μ' q) μ =
        deriv (fun q' => cepsRootProd D θ ρW μ q') q -
          cepsRootSum D θ ρW μ q * deriv (fun q' => cepsRootSum D θ ρW μ q') q ∧
      deriv (fun μ' => cepsRootProd D θ ρW μ' q) μ =
        -(cepsRootProd D θ ρW μ q * deriv (fun q' => cepsRootSum D θ ρW μ q') q) := by
  have hr := cepsChartRho_pos hD hθ
  have hV := isOpen_cepsSPRegion hW hθ hD
  obtain ⟨σ, hσsq, hσn, hσd⟩ := exists_local_sqrt hne
  -- the two local roots
  set w : ℂ × ℂ → ℂ := fun x => x.2 - cepsMorseMin D θ ρW x.1 with hw
  set b : ℂ × ℂ → ℂ := fun x => cepsMorseRoot D θ ρW x.1 (σ (w x)) with hb
  set b' : ℂ × ℂ → ℂ := fun x => cepsMorseRoot D θ ρW x.1 (-σ (w x)) with hb'
  have hσlt : ∀ x ∈ cepsSPRegion D θ ρW, ‖σ (w x)‖ < cepsChartRho D θ := by
    intro x hx'
    rw [hσn, Real.sqrt_lt' hr]; exact hx'.2
  -- `S = b + b'`, `P = b b'` on `V`
  have hSV : ∀ x ∈ cepsSPRegion D θ ρW, cepsRootSum D θ ρW x.1 x.2 = b x + b' x := by
    intro x _
    rw [cepsRootSum_eq, ← even_comp_eq_of_sq_eq (cepsPsiS_neg D θ ρW x.1) (hσsq (w x))]
    rfl
  have hPV : ∀ x ∈ cepsSPRegion D θ ρW, cepsRootProd D θ ρW x.1 x.2 = b x * b' x := by
    intro x _
    rw [cepsRootProd_eq, ← even_comp_eq_of_sq_eq (cepsPsiP_neg D θ ρW x.1) (hσsq (w x))]
    rfl
  -- joint differentiability of `b`, `b'`
  have hm := differentiableOn_cepsMorseMin hW hθ hD
  have hμball : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rw [mem_ball, dist_zero_right]; exact hx.1
  have hmd := (hm μ hμball).differentiableAt (isOpen_ball.mem_nhds hμball)
  have hwd : DifferentiableAt ℂ w (μ, q) :=
    differentiableAt_snd.sub (DifferentiableAt.fun_comp' (g := cepsMorseMin D θ ρW)
      (f := fun x : ℂ × ℂ => x.1) (μ, q) hmd differentiableAt_fst)
  have hσw : DifferentiableAt ℂ (fun x => σ (w x)) (μ, q) :=
    DifferentiableAt.fun_comp' (g := σ) (f := w) (μ, q) hσd hwd
  have hΘ := differentiableOn_cepsMorseRoot hW hθ hD
  have hbd : DifferentiableAt ℂ b (μ, q) ∧ DifferentiableAt ℂ b' (μ, q) := by
    have hm1 : ((μ, σ (w (μ, q))) : ℂ × ℂ) ∈
        ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ) :=
      ⟨hμball, by rw [mem_ball, dist_zero_right]; exact hσlt _ hx⟩
    have hm2 : ((μ, -σ (w (μ, q))) : ℂ × ℂ) ∈
        ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ) :=
      ⟨hμball, by rw [mem_ball, dist_zero_right, norm_neg]; exact hσlt _ hx⟩
    have h1 := (hΘ _ hm1).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hm1)
    have h2 := (hΘ _ hm2).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hm2)
    exact ⟨DifferentiableAt.fun_comp' (g := fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2)
        (f := fun x : ℂ × ℂ => ((x.1, σ (w x)) : ℂ × ℂ)) (μ, q) h1
        (differentiableAt_fst.prodMk hσw),
      DifferentiableAt.fun_comp' (g := fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2)
        (f := fun x : ℂ × ℂ => ((x.1, -σ (w x)) : ℂ × ℂ)) (μ, q) h2
        (differentiableAt_fst.prodMk hσw.neg)⟩
  -- partial derivatives along the two lines
  have line1 : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableAt ℂ g (μ, q) →
      HasDerivAt (fun μ' => g (μ', q)) (deriv (fun μ' => g (μ', q)) μ) μ := by
    intro g hg
    exact (DifferentiableAt.fun_comp' (g := g) (f := fun μ' : ℂ => ((μ', q) : ℂ × ℂ)) μ hg
      (differentiableAt_id.prodMk (differentiableAt_const _))).hasDerivAt
  have line2 : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableAt ℂ g (μ, q) →
      HasDerivAt (fun q' => g (μ, q')) (deriv (fun q' => g (μ, q')) q) q := by
    intro g hg
    exact (DifferentiableAt.fun_comp' (g := g) (f := fun q' : ℂ => ((μ, q') : ℂ × ℂ)) q hg
      ((differentiableAt_const _).prodMk differentiableAt_id)).hasDerivAt
  -- the root equation `ψ_{μ'}(b) = q'` on `V`
  have hroot : ∀ x ∈ cepsSPRegion D θ ρW, cepsCgfShift ρW x.1 (b x) = x.2 ∧
      cepsCgfShift ρW x.1 (b' x) = x.2 := by
    intro x hx'
    have h1 := cepsCgfShift_cepsMorseRoot hW hθ hD hx'.1 (hσlt x hx')
    have h2 := cepsCgfShift_cepsMorseRoot hW hθ hD hx'.1 (r := -σ (w x))
      (by rw [norm_neg]; exact hσlt x hx')
    rw [hσsq] at h1
    rw [neg_sq, hσsq] at h2
    exact ⟨by rw [hb]; simp only [hw] at h1 ⊢; rw [h1]; ring,
      by rw [hb']; simp only [hw] at h2 ⊢; rw [h2]; ring⟩
  -- `ψ_μ` is holomorphic at the roots
  have hrootball : ∀ z : ℂ, z = b (μ, q) ∨ z = b' (μ, q) → z ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
    intro z hz
    have hlt : ‖σ (w (μ, q))‖ < cepsChartRho D θ := hσlt _ hx
    rcases hz with h | h
    · rw [h]
      obtain ⟨hu, -⟩ := cepsMorseRoot_sub_center hW hθ hD hx.1 hlt
      rw [mem_ball, dist_zero_right] at hu ⊢
      have hb0 := norm_cepsMorseCenter_lt hW hθ hD hx.1
      have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
      have hr0 := cepsCgfRadius_pos hD hθ
      calc ‖b (μ, q)‖ = ‖cepsMorseCenter D θ ρW μ +
            (cepsMorseRoot D θ ρW μ (σ (w (μ, q))) - cepsMorseCenter D θ ρW μ)‖ := by
            rw [hb]; ring_nf
        _ ≤ _ := norm_add_le _ _
        _ < cepsCgfRadius D θ := by linarith
    · rw [h]
      obtain ⟨hu, -⟩ := cepsMorseRoot_sub_center hW hθ hD hx.1 (r := -σ (w (μ, q)))
        (by rw [norm_neg]; exact hlt)
      rw [mem_ball, dist_zero_right] at hu ⊢
      have hb0 := norm_cepsMorseCenter_lt hW hθ hD hx.1
      have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
      have hr0 := cepsCgfRadius_pos hD hθ
      calc ‖b' (μ, q)‖ = ‖cepsMorseCenter D θ ρW μ +
            (cepsMorseRoot D θ ρW μ (-σ (w (μ, q))) - cepsMorseCenter D θ ρW μ)‖ := by
            rw [hb']; ring_nf
        _ ≤ _ := norm_add_le _ _
        _ < cepsCgfRadius D θ := by linarith
  -- key: `∂_μ β = -β ∂_q β` for `β = b, b'`
  have key : ∀ {β : ℂ × ℂ → ℂ}, DifferentiableAt ℂ β (μ, q) →
      β (μ, q) ∈ ball (0 : ℂ) (cepsCgfRadius D θ) →
      (∀ x ∈ cepsSPRegion D θ ρW, cepsCgfShift ρW x.1 (β x) = x.2) →
      deriv (fun μ' => β (μ', q)) μ = -(β (μ, q) * deriv (fun q' => β (μ, q')) q) := by
    intro β hβ hβball hβroot
    have hψd := (differentiableOn_cepsCgf hW hθ hD _ hβball).differentiableAt
      (isOpen_ball.mem_nhds hβball)
    set ψ' := deriv (cepsCgf ρW) (β (μ, q))
    have h1 := line1 hβ
    have h2 := line2 hβ
    -- along `q`
    have hq : HasDerivAt (fun q' => cepsCgfShift ρW μ (β (μ, q')))
        ((ψ' + μ) * deriv (fun q' => β (μ, q')) q) q := by
      have := (hψd.hasDerivAt.comp q h2).add (h2.const_mul μ)
      refine this.congr_deriv ?_
      ring
    have hq' : HasDerivAt (fun q' => cepsCgfShift ρW μ (β (μ, q'))) 1 q := by
      have hev : (fun q' => cepsCgfShift ρW μ (β (μ, q'))) =ᶠ[𝓝 q] fun q' => q' := by
        have hmem : ∀ᶠ q' in 𝓝 q, ((μ, q') : ℂ × ℂ) ∈ cepsSPRegion D θ ρW :=
          ((continuous_const.prodMk continuous_id).continuousAt (x := q)).preimage_mem_nhds
            (hV.mem_nhds hx)
        filter_upwards [hmem] with q' hq'
        exact hβroot _ hq'
      exact (hasDerivAt_id q).congr_of_eventuallyEq hev
    have e1 := hq.unique hq'
    -- along `μ`
    have hμ : HasDerivAt (fun μ' => cepsCgfShift ρW μ' (β (μ', q)))
        ((ψ' + μ) * deriv (fun μ' => β (μ', q)) μ + β (μ, q)) μ := by
      have := (hψd.hasDerivAt.comp μ h1).add ((hasDerivAt_id μ).mul h1)
      refine this.congr_deriv ?_
      simp only [id]
      ring
    have hμ' : HasDerivAt (fun μ' => cepsCgfShift ρW μ' (β (μ', q))) 0 μ := by
      have hev : (fun μ' => cepsCgfShift ρW μ' (β (μ', q))) =ᶠ[𝓝 μ] fun _ => q := by
        have hmem : ∀ᶠ μ' in 𝓝 μ, ((μ', q) : ℂ × ℂ) ∈ cepsSPRegion D θ ρW :=
          ((continuous_id.prodMk continuous_const).continuousAt (x := μ)).preimage_mem_nhds
            (hV.mem_nhds hx)
        filter_upwards [hmem] with μ' hμ'
        exact hβroot _ hμ'
      exact (hasDerivAt_const μ q).congr_of_eventuallyEq hev
    have e2 := hμ.unique hμ'
    have : deriv (fun μ' => β (μ', q)) μ =
        deriv (fun μ' => β (μ', q)) μ * ((ψ' + μ) * deriv (fun q' => β (μ, q')) q) := by
      rw [e1, mul_one]
    rw [this]
    linear_combination (deriv (fun q' => β (μ, q')) q) * e2
  have kb := key hbd.1 (hrootball _ (Or.inl rfl)) (fun x hx' => (hroot x hx').1)
  have kb' := key hbd.2 (hrootball _ (Or.inr rfl)) (fun x hx' => (hroot x hx').2)
  -- derivatives of `S` and `P` through `b`, `b'`
  have evμ : ∀ {g : ℂ × ℂ → ℂ} {g' : ℂ × ℂ → ℂ}, (∀ x ∈ cepsSPRegion D θ ρW, g x = g' x) →
      deriv (fun μ' => g (μ', q)) μ = deriv (fun μ' => g' (μ', q)) μ := by
    intro g g' hgg
    refine Filter.EventuallyEq.deriv_eq ?_
    have hmem : ∀ᶠ μ' in 𝓝 μ, ((μ', q) : ℂ × ℂ) ∈ cepsSPRegion D θ ρW :=
      ((continuous_id.prodMk continuous_const).continuousAt (x := μ)).preimage_mem_nhds
        (hV.mem_nhds hx)
    filter_upwards [hmem] with μ' hμ'
    exact hgg _ hμ'
  have evq : ∀ {g : ℂ × ℂ → ℂ} {g' : ℂ × ℂ → ℂ}, (∀ x ∈ cepsSPRegion D θ ρW, g x = g' x) →
      deriv (fun q' => g (μ, q')) q = deriv (fun q' => g' (μ, q')) q := by
    intro g g' hgg
    refine Filter.EventuallyEq.deriv_eq ?_
    have hmem : ∀ᶠ q' in 𝓝 q, ((μ, q') : ℂ × ℂ) ∈ cepsSPRegion D θ ρW :=
      ((continuous_const.prodMk continuous_id).continuousAt (x := q)).preimage_mem_nhds
        (hV.mem_nhds hx)
    filter_upwards [hmem] with q' hq'
    exact hgg _ hq'
  have dSμ : deriv (fun μ' => cepsRootSum D θ ρW μ' q) μ =
      deriv (fun μ' => b (μ', q)) μ + deriv (fun μ' => b' (μ', q)) μ := by
    rw [evμ (g := fun x => cepsRootSum D θ ρW x.1 x.2) (g' := fun x => b x + b' x) hSV]
    exact ((line1 hbd.1).add (line1 hbd.2)).deriv
  have dSq : deriv (fun q' => cepsRootSum D θ ρW μ q') q =
      deriv (fun q' => b (μ, q')) q + deriv (fun q' => b' (μ, q')) q := by
    rw [evq (g := fun x => cepsRootSum D θ ρW x.1 x.2) (g' := fun x => b x + b' x) hSV]
    exact ((line2 hbd.1).add (line2 hbd.2)).deriv
  have dPμ : deriv (fun μ' => cepsRootProd D θ ρW μ' q) μ =
      deriv (fun μ' => b (μ', q)) μ * b' (μ, q) + b (μ, q) * deriv (fun μ' => b' (μ', q)) μ := by
    rw [evμ (g := fun x => cepsRootProd D θ ρW x.1 x.2) (g' := fun x => b x * b' x) hPV]
    exact ((line1 hbd.1).mul (line1 hbd.2)).deriv
  have dPq : deriv (fun q' => cepsRootProd D θ ρW μ q') q =
      deriv (fun q' => b (μ, q')) q * b' (μ, q) + b (μ, q) * deriv (fun q' => b' (μ, q')) q := by
    rw [evq (g := fun x => cepsRootProd D θ ρW x.1 x.2) (g' := fun x => b x * b' x) hPV]
    exact ((line2 hbd.1).mul (line2 hbd.2)).deriv
  have hS0 : cepsRootSum D θ ρW μ q = b (μ, q) + b' (μ, q) := hSV _ hx
  have hP0 : cepsRootProd D θ ρW μ q = b (μ, q) * b' (μ, q) := hPV _ hx
  refine ⟨?_, ?_⟩
  · rw [dSμ, dPq, dSq, hS0, kb, kb']; ring
  · rw [dPμ, dSq, hP0, kb, kb']; ring


/-- **Root transport** on the whole region `V` (including the double root). -/
theorem cepsRootSum_transport {μ q : ℂ} (hx : (μ, q) ∈ cepsSPRegion D θ ρW) :
    deriv (fun μ' => cepsRootSum D θ ρW μ' q) μ =
        deriv (fun q' => cepsRootProd D θ ρW μ q') q -
          cepsRootSum D θ ρW μ q * deriv (fun q' => cepsRootSum D θ ρW μ q') q ∧
      deriv (fun μ' => cepsRootProd D θ ρW μ' q) μ =
        -(cepsRootProd D θ ρW μ q * deriv (fun q' => cepsRootSum D θ ρW μ q') q) := by
  by_cases hne : q - cepsMorseMin D θ ρW μ ≠ 0
  · exact cepsRootSum_transport_of_ne hW hθ hD hx hne
  push Not at hne
  have hV := isOpen_cepsSPRegion hW hθ hD
  obtain ⟨hSd, hPd⟩ := differentiableOn_cepsRootSum_joint hW hθ hD
  -- the slice through `μ`
  set O : Set ℂ := {q' | ((μ, q') : ℂ × ℂ) ∈ cepsSPRegion D θ ρW} with hO
  have hOo : IsOpen O := hV.preimage (continuous_const.prodMk continuous_id)
  have hqO : q ∈ O := hx
  have slice : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableOn ℂ g (cepsSPRegion D θ ρW) →
      DifferentiableOn ℂ (fun q' => g (μ, q')) O := by
    intro g hg q' hq'
    have h1 := (hg _ hq').differentiableAt (hV.mem_nhds hq')
    exact (DifferentiableAt.fun_comp' (g := g) (f := fun q' : ℂ => ((μ, q') : ℂ × ℂ)) q' h1
      ((differentiableAt_const _).prodMk differentiableAt_id)).differentiableWithinAt
  have hSs := slice hSd
  have hPs := slice hPd
  have cS : ContinuousAt (fun q' => cepsRootSum D θ ρW μ q') q :=
    (hSs q hqO).continuousWithinAt.continuousAt (hOo.mem_nhds hqO)
  have cP : ContinuousAt (fun q' => cepsRootProd D θ ρW μ q') q :=
    (hPs q hqO).continuousWithinAt.continuousAt (hOo.mem_nhds hqO)
  have cSq : ContinuousAt (fun q' => deriv (fun q' => cepsRootSum D θ ρW μ q') q') q :=
    ((hSs.deriv hOo) q hqO).continuousWithinAt.continuousAt (hOo.mem_nhds hqO)
  have cPq : ContinuousAt (fun q' => deriv (fun q' => cepsRootProd D θ ρW μ q') q') q :=
    ((hPs.deriv hOo) q hqO).continuousWithinAt.continuousAt (hOo.mem_nhds hqO)
  have cSμ : ContinuousAt (fun q' => deriv (fun μ' => cepsRootSum D θ ρW μ' q') μ) q :=
    continuousAt_deriv_fst hV hSd hx
  have cPμ : ContinuousAt (fun q' => deriv (fun μ' => cepsRootProd D θ ρW μ' q') μ) q :=
    continuousAt_deriv_fst hV hPd hx
  -- the identities hold on a punctured neighbourhood of `q`
  have hpunct : ∀ᶠ q' in 𝓝[≠] q, ((μ, q') : ℂ × ℂ) ∈ cepsSPRegion D θ ρW ∧
      q' - cepsMorseMin D θ ρW μ ≠ 0 := by
    have h1 : ∀ᶠ q' in 𝓝[≠] q, q' ∈ O := nhdsWithin_le_nhds (hOo.mem_nhds hqO)
    filter_upwards [h1, self_mem_nhdsWithin] with q' hq'1 hq'2
    refine ⟨hq'1, ?_⟩
    intro h0
    apply hq'2
    have : q' = cepsMorseMin D θ ρW μ := sub_eq_zero.mp h0
    rw [this, ← sub_eq_zero.mp hne]
    exact Set.mem_singleton _
  have lim0 : ∀ {E : ℂ → ℂ}, ContinuousAt E q → (∀ᶠ q' in 𝓝[≠] q, E q' = 0) → E q = 0 := by
    intro E hE hz
    have t1 : Tendsto E (𝓝[≠] q) (𝓝 (E q)) := hE.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto E (𝓝[≠] q) (𝓝 0) := tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm)
    exact tendsto_nhds_unique t1 t2
  refine ⟨?_, ?_⟩
  · have h := lim0 (E := fun q' => deriv (fun μ' => cepsRootSum D θ ρW μ' q') μ -
        (deriv (fun q' => cepsRootProd D θ ρW μ q') q' -
          cepsRootSum D θ ρW μ q' * deriv (fun q' => cepsRootSum D θ ρW μ q') q'))
      (cSμ.sub (cPq.sub (cS.mul cSq))) (hpunct.mono fun q' h => by
        rw [(cepsRootSum_transport_of_ne hW hθ hD h.1 h.2).1]; ring)
    exact sub_eq_zero.mp h
  · have h := lim0 (E := fun q' => deriv (fun μ' => cepsRootProd D θ ρW μ' q') μ +
        cepsRootProd D θ ρW μ q' * deriv (fun q' => cepsRootSum D θ ρW μ q') q')
      (cPμ.add (cP.mul cSq)) (hpunct.mono fun q' h => by
        rw [(cepsRootSum_transport_of_ne hW hθ hD h.1 h.2).2]; ring)
    linear_combination h


/-- **Transport for `F`.** For `(μ, q) ∈ V` and `D₀(s) ≠ 0`:
`∂_μ F(s) + s ∂_q F(s) = S_q · F(s)`. -/
theorem cepsF_transport {γ μ q s : ℂ} (hx : (μ, q) ∈ cepsSPRegion D θ ρW)
    (hne : cepsQuad D θ ρW μ q s ≠ 0) :
    deriv (fun μ' => cepsF D θ ρW γ μ' q s) μ + s * deriv (fun q' => cepsF D θ ρW γ μ q' s) q =
      deriv (fun q' => cepsRootSum D θ ρW μ q') q * cepsF D θ ρW γ μ q s := by
  have hV := isOpen_cepsSPRegion hW hθ hD
  obtain ⟨hSd, hPd⟩ := differentiableOn_cepsRootSum_joint hW hθ hD
  obtain ⟨tS, tP⟩ := cepsRootSum_transport hW hθ hD hx
  have hSx := (hSd _ hx).differentiableAt (hV.mem_nhds hx)
  have hPx := (hPd _ hx).differentiableAt (hV.mem_nhds hx)
  have line1 : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableAt ℂ g (μ, q) →
      HasDerivAt (fun μ' => g (μ', q)) (deriv (fun μ' => g (μ', q)) μ) μ := by
    intro g hg
    exact (DifferentiableAt.fun_comp' (g := g) (f := fun μ' : ℂ => ((μ', q) : ℂ × ℂ)) μ hg
      (differentiableAt_id.prodMk (differentiableAt_const _))).hasDerivAt
  have line2 : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableAt ℂ g (μ, q) →
      HasDerivAt (fun q' => g (μ, q')) (deriv (fun q' => g (μ, q')) q) q := by
    intro g hg
    exact (DifferentiableAt.fun_comp' (g := g) (f := fun q' : ℂ => ((μ, q') : ℂ × ℂ)) q hg
      ((differentiableAt_const _).prodMk differentiableAt_id)).hasDerivAt
  set Sμ := deriv (fun μ' => cepsRootSum D θ ρW μ' q) μ
  set Pμ := deriv (fun μ' => cepsRootProd D θ ρW μ' q) μ
  set Sq := deriv (fun q' => cepsRootSum D θ ρW μ q') q
  set Pq := deriv (fun q' => cepsRootProd D θ ρW μ q') q
  have hS1 : HasDerivAt (fun μ' => cepsRootSum D θ ρW μ' q) Sμ μ :=
    line1 (g := fun x => cepsRootSum D θ ρW x.1 x.2) hSx
  have hP1 : HasDerivAt (fun μ' => cepsRootProd D θ ρW μ' q) Pμ μ :=
    line1 (g := fun x => cepsRootProd D θ ρW x.1 x.2) hPx
  have hS2 : HasDerivAt (fun q' => cepsRootSum D θ ρW μ q') Sq q :=
    line2 (g := fun x => cepsRootSum D θ ρW x.1 x.2) hSx
  have hP2 : HasDerivAt (fun q' => cepsRootProd D θ ρW μ q') Pq q :=
    line2 (g := fun x => cepsRootProd D θ ρW x.1 x.2) hPx
  set A := cexp (-q) * cexp (μ * s) * stepTransform ρW s with hA
  -- `d` along both lines
  have hd1 : HasDerivAt (fun μ' => cepsD ρW μ' q s) (-(A * s)) μ := by
    have h := ((((hasDerivAt_id μ).mul_const s).cexp).const_mul (cexp (-q))).mul_const
      (stepTransform ρW s)
    have h2 := h.const_sub 1
    unfold cepsD
    refine h2.congr_deriv ?_
    rw [hA]; simp; ring
  have hd2 : HasDerivAt (fun q' => cepsD ρW μ q' s) A q := by
    have h := ((((hasDerivAt_id q).neg).cexp).mul_const (cexp (μ * s))).mul_const
      (stepTransform ρW s)
    have h2 := h.const_sub 1
    unfold cepsD
    refine h2.congr_deriv ?_
    rw [hA]; simp
  -- `D₀` along both lines
  have hQ1 : HasDerivAt (fun μ' => cepsQuad D θ ρW μ' q s) (-(Sμ * s) + Pμ) μ := by
    have h := ((hasDerivAt_const μ (s ^ 2)).sub (hS1.mul_const s)).add hP1
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun μ' => cepsQuad_eq_SP D θ ρW μ' q s
  have hQ2 : HasDerivAt (fun q' => cepsQuad D θ ρW μ q' s) (-(Sq * s) + Pq) q := by
    have h := ((hasDerivAt_const q (s ^ 2)).sub (hS2.mul_const s)).add hP2
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun q' => cepsQuad_eq_SP D θ ρW μ q' s
  -- `F = N/D₀`
  have hF1 : HasDerivAt (fun μ' => cepsD ρW μ' q s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ' q s)
      ((-(A * s) * (s ^ 2 - γ ^ 2) * cepsQuad D θ ρW μ q s -
        cepsD ρW μ q s * (s ^ 2 - γ ^ 2) * (-(Sμ * s) + Pμ)) / cepsQuad D θ ρW μ q s ^ 2) μ :=
    (hd1.mul_const (s ^ 2 - γ ^ 2)).div hQ1 hne
  have hF2 : HasDerivAt (fun q' => cepsD ρW μ q' s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q' s)
      ((A * (s ^ 2 - γ ^ 2) * cepsQuad D θ ρW μ q s -
        cepsD ρW μ q s * (s ^ 2 - γ ^ 2) * (-(Sq * s) + Pq)) / cepsQuad D θ ρW μ q s ^ 2) q :=
    (hd2.mul_const (s ^ 2 - γ ^ 2)).div hQ2 hne
  have e1 : (fun μ' => cepsF D θ ρW γ μ' q s) =
      fun μ' => cepsD ρW μ' q s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ' q s := by
    funext μ'; rfl
  have e2 : (fun q' => cepsF D θ ρW γ μ q' s) =
      fun q' => cepsD ρW μ q' s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q' s := by
    funext q'; rfl
  rw [e1, e2, hF1.deriv, hF2.deriv]
  have hQ0 : cepsQuad D θ ρW μ q s = s ^ 2 - cepsRootSum D θ ρW μ q * s + cepsRootProd D θ ρW μ q :=
    cepsQuad_eq_SP D θ ρW μ q s
  have hF : cepsF D θ ρW γ μ q s =
      cepsD ρW μ q s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q s := rfl
  rw [hF, tS, tP]
  field_simp
  rw [hQ0]
  ring

end

end PGM
