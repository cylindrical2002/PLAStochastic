import PLAStochastic.Index.CEPS.Central.Newton

/-! # A local analytic branch for the two Newton base roots

The principal base roots may exchange when the frequency crosses the square-root cut, but
the pair of roots does not. At a non-merger frequency `z`, an analytic local square root of
`w + λ²/(2V)` gives an analytic root `ρ(w)` with partner `-2λ/V - ρ(w)`; every node-symmetric
kernel of the two Newton iterations equals its value along this branch for all `w`. -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

variable {d N : ℕ}

/-- The local analytic square root of `w + λ²/(2V)` through the principal value at `z`. -/
def cepsCentralBranchSqrt (V lam z w : ℂ) : ℂ :=
  Complex.sqrt (z + lam ^ 2 / (2 * V)) *
    Complex.sqrt (1 + (w - z) / (z + lam ^ 2 / (2 * V)))

/-- The analytic branch of the zero-scale root. -/
def cepsCentralBranchRoot (V lam z w : ℂ) : ℂ :=
  -lam / V + Complex.sqrt (2 / V) * cepsCentralBranchSqrt V lam z w

theorem cepsCentralBranchSqrt_sq {V lam z : ℂ} (hm : z + lam ^ 2 / (2 * V) ≠ 0) (w : ℂ) :
    cepsCentralBranchSqrt V lam z w ^ 2 = w + lam ^ 2 / (2 * V) := by
  rw [cepsCentralBranchSqrt, mul_pow, sqrt_sq_eq, sqrt_sq_eq, mul_add, mul_one,
    mul_div_cancel₀ _ hm]
  ring

theorem cepsCentralBranchSqrt_self (V lam z : ℂ) :
    cepsCentralBranchSqrt V lam z z = Complex.sqrt (z + lam ^ 2 / (2 * V)) := by
  simp [cepsCentralBranchSqrt]

theorem cepsCentralBranchSqrt_analyticAt (V lam z : ℂ) :
    AnalyticAt ℂ (cepsCentralBranchSqrt V lam z) z := by
  have h1 : (fun w : ℂ => 1 + (w - z) / (z + lam ^ 2 / (2 * V))) z ∈ slitPlane := by
    simp only [sub_self, zero_div, add_zero]
    exact one_mem_slitPlane
  have hsqrt := Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds h1)
  have hin : AnalyticAt ℂ (fun w : ℂ => 1 + (w - z) / (z + lam ^ 2 / (2 * V))) z :=
    analyticAt_const.add ((analyticAt_id.sub analyticAt_const).div_const)
  exact analyticAt_const.mul (hsqrt.comp (f := fun w : ℂ => 1 + (w - z) / (z + lam ^ 2 / (2 * V)))
    (x := z) hin)

theorem cepsCentralBranchRoot_analyticAt (V lam z : ℂ) :
    AnalyticAt ℂ (cepsCentralBranchRoot V lam z) z :=
  analyticAt_const.add (analyticAt_const.mul (cepsCentralBranchSqrt_analyticAt V lam z))

theorem cepsCentralBranchRoot_root {V lam z : ℂ} (hV : V ≠ 0)
    (hm : z + lam ^ 2 / (2 * V) ≠ 0) (w : ℂ) :
    cepsCentralBranchRoot V lam z w ^ 2 * (V / 2) + lam * cepsCentralBranchRoot V lam z w = w := by
  have hs := cepsCentralBranchSqrt_sq hm w
  have hc : Complex.sqrt (2 / V) ^ 2 = 2 / V := sqrt_sq_eq _
  rw [cepsCentralBranchRoot]
  generalize cepsCentralBranchSqrt V lam z w = σ at hs ⊢
  generalize Complex.sqrt (2 / V) = c at hc ⊢
  have e : (-lam / V + c * σ) ^ 2 * (V / 2) + lam * (-lam / V + c * σ) =
      (c ^ 2) * σ ^ 2 * (V / 2) - lam ^ 2 / (2 * V) := by
    field_simp
    ring
  rw [e, hc, hs]
  field_simp
  ring

theorem cepsCentralBranchRoot_gap {V lam z : ℂ} (hV : V ≠ 0) (w : ℂ) :
    lam + V * cepsCentralBranchRoot V lam z w =
      V * Complex.sqrt (2 / V) * cepsCentralBranchSqrt V lam z w := by
  rw [cepsCentralBranchRoot]
  field_simp
  ring

theorem cepsCentralBranchRoot_gap_ne {V lam z : ℂ} (hV : V ≠ 0)
    (hm : z + lam ^ 2 / (2 * V) ≠ 0) :
    lam + V * cepsCentralBranchRoot V lam z z ≠ 0 := by
  rw [cepsCentralBranchRoot_gap hV]
  have hc : Complex.sqrt (2 / V) ≠ 0 := by
    intro h0
    have := sqrt_sq_eq (2 / V)
    rw [h0, zero_pow two_ne_zero] at this
    exact div_ne_zero two_ne_zero hV this.symm
  have hσ : cepsCentralBranchSqrt V lam z z ≠ 0 := by
    intro h0
    have := cepsCentralBranchSqrt_sq hm z
    rw [h0, zero_pow two_ne_zero] at this
    exact hm this.symm
  exact mul_ne_zero (mul_ne_zero hV hc) hσ

theorem cepsCentralBranchRoot_self (q : Fin d → ℂ) (lam : ℝ) (z : ℂ) :
    cepsCentralBranchRoot (cepsComplexJetPad d q (cepsJetCode (.inl 0))) lam z z =
      cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z 1 := by
  rw [cepsCentralBranchRoot, cepsCentralBranchSqrt_self, cepsComplexCumulantRootBase, one_mul]

theorem cepsCentralBranchRoot_partner_self (q : Fin d → ℂ) (lam : ℝ) (z : ℂ) :
    -2 * (lam : ℂ) / cepsComplexJetPad d q (cepsJetCode (.inl 0)) -
        cepsCentralBranchRoot (cepsComplexJetPad d q (cepsJetCode (.inl 0))) lam z z =
      cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam z (-1) := by
  rw [cepsCentralBranchRoot, cepsCentralBranchSqrt_self, cepsComplexCumulantRootBase]
  ring

/-- Every node-symmetric kernel of the two Newton root models is its value along the
analytic branch, for every frequency `w`. -/
theorem cepsCentral_rootModel_symm_eq_branch {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    (hsym : ∀ x a₁ a₂, F x a₁ a₂ = F x a₂ a₁) (q : Fin d → ℂ) (lam : ℝ) {z : ℂ}
    (hm : z + (lam : ℂ) ^ 2 / (2 * cepsComplexJetPad d q (cepsJetCode (.inl 0))) ≠ 0)
    (w b : ℂ) :
    F (q, lam, w, b) (cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w 1 N b)
        (cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w (-1) N b) =
      F (q, lam, w, b)
        (cepsCentralNewton d N q lam w
          (cepsCentralBranchRoot (cepsComplexJetPad d q (cepsJetCode (.inl 0))) lam z w) N b)
        (cepsCentralNewton d N q lam w (-2 * (lam : ℂ) / cepsComplexJetPad d q (cepsJetCode (.inl 0)) -
          cepsCentralBranchRoot (cepsComplexJetPad d q (cepsJetCode (.inl 0))) lam z w) N b) := by
  set V := cepsComplexJetPad d q (cepsJetCode (.inl 0)) with hVdef
  rw [cepsComplexCumulantRootModel_eq_central, cepsComplexCumulantRootModel_eq_central]
  have hsq : Complex.sqrt (w + (lam : ℂ) ^ 2 / (2 * V)) ^ 2 =
      cepsCentralBranchSqrt V lam z w ^ 2 := by
    rw [sqrt_sq_eq, cepsCentralBranchSqrt_sq hm]
  have hb₁ : ∀ ε : ℂ, cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam w ε =
      -(lam : ℂ) / V + ε * Complex.sqrt (2 / V) * Complex.sqrt (w + (lam : ℂ) ^ 2 / (2 * V)) :=
    fun _ => rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · have e₁ : cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam w 1 =
        cepsCentralBranchRoot V lam z w := by
      rw [hb₁, h, cepsCentralBranchRoot]
      ring
    have e₂ : cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam w (-1) =
        -2 * (lam : ℂ) / V - cepsCentralBranchRoot V lam z w := by
      rw [hb₁, h, cepsCentralBranchRoot]
      ring
    rw [e₁, e₂]
  · have e₁ : cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam w 1 =
        -2 * (lam : ℂ) / V - cepsCentralBranchRoot V lam z w := by
      rw [hb₁, h, cepsCentralBranchRoot]
      ring
    have e₂ : cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam w (-1) =
        cepsCentralBranchRoot V lam z w := by
      rw [hb₁, h, cepsCentralBranchRoot]
      ring
    rw [e₁, e₂, hsym]

end PGM
