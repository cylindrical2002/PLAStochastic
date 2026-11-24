import PLAStochastic.Index.CEPS.Canonical.Transport
import PLAStochastic.Index.CEPS.Canonical.Factor

/-!
# CEPS WP3, lemma C-4: logarithmic derivatives of `F` on the lines

Explicit first derivatives of `log F(s; μ, q)` (`F = d (s² - γ²)/D₀`):

* `cepsDmuLogF = -s A/d + (S_μ s - P_μ)/D₀` (`hasDerivAt_logF_mu`),
* `cepsDqLogF = A/d + (S_q s - P_q)/D₀` (`hasDerivAt_logF_q`),

and the pointwise transport identity `∂_μ log F + s ∂_q log F = S_q` (`cepsDmuLogF_add`),
which follows from `S_μ = P_q - S S_q`, `P_μ = -P S_q`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `S_μ`. -/
def cepsSmu (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ := deriv (fun μ' => cepsRootSum D θ ρW μ' q) μ
/-- `P_μ`. -/
def cepsPmu (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ := deriv (fun μ' => cepsRootProd D θ ρW μ' q) μ
/-- `S_q`. -/
def cepsSq (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ := deriv (fun q' => cepsRootSum D θ ρW μ q') q
/-- `P_q`. -/
def cepsPq (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ := deriv (fun q' => cepsRootProd D θ ρW μ q') q

/-- `∂_μ log F(s) = -s A/d + (S_μ s - P_μ)/D₀`. -/
def cepsDmuLogF (D θ : ℝ) (ρW : Measure ℝ) (μ q s : ℂ) : ℂ :=
  -(s * cepsA ρW μ q s) / cepsD ρW μ q s +
    (cepsSmu D θ ρW μ q * s - cepsPmu D θ ρW μ q) / cepsQuad D θ ρW μ q s

/-- `∂_q log F(s) = A/d + (S_q s - P_q)/D₀`. -/
def cepsDqLogF (D θ : ℝ) (ρW : Measure ℝ) (μ q s : ℂ) : ℂ :=
  cepsA ρW μ q s / cepsD ρW μ q s +
    (cepsSq D θ ρW μ q * s - cepsPq D θ ρW μ q) / cepsQuad D θ ρW μ q s

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- **Pointwise transport.** `∂_μ log F + s ∂_q log F = S_q`. -/
theorem cepsDmuLogF_add {μ q s : ℂ} (hx : (μ, q) ∈ cepsSPRegion D θ ρW)
    (hd : cepsD ρW μ q s ≠ 0) (hQ : cepsQuad D θ ρW μ q s ≠ 0) :
    cepsDmuLogF D θ ρW μ q s + s * cepsDqLogF D θ ρW μ q s = cepsSq D θ ρW μ q := by
  obtain ⟨tS, tP⟩ := cepsRootSum_transport hW hθ hD hx
  have hQ0 := cepsQuad_eq_SP D θ ρW μ q s
  unfold cepsDmuLogF cepsDqLogF cepsSmu cepsPmu cepsSq cepsPq
  rw [tS, tP]
  field_simp
  rw [hQ0]
  ring

theorem hasDerivAt_SP_lines {μ q : ℂ} (hx : (μ, q) ∈ cepsSPRegion D θ ρW) :
    HasDerivAt (fun μ' => cepsRootSum D θ ρW μ' q) (cepsSmu D θ ρW μ q) μ ∧
      HasDerivAt (fun μ' => cepsRootProd D θ ρW μ' q) (cepsPmu D θ ρW μ q) μ ∧
      HasDerivAt (fun q' => cepsRootSum D θ ρW μ q') (cepsSq D θ ρW μ q) q ∧
      HasDerivAt (fun q' => cepsRootProd D θ ρW μ q') (cepsPq D θ ρW μ q) q := by
  have hV := isOpen_cepsSPRegion hW hθ hD
  obtain ⟨hSd, hPd⟩ := differentiableOn_cepsRootSum_joint hW hθ hD
  have hSx := (hSd _ hx).differentiableAt (hV.mem_nhds hx)
  have hPx := (hPd _ hx).differentiableAt (hV.mem_nhds hx)
  have l1 : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableAt ℂ g (μ, q) →
      DifferentiableAt ℂ (fun μ' => g (μ', q)) μ := by
    intro g hg
    exact DifferentiableAt.fun_comp' (g := g) (f := fun μ' : ℂ => ((μ', q) : ℂ × ℂ)) μ hg
      (differentiableAt_id.prodMk (differentiableAt_const _))
  have l2 : ∀ {g : ℂ × ℂ → ℂ}, DifferentiableAt ℂ g (μ, q) →
      DifferentiableAt ℂ (fun q' => g (μ, q')) q := by
    intro g hg
    exact DifferentiableAt.fun_comp' (g := g) (f := fun q' : ℂ => ((μ, q') : ℂ × ℂ)) q hg
      ((differentiableAt_const _).prodMk differentiableAt_id)
  exact ⟨(l1 (g := fun x => cepsRootSum D θ ρW x.1 x.2) hSx).hasDerivAt,
    (l1 (g := fun x => cepsRootProd D θ ρW x.1 x.2) hPx).hasDerivAt,
    (l2 (g := fun x => cepsRootSum D θ ρW x.1 x.2) hSx).hasDerivAt,
    (l2 (g := fun x => cepsRootProd D θ ρW x.1 x.2) hPx).hasDerivAt⟩

/-- `μ ↦ log F(s; μ, q)` has derivative `cepsDmuLogF`. -/
theorem hasDerivAt_logF_mu {γ μ q s : ℂ} (hx : (μ, q) ∈ cepsSPRegion D θ ρW)
    (hd : cepsD ρW μ q s ≠ 0) (hQ : cepsQuad D θ ρW μ q s ≠ 0) (hγs : s ^ 2 - γ ^ 2 ≠ 0)
    (hslit : cepsF D θ ρW γ μ q s ∈ slitPlane) :
    HasDerivAt (fun μ' => Complex.log (cepsF D θ ρW γ μ' q s)) (cepsDmuLogF D θ ρW μ q s) μ := by
  obtain ⟨hS1, hP1, -, -⟩ := hasDerivAt_SP_lines hW hθ hD hx
  have hd1 : HasDerivAt (fun μ' => cepsD ρW μ' q s) (-(cepsA ρW μ q s * s)) μ := by
    have h := ((((hasDerivAt_id μ).mul_const s).cexp).const_mul (cexp (-q))).mul_const
      (stepTransform ρW s)
    have h2 := h.const_sub 1
    unfold cepsD
    refine h2.congr_deriv ?_
    unfold cepsA; simp; ring
  have hQ1 : HasDerivAt (fun μ' => cepsQuad D θ ρW μ' q s)
      (-(cepsSmu D θ ρW μ q * s) + cepsPmu D θ ρW μ q) μ := by
    have h := ((hasDerivAt_const μ (s ^ 2)).sub (hS1.mul_const s)).add hP1
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun μ' => cepsQuad_eq_SP D θ ρW μ' q s
  have hF1 : HasDerivAt (fun μ' => cepsD ρW μ' q s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ' q s)
      ((-(cepsA ρW μ q s * s) * (s ^ 2 - γ ^ 2) * cepsQuad D θ ρW μ q s -
        cepsD ρW μ q s * (s ^ 2 - γ ^ 2) * (-(cepsSmu D θ ρW μ q * s) + cepsPmu D θ ρW μ q)) /
          cepsQuad D θ ρW μ q s ^ 2) μ :=
    (hd1.mul_const (s ^ 2 - γ ^ 2)).div hQ1 hQ
  have e1 : (fun μ' => cepsF D θ ρW γ μ' q s) =
      fun μ' => cepsD ρW μ' q s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ' q s := by
    funext μ'; rfl
  have hlog := (show HasDerivAt (fun μ' => cepsF D θ ρW γ μ' q s) _ μ by rw [e1]; exact hF1).clog
    hslit
  refine hlog.congr_deriv ?_
  have hF : cepsF D θ ρW γ μ q s =
      cepsD ρW μ q s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q s := rfl
  rw [hF]
  unfold cepsDmuLogF
  field_simp
  ring

/-- `q ↦ log F(s; μ, q)` has derivative `cepsDqLogF`. -/
theorem hasDerivAt_logF_q {γ μ q s : ℂ} (hx : (μ, q) ∈ cepsSPRegion D θ ρW)
    (hd : cepsD ρW μ q s ≠ 0) (hQ : cepsQuad D θ ρW μ q s ≠ 0) (hγs : s ^ 2 - γ ^ 2 ≠ 0)
    (hslit : cepsF D θ ρW γ μ q s ∈ slitPlane) :
    HasDerivAt (fun q' => Complex.log (cepsF D θ ρW γ μ q' s)) (cepsDqLogF D θ ρW μ q s) q := by
  obtain ⟨-, -, hS2, hP2⟩ := hasDerivAt_SP_lines hW hθ hD hx
  have hd2 : HasDerivAt (fun q' => cepsD ρW μ q' s) (cepsA ρW μ q s) q := by
    have h := ((((hasDerivAt_id q).neg).cexp).mul_const (cexp (μ * s))).mul_const
      (stepTransform ρW s)
    have h2 := h.const_sub 1
    unfold cepsD
    refine h2.congr_deriv ?_
    unfold cepsA; simp
  have hQ2 : HasDerivAt (fun q' => cepsQuad D θ ρW μ q' s)
      (-(cepsSq D θ ρW μ q * s) + cepsPq D θ ρW μ q) q := by
    have h := ((hasDerivAt_const q (s ^ 2)).sub (hS2.mul_const s)).add hP2
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun q' => cepsQuad_eq_SP D θ ρW μ q' s
  have hF2 : HasDerivAt (fun q' => cepsD ρW μ q' s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q' s)
      ((cepsA ρW μ q s * (s ^ 2 - γ ^ 2) * cepsQuad D θ ρW μ q s -
        cepsD ρW μ q s * (s ^ 2 - γ ^ 2) * (-(cepsSq D θ ρW μ q * s) + cepsPq D θ ρW μ q)) /
          cepsQuad D θ ρW μ q s ^ 2) q :=
    (hd2.mul_const (s ^ 2 - γ ^ 2)).div hQ2 hQ
  have e1 : (fun q' => cepsF D θ ρW γ μ q' s) =
      fun q' => cepsD ρW μ q' s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q' s := by
    funext q'; rfl
  have hlog := (show HasDerivAt (fun q' => cepsF D θ ρW γ μ q' s) _ q by rw [e1]; exact hF2).clog
    hslit
  refine hlog.congr_deriv ?_
  have hF : cepsF D θ ρW γ μ q s =
      cepsD ρW μ q s * (s ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q s := rfl
  rw [hF]
  unfold cepsDqLogF
  field_simp
  ring

end

end PGM
