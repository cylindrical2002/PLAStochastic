import PLAStochastic.Index.CEPS.Central.NodeKernel
import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticNewtonJets
import PLAStochastic.Index.CEPS.Normal.MovingSlopeAnalyticAt

/-! # Fixed-gap Newton iterations from an arbitrary zero-scale root

The finite Newton root model is the fixed-gap Newton iteration started at the principal
base root. Started at any root `β` of the zero-scale quadratic with nonzero gap, the
iteration is jointly analytic, keeps the value `β` at zero scale, and approximates every
analytic exact root through `β` to order `b^(N+1)` after `N` steps. -/

noncomputable section
open Complex Set Filter Topology Asymptotics
namespace PGM

/-- Fixed-gap Newton iteration for `r² P(b r) + λ r = w (1 + b λ)` started at `β`. -/
def cepsCentralNewton (d N : ℕ) (q : Fin d → ℂ) (lam w β : ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => β
  | k + 1 => quadraticNewtonStep (cepsCgfComplexJetPolynomial (cepsComplexJetPad d q) N)
      (cepsCentralNewton d N q lam w β k) lam w
      (lam + cepsComplexJetPad d q (cepsJetCode (.inl 0)) * β)

variable {d N : ℕ}

theorem cepsComplexCumulantRootModel_eq_central (q : Fin d → ℂ) (lam : ℝ) (w sign : ℂ)
    (k : ℕ) : cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w sign k =
      cepsCentralNewton d N q lam w
        (cepsComplexCumulantRootBase (cepsComplexJetPad d q) lam w sign) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cepsComplexCumulantRootModel, cepsCentralNewton, ih]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cepsCentralNewton_analyticAt {e₀ : E} {q : E → Fin d → ℂ} {lam w β b : E → ℂ}
    (hq : AnalyticAt ℂ q e₀) (hlam : AnalyticAt ℂ lam e₀) (hw : AnalyticAt ℂ w e₀)
    (hβ : AnalyticAt ℂ β e₀) (hb : AnalyticAt ℂ b e₀)
    (hgap : lam e₀ + cepsComplexJetPad d (q e₀) (cepsJetCode (.inl 0)) * β e₀ ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun e => cepsCentralNewton d N (q e) (lam e) (w e) (β e) k (b e)) e₀ := by
  have hpi : ∀ i, AnalyticAt ℂ (fun e => cepsComplexJetPad d (q e) i) e₀ :=
    fun i => (cepsComplexJetPad_analyticAt d i _).comp hq
  have hgapA : AnalyticAt ℂ (fun e => lam e +
      cepsComplexJetPad d (q e) (cepsJetCode (.inl 0)) * β e) e₀ :=
    hlam.add ((hpi _).mul hβ)
  induction k with
  | zero => exact hβ
  | succ k ih =>
    have hP := cepsCgfComplexJetPolynomial_analyticAt hpi (hb.mul ih) N
    exact ih.sub (((((ih.pow 2).mul hP).add (hlam.mul ih)).sub
      (hw.mul ((analyticAt_const (v := (1 : ℂ))).add (hb.mul hlam)))).div hgapA hgap)

theorem cepsCentralNewton_zero_of_root {q : Fin d → ℂ} {lam w β : ℂ}
    (hβ : β ^ 2 * (cepsComplexJetPad d q (cepsJetCode (.inl 0)) / 2) + lam * β = w) (k : ℕ) :
    cepsCentralNewton d N q lam w β k 0 = β := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [cepsCentralNewton, quadraticNewtonStep, ih, zero_mul,
      cepsCgfComplexJetPolynomial_zero, add_zero, mul_one, hβ, sub_self, zero_div, sub_zero]

/-- Each fixed-gap Newton step gains one order against an analytic exact root. -/
theorem cepsCentralNewton_isBigO {q : Fin d → ℂ} {lam w β : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = β)
    (he : ∀ᶠ b in 𝓝 (0 : ℂ), f b ^ 2 * cepsCgfComplexJetPolynomial (cepsComplexJetPad d q) N
      (b * f b) + lam * f b = w * (1 + b * lam))
    (hgap : lam + cepsComplexJetPad d q (cepsJetCode (.inl 0)) * β ≠ 0) (k : ℕ) :
    (fun b => f b - cepsCentralNewton d N q lam w β k b) =O[𝓝 0]
      (fun b : ℂ => b ^ (min (k + 1) (N + 1))) := by
  let V := cepsComplexJetPad d q (cepsJetCode (.inl 0))
  let P := cepsCgfComplexJetPolynomial (cepsComplexJetPad d q) N
  have hP0 : P 0 = V / 2 := cepsCgfComplexJetPolynomial_zero _ N
  have hroot : β ^ 2 * (V / 2) + lam * β = w := by
    have h0 := he.self_of_nhds
    simp only [zero_mul, add_zero, mul_one, hf0] at h0
    rw [← hP0]
    exact h0
  have hH : AnalyticAt ℂ P 0 := by
    have hpi : ∀ i, AnalyticAt ℂ (fun _ : ℂ => cepsComplexJetPad d q i) 0 :=
      fun _ => analyticAt_const
    exact cepsCgfComplexJetPolynomial_analyticAt hpi analyticAt_id N
  have hgap' : lam + 2 * f 0 * P 0 = lam + V * β := by
    rw [hf0, hP0]
    ring
  have hunit : (fun s => P s - P s) =O[𝓝 0] (fun s : ℂ => s ^ (N + 1)) := by
    simpa only [sub_self] using isBigO_zero (fun s : ℂ => s ^ (N + 1)) (𝓝 0)
  induction k with
  | zero =>
    have ht := hf.differentiableAt.hasDerivAt.isBigO_sub
    simpa only [cepsCentralNewton, hf0, sub_zero, show min (0 + 1) (N + 1) = 1 by omega,
      pow_one] using! ht
  | succ k ih =>
    have hg : AnalyticAt ℂ (cepsCentralNewton d N q lam w β k) 0 :=
      cepsCentralNewton_analyticAt (q := fun _ : ℂ => q) (lam := fun _ => lam)
        (w := fun _ => w) (β := fun _ => β) (b := id) analyticAt_const analyticAt_const
        analyticAt_const analyticAt_const analyticAt_id hgap k
    have hzero : f 0 = cepsCentralNewton d N q lam w β k 0 := by
      rw [cepsCentralNewton_zero_of_root hroot k, hf0]
    have hslope := cepsNormal_analyticAt_moving_dslope_of_analyticAt hH
      ((analyticAt_id (𝕜 := ℂ)).mul hg) ((analyticAt_id (𝕜 := ℂ)).mul hf)
      (by simp) (by simp)
    have hgap₀ : lam + 2 * f 0 * P 0 ≠ 0 := by rw [hgap']; exact hgap
    have ht := quadraticNewtonStep_improves_order hf hg hH hslope hzero hgap₀ he
      N (min (k + 1) (N + 1)) hunit ih
    rw [hgap'] at ht
    simpa only [cepsCentralNewton,
      show min (min (k + 1) (N + 1) + 1) (N + 1) = min (k + 1 + 1) (N + 1) by omega] using ht

end PGM
