import PLAStochastic.Index.CEPS.Central.NodeKernelGerm
import PLAStochastic.Index.CEPS.Scaled.ComplexJetMorseKernelGerm
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricEvenSqrtDescent

/-! # Morse substitution and square-coordinate descent of symmetric node kernels

Substituting the two signed Morse roots and the Morse frequency into a node-symmetric
kernel gives an even function of the signed Morse coordinate `s`. Its descent to the
square coordinate, followed by the Morse square relation
`s² = z (1 + b λ) - λ² U(q, b λ)`, is jointly analytic in `(q, λ, z, b)` at the merged
reference origin. -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

variable {d N : ℕ}

/-- The node-kernel parameters at a signed Morse point `u = (((q, λ), b), s)`. -/
def cepsCentralMorsePoint (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ) (u : CepsComplexJetMorseParam d × ℂ) :
    CepsCentralBase d × ℂ × ℂ :=
  ((u.1.1.1, u.1.1.2, cepsComplexJetMorseFrequency d N η u, u.1.2),
    cepsComplexJetMorseNode d Θ 1 u, cepsComplexJetMorseNode d Θ (-1) u)

/-- A node kernel evaluated at the signed Morse point. -/
def cepsCentralMorseEval (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ) (F : CepsCentralBase d → ℂ → ℂ → ℂ)
    (u : CepsComplexJetMorseParam d × ℂ) : ℂ :=
  F (cepsCentralMorsePoint d N η Θ u).1 (cepsCentralMorsePoint d N η Θ u).2.1
    (cepsCentralMorsePoint d N η Θ u).2.2

/-- The descended node kernel in the original parameters `(q, λ, z, b)`. -/
def cepsCentralDescended (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ) (F : CepsCentralBase d → ℂ → ℂ → ℂ)
    (x : CepsCentralBase d) : ℂ :=
  cepsCentralMorseEval d N η Θ F (((x.1, x.2.1), x.2.2.2),
    Complex.sqrt (cepsComplexJetMorseSquare d N η x.1 x.2.1 x.2.2.1 x.2.2.2))

theorem cepsComplexJetMorseFrequency_neg (η : (Fin d → ℂ) × ℂ → ℂ)
    (e : CepsComplexJetMorseParam d) (s : ℂ) :
    cepsComplexJetMorseFrequency d N η (e, -s) = cepsComplexJetMorseFrequency d N η (e, s) := by
  simp only [cepsComplexJetMorseFrequency, cepsComplexJetMorseEnergy, even_two, Even.neg_pow]

theorem cepsComplexJetMorseNode_neg (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ)
    (e : CepsComplexJetMorseParam d) (s sgn : ℂ) :
    cepsComplexJetMorseNode d Θ sgn (e, -s) = cepsComplexJetMorseNode d Θ (-sgn) (e, s) := by
  simp only [cepsComplexJetMorseNode, mul_neg, neg_mul]

theorem cepsCentralMorseEval_neg (η : (Fin d → ℂ) × ℂ → ℂ)
    (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ) {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    (hF : ∀ x a₁ a₂, F x a₁ a₂ = F x a₂ a₁) (e : CepsComplexJetMorseParam d) (s : ℂ) :
    cepsCentralMorseEval d N η Θ F (e, -s) = cepsCentralMorseEval d N η Θ F (e, s) := by
  simp only [cepsCentralMorseEval, cepsCentralMorsePoint, cepsComplexJetMorseFrequency_neg,
    cepsComplexJetMorseNode_neg, neg_neg]
  exact hF _ _ _

/-- With any square root of the Morse square, the descended kernel is the signed Morse
evaluation. -/
theorem cepsCentralDescended_eq_of_sq (η : (Fin d → ℂ) × ℂ → ℂ)
    (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ) {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    (hF : ∀ x a₁ a₂, F x a₁ a₂ = F x a₂ a₁) (x : CepsCentralBase d) {s : ℂ}
    (hs : s ^ 2 = cepsComplexJetMorseSquare d N η x.1 x.2.1 x.2.2.1 x.2.2.2) :
    cepsCentralDescended d N η Θ F x = cepsCentralMorseEval d N η Θ F (((x.1, x.2.1), x.2.2.2), s) := by
  have h : Complex.sqrt (cepsComplexJetMorseSquare d N η x.1 x.2.1 x.2.2.1 x.2.2.2) ^ 2 = s ^ 2 := by
    rw [sqrt_sq_eq, hs]
  rw [cepsCentralDescended]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
  · rw [h']
  · rw [h', cepsCentralMorseEval_neg η Θ hF]

/-- The Morse frequency recovers the original frequency on the Morse square relation. -/
theorem cepsComplexJetMorseFrequency_of_sq (η : (Fin d → ℂ) × ℂ → ℂ)
    (x : CepsCentralBase d) {s : ℂ}
    (hs : s ^ 2 = cepsComplexJetMorseSquare d N η x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hw : 1 + x.2.2.2 * x.2.1 ≠ 0) :
    cepsComplexJetMorseFrequency d N η (((x.1, x.2.1), x.2.2.2), s) = x.2.2.1 := by
  rw [cepsComplexJetMorseFrequency, cepsComplexJetMorseEnergy, div_eq_iff hw]
  simp only
  rw [hs, cepsComplexJetMorseSquare]
  ring

theorem cepsCentralMorsePoint_analyticAt {η : (Fin d → ℂ) × ℂ → ℂ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0)) :
    AnalyticAt ℂ (cepsCentralMorsePoint d N η Θ) (((p₀, 0), 0), 0) := by
  have hp : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.1.1) (((p₀, 0), 0), 0) :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have hl : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.1.2) (((p₀, 0), 0), 0) :=
    analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)
  have hb : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.2) (((p₀, 0), 0), 0) :=
    analyticAt_snd.comp analyticAt_fst
  have hz := cepsComplexJetMorseFrequency_analyticAt (N := N) hη
  have h₁ := cepsComplexJetMorseNode_analyticAt hΘ 1
  have h₂ := cepsComplexJetMorseNode_analyticAt hΘ (-1)
  exact (hp.prod (hl.prod (hz.prod hb))).prod (h₁.prod h₂)

theorem cepsCentralMorsePoint_origin {η : (Fin d → ℂ) × ℂ → ℂ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ} (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0)) :
    cepsCentralMorsePoint d N η Θ (((p₀, 0), 0), 0) = ((p₀, 0, 0, 0), 0, 0) := by
  simp only [cepsCentralMorsePoint, cepsComplexJetMorseNode_zero hΘ,
    cepsComplexJetMorseFrequency, cepsComplexJetMorseEnergy]
  simp

theorem cepsCentralMorseEval_analyticAt {η : (Fin d → ℂ) × ℂ → ℂ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ} {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0))
    (hF : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => F X.1 X.2.1 X.2.2)
      ((p₀, 0, 0, 0), 0, 0)) :
    AnalyticAt ℂ (cepsCentralMorseEval d N η Θ F) (((p₀, 0), 0), 0) := by
  have h := hF.comp_of_eq (cepsCentralMorsePoint_analyticAt (N := N) hη hΘ)
    (cepsCentralMorsePoint_origin hΘ)
  simp only [Function.comp_def] at h
  exact h

theorem cepsComplexJetMorseSquare_origin {η : (Fin d → ℂ) × ℂ → ℂ} (p₀ : Fin d → ℂ) :
    cepsComplexJetMorseSquare d N η p₀ 0 0 0 = 0 := by
  simp [cepsComplexJetMorseSquare]

/-- The descended node kernel is jointly analytic at the merged reference origin. -/
theorem cepsCentralDescended_analyticAt {η : (Fin d → ℂ) × ℂ → ℂ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ} {F : CepsCentralBase d → ℂ → ℂ → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0))
    (hF : AnalyticAt ℂ (fun X : CepsCentralBase d × ℂ × ℂ => F X.1 X.2.1 X.2.2)
      ((p₀, 0, 0, 0), 0, 0))
    (hsym : ∀ x a₁ a₂, F x a₁ a₂ = F x a₂ a₁) :
    AnalyticAt ℂ (cepsCentralDescended d N η Θ F) (p₀, 0, 0, 0) := by
  have hg := cepsCentralMorseEval_analyticAt (N := N) hη hΘ hF
  have heven : ∀ᶠ u in 𝓝 ((((p₀, 0), 0) : CepsComplexJetMorseParam d), (0 : ℂ)),
      cepsCentralMorseEval d N η Θ F (u.1, -u.2) = cepsCentralMorseEval d N η Θ F u :=
    Eventually.of_forall fun u => cepsCentralMorseEval_neg η Θ hsym u.1 u.2
  have hD := analyticAt_parametric_even_sqrt hg heven
  have hSq := cepsComplexJetMorseSquare_analyticAt (N := N) hη 0 0
  have hm : AnalyticAt ℂ (fun x : CepsCentralBase d => (((x.1, x.2.1), x.2.2.1), x.2.2.2))
      (p₀, 0, 0, 0) :=
    ((analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)).prod
      (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd))).prod
      (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd))
  have hSq' := hSq.comp_of_eq hm rfl
  simp only [Function.comp_def] at hSq'
  have he : AnalyticAt ℂ (fun x : CepsCentralBase d => ((x.1, x.2.1), x.2.2.2)) (p₀, 0, 0, 0) :=
    (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)).prod
      (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd))
  have h0 : (fun x : CepsCentralBase d => (((x.1, x.2.1), x.2.2.2),
      cepsComplexJetMorseSquare d N η x.1 x.2.1 x.2.2.1 x.2.2.2)) (p₀, 0, 0, 0) =
      ((((p₀, 0), 0) : CepsComplexJetMorseParam d), (0 : ℂ)) := by
    simp only [cepsComplexJetMorseSquare_origin]
  have h := hD.comp_of_eq (he.prod hSq') h0
  simp only [Function.comp_def] at h
  exact h

end PGM
