import PLAStochastic.Index.CEPS.Scaled.ComplexJetPair
import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientCompact
import PLAStochastic.Index.CEPS.Normal.DividedDifferenceSymmetry
import PLAStochastic.Index.CEPS.Normal.MovingSlopeGermLocal

/-! # Central finite-jet kernels as explicit symmetric functions of their two nodes

The complete bridge and entrance of the finite Newton model are evaluations of
explicit node kernels at the two Newton roots. The node kernels are symmetric under
exchanging the nodes and are jointly analytic at the merged reference origin. -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

/-- Central base parameters `(q, λ, w, b)`: finite complex input vector, complex drift,
complex frequency and complex scale. -/
abbrev CepsCentralBase (d : ℕ) := (Fin d → ℂ) × ℂ × ℂ × ℂ

def cepsCentralSpatial (d N : ℕ) (x : CepsCentralBase d) (ξ : ℂ) : ℂ :=
  quadraticExpUnit x.2.2.2 (ξ ^ 2 * cepsCgfComplexJetPolynomial (cepsComplexJetPad d x.1) N
    (x.2.2.2 * ξ) + x.2.1 * ξ - x.2.2.1 * (1 + x.2.2.2 * x.2.1))

def cepsCentralQuotient (d N : ℕ) (x : CepsCentralBase d) (a₁ a₂ ξ : ℂ) : ℂ :=
  dslope (dslope (cepsCentralSpatial d N x) a₁) a₂ ξ

def cepsCentralG (d N : ℕ) (x : CepsCentralBase d) (a₁ a₂ ξ : ℂ) : ℂ :=
  exp (-ξ * (1 + x.2.2.2 * x.2.1)) * (cepsCentralQuotient d N x a₁ a₂ ξ *
    exp (-2 * cepsCanonComplexJetPolynomial (cepsComplexJetPad d x.1) N (x.2.2.2 * x.2.1)
      (x.2.2.2 ^ 2 * x.2.2.1 * (1 + x.2.2.2 * x.2.1)) (x.2.2.2 * ξ)))

def cepsCentralDen (d N : ℕ) (x : CepsCentralBase d) (a₁ a₂ : ℂ) : ℂ :=
  dslope (cepsCentralG d N x a₁ a₂) a₂ a₁

def cepsCentralEntranceSlope (d N : ℕ) (x : CepsCentralBase d) (a₁ a₂ : ℂ) : ℂ :=
  dslope (dslope (cepsCentralG d N x a₁ a₂) a₂) a₁ (x.2.2.2 * x.2.2.1)

def cepsCentralBridge (d N : ℕ) (x : CepsCentralBase d) (a₁ a₂ : ℂ) : ℂ :=
  -cepsCentralG d N x a₁ a₂ a₁ * cepsCentralG d N x a₁ a₂ a₂ / cepsCentralDen d N x a₁ a₂

def cepsCentralEntrance (d N : ℕ) (x : CepsCentralBase d) (a₁ a₂ : ℂ) : ℂ :=
  -exp (cepsCanonComplexJetPolynomial (cepsComplexJetPad d x.1) N (x.2.2.2 * x.2.1)
    (x.2.2.2 ^ 2 * x.2.2.1 * (1 + x.2.2.2 * x.2.1)) (x.2.2.2 ^ 2 * x.2.2.1)) *
    cepsCentralEntranceSlope d N x a₁ a₂ /
      (cepsCentralQuotient d N x a₁ a₂ (x.2.2.2 * x.2.2.1) * cepsCentralDen d N x a₁ a₂)

/-! ## The Newton factors are node-kernel evaluations -/

theorem cepsComplexKernelBridgeJetModel_eq_central (d N : ℕ) (q : Fin d → ℂ) (lam : ℝ)
    (w b : ℂ) :
    cepsComplexKernelBridgeJetModel (cepsComplexJetPad d q) N lam w b =
      cepsCentralBridge d N (q, (lam : ℂ), w, b)
        (cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w 1 N b)
        (cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w (-1) N b) := rfl

theorem cepsComplexKernelEntranceJetModel_eq_central (d N : ℕ) (q : Fin d → ℂ) (lam : ℝ)
    (w b : ℂ) :
    cepsComplexKernelEntranceJetModel (cepsComplexJetPad d q) N lam w b =
      cepsCentralEntrance d N (q, (lam : ℂ), w, b)
        (cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w 1 N b)
        (cepsComplexCumulantRootModel (cepsComplexJetPad d q) N lam w (-1) N b) := rfl

/-! ## Node exchange -/

theorem differentiable_dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  have hd := (differentiableOn_dslope (s := univ) (c := c) univ_mem).mpr hf.differentiableOn
  exact fun ξ => (hd ξ (mem_univ ξ)).differentiableAt univ_mem

variable {d N : ℕ}

theorem cepsCentralSpatial_differentiable (x : CepsCentralBase d) :
    Differentiable ℂ (cepsCentralSpatial d N x) := by
  intro ξ
  have hpi : ∀ i, AnalyticAt ℂ (fun _ : ℂ => cepsComplexJetPad d x.1 i) ξ :=
    fun _ => analyticAt_const
  have hP := cepsCgfComplexJetPolynomial_analyticAt hpi
    ((analyticAt_const (v := x.2.2.2)).mul (analyticAt_id (z := ξ))) N
  have hT : AnalyticAt ℂ (fun t : ℂ => t ^ 2 * cepsCgfComplexJetPolynomial
      (cepsComplexJetPad d x.1) N (x.2.2.2 * t) + x.2.1 * t -
        x.2.2.1 * (1 + x.2.2.2 * x.2.1)) ξ :=
    (((analyticAt_id.pow 2).mul hP).add (analyticAt_const.mul analyticAt_id)).sub analyticAt_const
  exact ((quadraticExpUnit_joint_analyticAt (x.2.2.2, _)).comp (x := ξ)
    (f := fun t : ℂ => (x.2.2.2, t ^ 2 * cepsCgfComplexJetPolynomial
      (cepsComplexJetPad d x.1) N (x.2.2.2 * t) + x.2.1 * t -
        x.2.2.1 * (1 + x.2.2.2 * x.2.1))) (analyticAt_const.prod hT)).differentiableAt

theorem cepsCentralQuotient_differentiable (x : CepsCentralBase d) (a₁ a₂ : ℂ) :
    Differentiable ℂ (cepsCentralQuotient d N x a₁ a₂) :=
  differentiable_dslope_entire (differentiable_dslope_entire
    (cepsCentralSpatial_differentiable x) a₁) a₂

theorem cepsCentralG_differentiable (x : CepsCentralBase d) (a₁ a₂ : ℂ) :
    Differentiable ℂ (cepsCentralG d N x a₁ a₂) := by
  intro ξ
  have hpi : ∀ i, AnalyticAt ℂ (fun _ : ℂ => cepsComplexJetPad d x.1 i) ξ :=
    fun _ => analyticAt_const
  have hC := cepsCanonComplexJetPolynomial_analyticAt hpi
    (analyticAt_const (v := x.2.2.2 * x.2.1))
    (analyticAt_const (v := x.2.2.2 ^ 2 * x.2.2.1 * (1 + x.2.2.2 * x.2.1)))
    ((analyticAt_const (v := x.2.2.2)).mul (analyticAt_id (z := ξ))) N
  have hQ := ((cepsCentralQuotient_differentiable (N := N) x a₁ a₂).analyticAt ξ)
  have hA : AnalyticAt ℂ (fun t : ℂ => exp (-t * (1 + x.2.2.2 * x.2.1)) *
      (cepsCentralQuotient d N x a₁ a₂ t *
        exp (-2 * cepsCanonComplexJetPolynomial (cepsComplexJetPad d x.1) N (x.2.2.2 * x.2.1)
          (x.2.2.2 ^ 2 * x.2.2.1 * (1 + x.2.2.2 * x.2.1)) (x.2.2.2 * t)))) ξ :=
    ((analyticAt_id.neg.mul analyticAt_const).cexp).mul
      (hQ.mul ((analyticAt_const.mul hC).cexp))
  exact hA.differentiableAt

theorem cepsCentralQuotient_swap (x : CepsCentralBase d) (a₁ a₂ ξ : ℂ) :
    cepsCentralQuotient d N x a₁ a₂ ξ = cepsCentralQuotient d N x a₂ a₁ ξ :=
  cepsNormal_second_dslope_swap ((cepsCentralSpatial_differentiable x) a₂)
    ((cepsCentralSpatial_differentiable x) a₁) ξ

theorem cepsCentralG_swap (x : CepsCentralBase d) (a₁ a₂ : ℂ) :
    cepsCentralG d N x a₁ a₂ = cepsCentralG d N x a₂ a₁ := by
  funext ξ
  simp only [cepsCentralG, cepsCentralQuotient_swap x a₁ a₂ ξ]

theorem cepsCentralDen_swap (x : CepsCentralBase d) (a₁ a₂ : ℂ) :
    cepsCentralDen d N x a₁ a₂ = cepsCentralDen d N x a₂ a₁ := by
  rw [cepsCentralDen, cepsCentralDen, cepsCentralG_swap x a₁ a₂, cepsNormal_dslope_swap]

theorem cepsCentralEntranceSlope_swap (x : CepsCentralBase d) (a₁ a₂ : ℂ) :
    cepsCentralEntranceSlope d N x a₁ a₂ = cepsCentralEntranceSlope d N x a₂ a₁ := by
  rw [cepsCentralEntranceSlope, cepsCentralEntranceSlope, cepsCentralG_swap x a₁ a₂]
  exact cepsNormal_second_dslope_swap ((cepsCentralG_differentiable x a₂ a₁) a₁)
    ((cepsCentralG_differentiable x a₂ a₁) a₂) _

theorem cepsCentralBridge_swap (x : CepsCentralBase d) (a₁ a₂ : ℂ) :
    cepsCentralBridge d N x a₁ a₂ = cepsCentralBridge d N x a₂ a₁ := by
  rw [cepsCentralBridge, cepsCentralBridge, cepsCentralG_swap x a₁ a₂, cepsCentralDen_swap x a₁ a₂]
  ring

theorem cepsCentralEntrance_swap (x : CepsCentralBase d) (a₁ a₂ : ℂ) :
    cepsCentralEntrance d N x a₁ a₂ = cepsCentralEntrance d N x a₂ a₁ := by
  rw [cepsCentralEntrance, cepsCentralEntrance, cepsCentralEntranceSlope_swap x a₁ a₂,
    cepsCentralQuotient_swap x a₁ a₂, cepsCentralDen_swap x a₁ a₂]

end PGM
