import PLAStochastic.Index.CEPS.Scaled.CgfUnitJets
import PLAStochastic.Index.CEPS.Canonical.LineZones
import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticExpUnit

/-! # The genuine and finite-jet quadratic exponential spatial units -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

def cepsScaledQuadraticEquation (ρW : Measure ℝ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  ξ ^ 2 * cepsCgfUnit ρW (b * ξ) + (lam : ℂ) * ξ - z * (1 + b * lam)

def cepsScaledQuotientSpatialUnit (ρW : Measure ℝ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  quadraticExpUnit b (cepsScaledQuadraticEquation ρW lam z b ξ)

def cepsCumulantQuadraticEquation (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  ξ ^ 2 * cepsCgfJetPolynomial p N (b * ξ) + (lam : ℂ) * ξ - z * (1 + b * lam)

def cepsCumulantQuotientSpatialUnit (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b ξ : ℂ) : ℂ :=
  quadraticExpUnit b (cepsCumulantQuadraticEquation p N lam z b ξ)

theorem cepsCumulantQuotientSpatialUnit_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) (lam : ℝ) (z : ℂ) :
    cepsCumulantQuotientSpatialUnit p N lam z = cepsCumulantQuotientSpatialUnit p' N lam z := by
  funext b ξ
  simp only [cepsCumulantQuotientSpatialUnit, cepsCumulantQuadraticEquation,
    cepsCgfJetPolynomial_congr N hp]

theorem cepsCumulantQuotientSpatialUnit_joint_analyticAt (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z : ℂ) (x : ℂ × ℂ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => cepsCumulantQuotientSpatialUnit p N lam z x.1 x.2) x := by
  have harg : AnalyticAt ℂ (fun x : ℂ × ℂ => x.1 * x.2) x := analyticAt_fst.mul analyticAt_snd
  have hP : AnalyticAt ℂ (fun x : ℂ × ℂ => cepsCgfJetPolynomial p N (x.1 * x.2)) x :=
    ((cepsCgfJetPolynomial_differentiable p N).analyticAt (x.1 * x.2)).comp (f := fun x : ℂ × ℂ => x.1 * x.2) harg
  have hT : AnalyticAt ℂ (fun x : ℂ × ℂ => cepsCumulantQuadraticEquation p N lam z x.1 x.2) x :=
    (((analyticAt_snd.pow 2).mul hP).add (analyticAt_const.mul analyticAt_snd)).sub
      (analyticAt_const.mul (analyticAt_const.add (analyticAt_fst.mul analyticAt_const)))
  have he := (quadraticExpUnit_joint_analyticAt (x.1, cepsCumulantQuadraticEquation p N lam z x.1 x.2)).comp (f := fun x : ℂ × ℂ => (x.1, cepsCumulantQuadraticEquation p N lam z x.1 x.2))
    (analyticAt_fst.prod hT)
  exact he

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsD_scaled_eq_quadraticSpatialUnit (lam : ℝ) (z b ξ : ℂ)
    (hξ : ‖b * ξ‖ < cepsCgfRadius D θ) :
    -cepsD ρW (b * lam) (b ^ 2 * z * (1 + b * lam)) (b * ξ) =
      b ^ 2 * cepsScaledQuotientSpatialUnit ρW lam z b ξ := by
  rw [CepsCanonDomain.cepsD_eq_one_sub_exp hW hθ hD hξ]
  have he : cepsRootEq ρW (b * lam) (b ^ 2 * z * (1 + b * lam)) (b * ξ) =
      b ^ 2 * cepsScaledQuadraticEquation ρW lam z b ξ := by
    unfold cepsRootEq cepsCgfShift cepsScaledQuadraticEquation
    rw [cepsCgf_eq_mul_unit hW hθ hD (mem_ball_zero_iff.mpr hξ)]
    ring
  rw [he, neg_sub]
  exact exp_sub_one_eq_quadraticExpUnit b _

include hW hθ hD in
theorem cepsScaledQuotientSpatialUnit_joint_analyticAt (lam : ℝ) (z : ℂ)
    (x : ℂ × ℂ) (hx : ‖x.1 * x.2‖ < cepsCgfRadius D θ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => cepsScaledQuotientSpatialUnit ρW lam z x.1 x.2) x := by
  have harg : AnalyticAt ℂ (fun x : ℂ × ℂ => x.1 * x.2) x := analyticAt_fst.mul analyticAt_snd
  have hH : AnalyticAt ℂ (fun x : ℂ × ℂ => cepsCgfUnit ρW (x.1 * x.2)) x :=
    ((cepsCgfUnit_differentiableOn hW hθ hD).analyticAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx))).comp (f := fun x : ℂ × ℂ => x.1 * x.2) harg
  have hT : AnalyticAt ℂ (fun x : ℂ × ℂ => cepsScaledQuadraticEquation ρW lam z x.1 x.2) x :=
    (((analyticAt_snd.pow 2).mul hH).add (analyticAt_const.mul analyticAt_snd)).sub
      (analyticAt_const.mul (analyticAt_const.add (analyticAt_fst.mul analyticAt_const)))
  exact (quadraticExpUnit_joint_analyticAt (x.1, cepsScaledQuadraticEquation ρW lam z x.1 x.2)).comp (f := fun x : ℂ × ℂ => (x.1, cepsScaledQuadraticEquation ρW lam z x.1 x.2))
    (analyticAt_fst.prod hT)

end PGM
