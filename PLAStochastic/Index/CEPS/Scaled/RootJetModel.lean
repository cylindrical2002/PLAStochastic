import PLAStochastic.Index.CEPS.Scaled.RootJets
import PLAStochastic.Index.CEPS.Normal.MovingSlopeAnalyticAt
import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticNewtonJets

/-! # An explicit finite cumulant-jet Newton model for the scaled root -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries Asymptotics
open PGM.WienerHopf
namespace PGM

def cepsCumulantRootBase (p : ℕ → ℝ) (lam : ℝ) (z sign : ℂ) : ℂ :=
  let v : ℂ := p (cepsJetCode (.inl 0));
  -(lam : ℂ) / v + sign * Complex.sqrt (2 / v) * Complex.sqrt (z + (lam : ℂ) ^ 2 / (2 * v))

def cepsCumulantRootGap (p : ℕ → ℝ) (lam : ℝ) (z sign : ℂ) : ℂ :=
  (lam : ℂ) + (p (cepsJetCode (.inl 0)) : ℂ) * cepsCumulantRootBase p lam z sign

def cepsCumulantRootModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z sign : ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => cepsCumulantRootBase p lam z sign
  | k + 1 => quadraticNewtonStep (cepsCgfJetPolynomial p N)
      (cepsCumulantRootModel p N lam z sign k) lam z (cepsCumulantRootGap p lam z sign)

theorem cepsCumulantRootModel_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) (lam : ℝ) (z sign : ℂ) (k : ℕ) :
    cepsCumulantRootModel p N lam z sign k = cepsCumulantRootModel p' N lam z sign k := by
  have hv := hp (cepsJetCode (.inl 0)) (cepsJetCode_lt_cepsJetDim (by simp [cepsJetWeight]))
  have hb : cepsCumulantRootBase p lam z sign = cepsCumulantRootBase p' lam z sign := by
    simp only [cepsCumulantRootBase, hv]
  have hg : cepsCumulantRootGap p lam z sign = cepsCumulantRootGap p' lam z sign := by
    simp only [cepsCumulantRootGap, hv, hb]
  induction k with
  | zero => simp only [cepsCumulantRootModel, hb]
  | succ k ih => rw [cepsCumulantRootModel, cepsCumulantRootModel, ih,
      cepsCgfJetPolynomial_congr N hp, hg]

theorem cepsCumulantRootModel_differentiable (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z sign : ℂ) (k : ℕ) :
    Differentiable ℂ (cepsCumulantRootModel p N lam z sign k) := by
  induction k with
  | zero => exact differentiable_const _
  | succ k ih =>
    have hP := (cepsCgfJetPolynomial_differentiable p N).comp (differentiable_id.mul ih)
    unfold cepsCumulantRootModel quadraticNewtonStep
    fun_prop

theorem cepsCumulantRootModel_origin (p : ℕ → ℝ) (N : ℕ) (sign : ℂ) (k : ℕ) :
    cepsCumulantRootModel p N 0 0 sign k = fun _ => 0 := by
  induction k with
  | zero => funext b; simp [cepsCumulantRootModel, cepsCumulantRootBase]
  | succ k ih => funext b; simp [cepsCumulantRootModel, quadraticNewtonStep, ih]

end PGM
