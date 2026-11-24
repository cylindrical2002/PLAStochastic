import PLAStochastic.Index.CEPS.Scaled.ComplexJetPolynomial
import PLAStochastic.Index.CEPS.Scaled.RootModelFrequency

/-! # Complex finite jet roots and genuine joint parameter analyticity -/

noncomputable section
open Complex
namespace PGM

def cepsComplexCumulantRootBase (p : ℕ → ℂ) (lam : ℝ) (z sign : ℂ) : ℂ :=
  let v := p (cepsJetCode (.inl 0));
  -(lam : ℂ) / v + sign * sqrt (2 / v) * sqrt (z + (lam : ℂ) ^ 2 / (2 * v))

def cepsComplexCumulantRootGap (p : ℕ → ℂ) (lam : ℝ) (z sign : ℂ) : ℂ :=
  (lam : ℂ) + p (cepsJetCode (.inl 0)) * cepsComplexCumulantRootBase p lam z sign

def cepsComplexCumulantRootModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z sign : ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => cepsComplexCumulantRootBase p lam z sign
  | k + 1 => quadraticNewtonStep (cepsCgfComplexJetPolynomial p N)
      (cepsComplexCumulantRootModel p N lam z sign k) lam z (cepsComplexCumulantRootGap p lam z sign)

theorem cepsComplexCumulantRootBase_real (p : ℕ → ℝ) (lam : ℝ) (z sign : ℂ) :
    cepsComplexCumulantRootBase (fun i => (p i : ℂ)) lam z sign =
      cepsCumulantRootBase p lam z sign := rfl

theorem cepsComplexCumulantRootGap_real (p : ℕ → ℝ) (lam : ℝ) (z sign : ℂ) :
    cepsComplexCumulantRootGap (fun i => (p i : ℂ)) lam z sign =
      cepsCumulantRootGap p lam z sign := rfl

theorem cepsComplexCumulantRootModel_real (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z sign : ℂ)
    (k : ℕ) : cepsComplexCumulantRootModel (fun i => (p i : ℂ)) N lam z sign k =
      cepsCumulantRootModel p N lam z sign k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [cepsComplexCumulantRootModel, cepsCumulantRootModel,
      cepsCgfComplexJetPolynomial_real, cepsComplexCumulantRootGap_real, ih]

/-- The complex roots are analytic in every input coordinate, scale, and frequency along
any jointly analytic parameterization inside the genuine square-root charts. -/
theorem cepsComplexCumulantRootModel_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {x : E} {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x) (hb : AnalyticAt ℂ b x)
    (hz : AnalyticAt ℂ z x) (N : ℕ) (lam : ℝ) (sign : ℂ)
    (hv : p x (cepsJetCode (.inl 0)) ≠ 0)
    (hsv : 2 / p x (cepsJetCode (.inl 0)) ∈ slitPlane)
    (hsz : z x + (lam : ℂ) ^ 2 / (2 * p x (cepsJetCode (.inl 0))) ∈ slitPlane)
    (hgap : cepsComplexCumulantRootGap (p x) lam (z x) sign ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun x => cepsComplexCumulantRootModel (p x) N lam (z x) sign k (b x)) x := by
  have hvA := hp (cepsJetCode (.inl 0))
  have hratio : AnalyticAt ℂ (fun x => 2 / p x (cepsJetCode (.inl 0))) x :=
    analyticAt_const.div hvA hv
  have hs1 := (differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hsv)).comp
    (x := x) (f := fun x => 2 / p x (cepsJetCode (.inl 0))) hratio
  have hrad : AnalyticAt ℂ (fun x => z x + (lam : ℂ) ^ 2 /
      (2 * p x (cepsJetCode (.inl 0)))) x :=
    hz.add (analyticAt_const.div (analyticAt_const.mul hvA) (mul_ne_zero (by norm_num) hv))
  have hs2 := (differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hsz)).comp
    (x := x) (f := fun x => z x + (lam : ℂ) ^ 2 / (2 * p x (cepsJetCode (.inl 0)))) hrad
  have hbase : AnalyticAt ℂ (fun x => cepsComplexCumulantRootBase (p x) lam (z x) sign) x :=
    (analyticAt_const.div hvA hv).add ((analyticAt_const.mul hs1).mul hs2)
  have hgapA : AnalyticAt ℂ (fun x => cepsComplexCumulantRootGap (p x) lam (z x) sign) x :=
    analyticAt_const.add (hvA.mul hbase)
  induction k with
  | zero => exact hbase
  | succ k ih =>
    have hP := cepsCgfComplexJetPolynomial_analyticAt hp (hb.mul ih) N
    exact ih.sub (((((ih.pow 2).mul hP).add (analyticAt_const.mul ih)).sub
      (hz.mul (analyticAt_const.add (hb.mul analyticAt_const)))).div hgapA hgap)

end PGM
