import PLAStochastic.Index.CEPS.Scaled.CanonJetApprox
import PLAStochastic.Index.CEPS.Scaled.RootJetApprox
import PLAStochastic.ForMathlib.Analysis.Complex.AnalyticJetComposition

/-! # Exact canonical curve coefficients from the finite X8 mixed-jet model -/

noncomputable section
open Complex Set Metric MeasureTheory Finset Filter Topology Asymptotics PowerSeries
open PGM.WienerHopf
namespace PGM

theorem cepsCanonJetPolynomial_curve_analyticAt (p : ℕ → ℝ) (N : ℕ)
    {μ q ζ : ℂ → ℂ} (hμ : AnalyticAt ℂ μ 0) (hq : AnalyticAt ℂ q 0)
    (hζ : AnalyticAt ℂ ζ 0) :
    AnalyticAt ℂ (fun b => cepsCanonJetPolynomial p N (μ b) (q b) (ζ b)) 0 := by
  unfold cepsCanonJetPolynomial
  fun_prop

theorem cepsCanonJetPolynomial_joint_analyticAt (p : ℕ → ℝ) (N : ℕ) (x : ℂ × (ℂ × ℂ)) :
    AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => cepsCanonJetPolynomial p N x.1 x.2.1 x.2.2) x := by
  unfold cepsCanonJetPolynomial
  have h1 : AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => x.1) x := analyticAt_fst
  have h2 : AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => x.2.1) x :=
    analyticAt_fst.comp analyticAt_snd
  have h3 : AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => x.2.2) x :=
    analyticAt_snd.comp analyticAt_snd
  exact Finset.analyticAt_fun_sum _ fun j _ => (analyticAt_const.mul (h1.pow j)).mul
    (Finset.analyticAt_fun_sum _ fun m _ => (analyticAt_const.mul (h3.pow m)).mul
      (Finset.analyticAt_fun_sum _ fun n _ => (analyticAt_const.mul (h2.pow n)).mul analyticAt_const))

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsCanonDriftTaylor_taylorJets_eq_jetPolynomial :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ {μ q ζ : ℂ → ℂ},
      AnalyticAt ℂ μ 0 → AnalyticAt ℂ q 0 → AnalyticAt ℂ ζ 0 → q 0 = 0 → ζ 0 = 0 →
      ∀ j ≤ N, coeff j (complexTaylorSeries
        (fun b => cepsCanonDriftTaylor dom ρW N (μ b) (q b) (ζ b)) 0) =
        coeff j (complexTaylorSeries
          (fun b => cepsCanonJetPolynomial (cepsJet f) N (μ b) (q b) (ζ b)) 0) := by
  obtain ⟨r, hr, he⟩ := cepsCanonDriftRectTaylor_eq_jetPolynomial dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN μ q ζ hμ hq hζ hq0 hζ0
  have hqo : q =O[𝓝 (0 : ℂ)] fun b => b := by
    simpa only [hq0, sub_zero] using hq.differentiableAt.hasDerivAt.isBigO_sub
  have hζo : ζ =O[𝓝 (0 : ℂ)] fun b => b := by
    simpa only [hζ0, sub_zero] using hζ.differentiableAt.hasDerivAt.isBigO_sub
  have herr := cepsCanonDriftTaylor_rect_curve_isBigO dom hW hθ hD hfS hηc
    le_rfl N (by omega) hμ.continuousAt
    (by simpa only [hq0] using hq.continuousAt.tendsto)
    (by simpa only [hζ0] using hζ.continuousAt.tendsto) hqo hζo
  rw [he hW hfW hneg hη hf hclose N hN] at herr
  exact complexTaylorSeries_coeff_eq_of_isBigO
    (cepsCanonDriftTaylor_curve_analyticAt dom hW hθ hD hfS hηc N (by omega)
      hμ hq hζ hq0 hζ0)
    (cepsCanonJetPolynomial_curve_analyticAt (cepsJet f) N hμ hq hζ) N herr

variable {ρW : Measure ℝ} {fW f : ℝ → ℝ} (hW : IsStepLaw ρW fW D θ v)

include dom hW hθ hD in
theorem cepsCumulantRootModel_actual_isBigO_all (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    (fun b => cepsScaledSignedRoot D θ ρW lam z sign b -
      cepsCumulantRootModel (cepsJet f) N lam z sign N b) =O[𝓝 0]
        (fun b : ℂ => b ^ (N + 1)) := by
  by_cases hne : lam ≠ 0 ∨ z ≠ 0
  · simpa only [min_self] using
      cepsCumulantRootModel_actual_isBigO dom hW hθ hD hfW N lam hz hsign hne N
  · have hlam : lam = 0 := not_ne_iff.mp (fun h => hne (Or.inl h))
    have hz0 : z = 0 := not_ne_iff.mp (fun h => hne (Or.inr h))
    subst lam; subst z
    rw [cepsScaledSignedRoot_zero_origin hW hθ hD, cepsCumulantRootModel_origin]
    simpa only [sub_self] using (isBigO_zero (E' := ℂ)
      (fun b : ℂ => b ^ (N + 1)) (𝓝 0))

include dom hW hθ hD in
theorem cepsCanonJetPolynomial_rootModel_taylorJets (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => cepsCanonJetPolynomial (cepsJet f) N
      (b * lam) (cepsComplexScaledDiscount lam z b)
        (b * cepsScaledSignedRoot D θ ρW lam z sign b)) 0) =
      coeff j (complexTaylorSeries (fun b => cepsCanonJetPolynomial (cepsJet f) N
        (b * lam) (cepsComplexScaledDiscount lam z b)
          (b * cepsCumulantRootModel (cepsJet f) N lam z sign N b)) 0) := by
  let a : ℂ → ℂ × (ℂ × ℂ) := fun b =>
    (b * lam, (cepsComplexScaledDiscount lam z b,
      b * cepsScaledSignedRoot D θ ρW lam z sign b))
  let c : ℂ → ℂ × (ℂ × ℂ) := fun b =>
    (b * lam, (cepsComplexScaledDiscount lam z b,
      b * cepsCumulantRootModel (cepsJet f) N lam z sign N b))
  have hr := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
  have hc := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z sign N).analyticAt 0
  have ha : AnalyticAt ℂ a 0 := by
    dsimp [a]; unfold cepsComplexScaledDiscount; fun_prop
  have hca : AnalyticAt ℂ c 0 := by
    dsimp [c]; unfold cepsComplexScaledDiscount; fun_prop
  have hzeroa : a 0 = 0 := by simp [a, cepsComplexScaledDiscount]
  have hzeroc : c 0 = 0 := by simp [c, cepsComplexScaledDiscount]
  have he := cepsCumulantRootModel_actual_isBigO_all dom hθ hD hW hfW N lam hz hsign
  have hb : (fun b : ℂ => b) =O[𝓝 0] (fun _ => (1 : ℂ)) :=
    (continuousAt_id (x := (0 : ℂ))).tendsto.isBigO_one ℂ
  have hlast : (fun b => b * cepsScaledSignedRoot D θ ρW lam z sign b -
      b * cepsCumulantRootModel (cepsJet f) N lam z sign N b)
      =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    simpa only [one_mul, mul_sub] using hb.mul he
  have hzerr : (fun _ : ℂ => (0 : ℂ)) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) :=
    isBigO_zero _ _
  have hdiff : (fun b => a b - c b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    simpa only [a, c, Prod.mk_sub_mk, sub_self] using hzerr.prod_left (hzerr.prod_left hlast)
  exact complexTaylorSeries_coeff_eq_of_analytic_composition
    (cepsCanonJetPolynomial_joint_analyticAt (cepsJet f) N 0) ha hca hzeroa hzeroc N hdiff

end PGM
