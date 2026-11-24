import PLAStochastic.Index.CEPS.Scaled.KernelSpatialFrequency
import PLAStochastic.Index.CEPS.Scaled.KernelFiniteFactors
import PLAStochastic.ForMathlib.Analysis.Complex.PolydiscGerms

/-! # Common genuine frequency neighborhoods for finite bridge and entrance models -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem cepsKernelFiniteSlopes_frequency_neighborhood (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelDenominatorJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelEntranceSlopeJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelGJetModel p N lam x.2 x.1
        (cepsCumulantRootModel p N lam x.2 1 N x.1)) (ball 0 B ×ˢ ball z B) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelGJetModel p N lam x.2 x.1
        (cepsCumulantRootModel p N lam x.2 (-1) N x.1)) (ball 0 B ×ˢ ball z B) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCumulantJetQuotient p N lam x.2 x.1 (x.1 * x.2))
        (ball 0 B ×ˢ ball z B) := by
  let a : ℂ × ℂ → ℂ := fun x => cepsCumulantRootModel p N lam x.2 1 N x.1
  let d : ℂ × ℂ → ℂ := fun x => cepsCumulantRootModel p N lam x.2 (-1) N x.1
  let t : ℂ × ℂ → ℂ := fun x => x.1 * x.2
  have ha : AnalyticAt ℂ a (0, z) := cepsCumulantRootModel_joint_frequency_analyticAt p hp N lam hz hne (by norm_num) 0 N
  have hd : AnalyticAt ℂ d (0, z) := cepsCumulantRootModel_joint_frequency_analyticAt p hp N lam hz hne (by norm_num) 0 N
  have ht : AnalyticAt ℂ t (0, z) := analyticAt_fst.mul analyticAt_snd
  let R : ℝ := 1 + ‖a (0, z)‖ + ‖d (0, z)‖
  have hR : 0 < R := by dsimp [R]; positivity
  have ha0 : a (0, z) ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (d (0, z))]
  have hd0 : d (0, z) ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a (0, z))]
  have ht0 : t (0, z) ∈ ball (0 : ℂ) R := by simpa [t] using (mem_ball_self hR : (0 : ℂ) ∈ ball 0 R)
  obtain ⟨BG, hBG, hG⟩ := cepsKernelGJetModel_frequency_family p hp N lam hz hne hR
  obtain ⟨BQ, hBQ, hQ⟩ := cepsCumulantJetQuotient_frequency_family p hp N lam hz hne hR
  have hev : ∀ᶠ x in 𝓝 ((0, z) : ℂ × ℂ), AnalyticAt ℂ a x ∧ AnalyticAt ℂ d x ∧
      a x ∈ ball 0 R ∧ d x ∈ ball 0 R ∧ t x ∈ ball 0 R :=
    ha.eventually_analyticAt.and (hd.eventually_analyticAt.and
      ((ha.continuousAt.eventually (isOpen_ball.mem_nhds ha0)).and
        ((hd.continuousAt.eventually (isOpen_ball.mem_nhds hd0)).and
          (ht.continuousAt.eventually (isOpen_ball.mem_nhds ht0)))))
  obtain ⟨B, hB, hBB, hball⟩ := exists_polydisc_of_eventually_le (lt_min hBG hBQ) hev
  have hda : DifferentiableOn ℂ a (ball 0 B ×ˢ ball z B) :=
    fun x hx => (hball x hx).1.differentiableAt.differentiableWithinAt
  have hdd : DifferentiableOn ℂ d (ball 0 B ×ˢ ball z B) :=
    fun x hx => (hball x hx).2.1.differentiableAt.differentiableWithinAt
  have hdt : DifferentiableOn ℂ t (ball 0 B ×ˢ ball z B) := by dsimp [t]; fun_prop
  have hma : MapsTo a (ball 0 B ×ˢ ball z B) (ball 0 R) := fun x hx => (hball x hx).2.2.1
  have hmd : MapsTo d (ball 0 B ×ˢ ball z B) (ball 0 R) := fun x hx => (hball x hx).2.2.2.1
  have hmt : MapsTo t (ball 0 B ×ˢ ball z B) (ball 0 R) := fun x hx => (hball x hx).2.2.2.2
  have hGB := hG.mono (ball_subset_ball (hBB.trans (min_le_left _ _)))
    (ball_subset_ball (hBB.trans (min_le_left _ _))) le_rfl
  have hQB := hQ.mono (ball_subset_ball (hBB.trans (min_le_right _ _)))
    (ball_subset_ball (hBB.trans (min_le_right _ _))) le_rfl
  have hS := hGB.dslope isOpen_ball isOpen_ball hdd hmd
  exact ⟨B, hB, hS.eval isOpen_ball isOpen_ball hda hma,
    (hS.dslope isOpen_ball isOpen_ball hda hma).eval isOpen_ball isOpen_ball hdt hmt,
    hGB.eval isOpen_ball isOpen_ball hda hma,
    hGB.eval isOpen_ball isOpen_ball hdd hmd,
    hQB.eval isOpen_ball isOpen_ball hdt hmt⟩

theorem cepsMarkedCanonJetPolynomial_frequency_analyticAt (p : ℕ → ℝ)
    (N : ℕ) (lam : ℝ) (x : ℂ × ℂ) :
    AnalyticAt ℂ (fun x : ℂ × ℂ => exp (cepsCanonJetPolynomial p N (x.1 * lam)
      (cepsComplexScaledDiscount lam x.2 x.1) (x.1 ^ 2 * x.2))) x := by
  have hb : AnalyticAt ℂ (fun x : ℂ × ℂ => x.1) x := analyticAt_fst
  have hz : AnalyticAt ℂ (fun x : ℂ × ℂ => x.2) x := analyticAt_snd
  have hcurve : AnalyticAt ℂ (fun x : ℂ × ℂ => (x.1 * (lam : ℂ),
      (cepsComplexScaledDiscount lam x.2 x.1, x.1 ^ 2 * x.2))) x :=
    (hb.mul analyticAt_const).prod ((((hb.pow 2).mul hz).mul
      (analyticAt_const.add (hb.mul analyticAt_const))).prod ((hb.pow 2).mul hz))
  exact ((cepsCanonJetPolynomial_joint_analyticAt p N
    (x.1 * lam, (cepsComplexScaledDiscount lam x.2 x.1, x.1 ^ 2 * x.2))).comp
      (x := x) (f := fun x : ℂ × ℂ => (x.1 * (lam : ℂ),
        (cepsComplexScaledDiscount lam x.2 x.1, x.1 ^ 2 * x.2))) hcurve).cexp

theorem cepsKernelFiniteFactors_frequency_neighborhood (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0)
    (hDen0 : cepsKernelDenominatorJetModel p N lam z 0 ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelBridgeJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelEntranceJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) := by
  obtain ⟨C, hC, hDen, hS, hGP, hGM, hQ⟩ := cepsKernelFiniteSlopes_frequency_neighborhood p hp N lam hz hne
  have hU : IsOpen (ball (0 : ℂ) C ×ˢ ball z C) := isOpen_ball.prod isOpen_ball
  have hx : ((0, z) : ℂ × ℂ) ∈ ball (0 : ℂ) C ×ˢ ball z C := ⟨mem_ball_self hC, mem_ball_self hC⟩
  have hQ0 : cepsCumulantJetQuotient p N lam z 0 (0 * z) ≠ 0 := by
    rw [cepsCumulantJetQuotient_zero]
    exact div_ne_zero (by exact_mod_cast hp.ne') (by norm_num)
  have hev : ∀ᶠ x in 𝓝 ((0, z) : ℂ × ℂ), cepsKernelDenominatorJetModel p N lam x.2 x.1 ≠ 0 ∧
      cepsCumulantJetQuotient p N lam x.2 x.1 (x.1 * x.2) ≠ 0 :=
    ((hDen.continuousOn.continuousAt (hU.mem_nhds hx)).eventually_ne hDen0).and
      ((hQ.continuousOn.continuousAt (hU.mem_nhds hx)).eventually_ne hQ0)
  obtain ⟨B, hB, hBC, hball⟩ := exists_polydisc_of_eventually_le hC hev
  have hsub : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) C ×ˢ ball z C :=
    fun _ hx => ⟨ball_subset_ball hBC hx.1, ball_subset_ball hBC hx.2⟩
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => exp (cepsCanonJetPolynomial p N (x.1 * lam)
      (cepsComplexScaledDiscount lam x.2 x.1) (x.1 ^ 2 * x.2))) (ball 0 B ×ˢ ball z B) :=
    fun x _ => (cepsMarkedCanonJetPolynomial_frequency_analyticAt p N lam x).differentiableAt.differentiableWithinAt
  have hBridge := ((hGP.mono hsub).neg.mul (hGM.mono hsub)).mul
    ((hDen.mono hsub).inv (fun x hx => (hball x hx).1))
  have hEntrance := (hL.neg.mul (hS.mono hsub)).mul
    (((hQ.mono hsub).mul (hDen.mono hsub)).inv
      (fun x hx => mul_ne_zero (hball x hx).2 (hball x hx).1))
  refine ⟨B, hB, ?_, ?_⟩
  · simpa only [cepsKernelBridgeJetModel, div_eq_mul_inv, Pi.mul_apply, Pi.neg_apply, Pi.inv_apply] using! hBridge
  · simpa only [cepsKernelEntranceJetModel, div_eq_mul_inv, Pi.mul_apply, Pi.neg_apply, Pi.inv_apply] using! hEntrance

end PGM
