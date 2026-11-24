import PLAStochastic.Index.CEPS.Scaled.QuotientSpatialJets
import PLAStochastic.Index.CEPS.Scaled.CanonJetCurves
import PLAStochastic.Index.CEPS.Normal.SecondSlopeCurveError

/-! # Exact finite cumulant-jet recovery of the genuine scaled quadratic quotient -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology Asymptotics PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledUnitQuotientAtRoot_jet_isBigO (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    (fun b => cepsScaledUnitQuotientAtRoot D θ ρW lam z sign b -
      cepsCumulantJetQuotientAtRoot (cepsJet f) N lam z sign b)
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
  let a := cepsScaledSignedRoot D θ ρW lam z 1
  let d := cepsScaledSignedRoot D θ ρW lam z (-1)
  let t := cepsScaledSignedRoot D θ ρW lam z sign
  let a' := cepsCumulantRootModel (cepsJet f) N lam z 1 N
  let d' := cepsCumulantRootModel (cepsJet f) N lam z (-1) N
  let t' := cepsCumulantRootModel (cepsJet f) N lam z sign N
  have ha := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hd := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have ht := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
  have ha' := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z 1 N).analyticAt 0
  have hd' := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z (-1) N).analyticAt 0
  have ht' := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z sign N).analyticAt 0
  let R : ℝ := 8 * (1 + ‖a 0‖ + ‖d 0‖ + ‖t 0‖)
  have hR : 0 < R := by dsimp [R]; positivity
  have ha0 : a 0 ∈ ball (0 : ℂ) (R / 4) := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0)]
  have hd0 : d 0 ∈ ball (0 : ℂ) (R / 4) := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0)]
  have ht0 : t 0 ∈ ball (0 : ℂ) (R / 4) := by rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0)]
  have ha'0 : a' 0 ∈ ball (0 : ℂ) (R / 4) := by
    change cepsCumulantRootModel (cepsJet f) N lam z 1 N 0 ∈ _
    rw [cepsCumulantRootModel_cepsJet_zero dom hW hθ hD hfW N lam hz (by norm_num) N]
    exact ha0
  have hd'0 : d' 0 ∈ ball (0 : ℂ) (R / 4) := by
    change cepsCumulantRootModel (cepsJet f) N lam z (-1) N 0 ∈ _
    rw [cepsCumulantRootModel_cepsJet_zero dom hW hθ hD hfW N lam hz (by norm_num) N]
    exact hd0
  have ht'0 : t' 0 ∈ ball (0 : ℂ) (R / 4) := by
    change cepsCumulantRootModel (cepsJet f) N lam z sign N 0 ∈ _
    rw [cepsCumulantRootModel_cepsJet_zero dom hW hθ hD hfW N lam hz hsign N]
    exact ht0
  obtain ⟨C, B, _, hB, he⟩ := cepsScaledQuotientSpatialUnit_jet_budget hW hθ hD hfW N lam z hR
  let B' : ℝ := min B (cepsCgfRadius D θ / (2 * R))
  have hB' : 0 < B' := by dsimp [B']; positivity [cepsCgfRadius_pos hD hθ]
  have hBR : B' * R < cepsCgfRadius D θ := by
    have hh : B' * R ≤ cepsCgfRadius D θ / (2 * R) * R :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
    have hcancel : cepsCgfRadius D θ / (2 * R) * R = cepsCgfRadius D θ / 2 := by field_simp [hR.ne']
    rw [hcancel] at hh
    exact hh.trans_lt (half_lt_self (cepsCgfRadius_pos hD hθ))
  have hFdisc := cepsScaledQuotientSpatialUnit_analyticOnNhd_disc hW hθ hD (lam := lam) (z := z) hR hBR
  have hF : ∀ b ∈ ball (0 : ℂ) B', DifferentiableOn ℂ (cepsScaledQuotientSpatialUnit ρW lam z b) (ball 0 R) :=
    fun b hb ξ hξ => (hFdisc (b, ξ) ⟨hb, hξ⟩).curry_right.differentiableAt.differentiableWithinAt
  have hG : ∀ b : ℂ, DifferentiableOn ℂ (cepsCumulantQuotientSpatialUnit (cepsJet f) N lam z b) (ball 0 R) :=
    fun b ξ _ => (cepsCumulantQuotientSpatialUnit_joint_analyticAt (cepsJet f) N lam z (b, ξ)).curry_right.differentiableAt.differentiableWithinAt
  have herr := cepsNormal_second_dslope_curve_error_isBigO hR hB' hF
    (fun b _ => hG b) N
    (fun b hb ξ hξ => he (ball_subset_ball (min_le_left _ _) hb) hξ)
    ha.continuousAt hd.continuousAt ht.continuousAt
    (ball_subset_ball (by linarith : R / 4 ≤ R / 2) ha0)
    (ball_subset_ball (by linarith : R / 4 ≤ R / 2) hd0)
    (ball_subset_ball (by linarith : R / 4 ≤ R / 2) ht0)
  obtain ⟨M, hM⟩ := cepsCumulantQuotientSpatialUnit_disc_bound (cepsJet f) N lam z R
  have hnodes := cepsNormal_second_dslope_node_curves_isBigO hR (by norm_num : (0 : ℝ) < 1)
    (fun b _ => hG b) hM N ha.continuousAt hd.continuousAt ht.continuousAt
    ha'.continuousAt hd'.continuousAt ht'.continuousAt ha0 hd0 ht0 ha'0 hd'0 ht'0
    (cepsCumulantRootModel_actual_isBigO_all dom hθ hD hW hfW N lam hz (by norm_num))
    (cepsCumulantRootModel_actual_isBigO_all dom hθ hD hW hfW N lam hz (by norm_num))
    (cepsCumulantRootModel_actual_isBigO_all dom hθ hD hW hfW N lam hz hsign)
  exact (herr.add hnodes).congr_left (fun _ => sub_add_sub_cancel _ _ _)

include dom hW hθ hD in
theorem cepsScaledQuotientAtRoot_taylorJets_eq_finite_model (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z sign : ℂ} (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (cepsScaledQuotientAtRoot D θ ρW lam z sign) 0) =
      coeff j (complexTaylorSeries (cepsCumulantJetQuotientAtRoot (cepsJet f) N lam z sign) 0) := by
  have he := cepsScaledQuotientAtRoot_eq_unit_eventually hW hθ hD dom lam hz hsign
  have ha := cepsScaledUnitQuotientAtRoot_analyticAt dom hW hθ hD lam hz hsign
  have hm := cepsCumulantJetQuotientAtRoot_analyticAt (cepsJet f) N lam z sign
  have herr := cepsScaledUnitQuotientAtRoot_jet_isBigO dom hW hθ hD hfW N lam hz hsign
  have herr' : (fun b => cepsScaledQuotientAtRoot D θ ρW lam z sign b -
      cepsCumulantJetQuotientAtRoot (cepsJet f) N lam z sign b)
      =O[𝓝 (0 : ℂ)] (fun b => b ^ (N + 1)) := by
    apply herr.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [he] with b hb
    rw [hb]
  exact complexTaylorSeries_coeff_eq_of_isBigO (ha.congr he.symm) hm N herr'

end PGM
