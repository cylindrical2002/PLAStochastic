import PLAStochastic.Index.CEPS.Scaled.KernelGCurveJets
import PLAStochastic.Index.CEPS.Normal.MovingSlopeGerms

/-! # Explicit finite mixed-jet bridge and entrance factors -/

noncomputable section
open Complex Set Metric Filter Topology PowerSeries
namespace PGM

def cepsKernelDenominatorJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  dslope (cepsKernelGJetModel p N lam z b)
    (cepsCumulantRootModel p N lam z (-1) N b) (cepsCumulantRootModel p N lam z 1 N b)

def cepsKernelEntranceSlopeJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  dslope (dslope (cepsKernelGJetModel p N lam z b)
    (cepsCumulantRootModel p N lam z (-1) N b)) (cepsCumulantRootModel p N lam z 1 N b) (b * z)

def cepsKernelBridgeJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  -cepsKernelGJetModel p N lam z b (cepsCumulantRootModel p N lam z 1 N b) *
    cepsKernelGJetModel p N lam z b (cepsCumulantRootModel p N lam z (-1) N b) /
      cepsKernelDenominatorJetModel p N lam z b

def cepsKernelEntranceJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  -exp (cepsCanonJetPolynomial p N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) *
    cepsKernelEntranceSlopeJetModel p N lam z b /
      (cepsCumulantJetQuotient p N lam z b (b * z) * cepsKernelDenominatorJetModel p N lam z b)

theorem cepsKernelFiniteFactors_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) (lam : ℝ) (z : ℂ) :
    cepsKernelDenominatorJetModel p N lam z = cepsKernelDenominatorJetModel p' N lam z ∧
    cepsKernelEntranceSlopeJetModel p N lam z = cepsKernelEntranceSlopeJetModel p' N lam z ∧
    cepsKernelBridgeJetModel p N lam z = cepsKernelBridgeJetModel p' N lam z ∧
    cepsKernelEntranceJetModel p N lam z = cepsKernelEntranceJetModel p' N lam z := by
  have hpN : ∀ i, i < cepsJetDim N → p i = p' i :=
    fun i hi => hp i (hi.trans_le (cepsJetDim_monotone (by omega : N ≤ 4 * N)))
  have hG := cepsKernelGJetModel_congr N hp lam z
  have hRp := cepsCumulantRootModel_congr N hpN lam z 1 N
  have hRm := cepsCumulantRootModel_congr N hpN lam z (-1) N
  have hQ := cepsCumulantJetQuotient_congr N hpN lam z
  have hL := cepsCanonJetPolynomial_congr N hp
  have hDen : cepsKernelDenominatorJetModel p N lam z = cepsKernelDenominatorJetModel p' N lam z := by
    funext b; simp only [cepsKernelDenominatorJetModel, hG, hRp, hRm]
  have hSlope : cepsKernelEntranceSlopeJetModel p N lam z = cepsKernelEntranceSlopeJetModel p' N lam z := by
    funext b; simp only [cepsKernelEntranceSlopeJetModel, hG, hRp, hRm]
  refine ⟨hDen, hSlope, ?_, ?_⟩
  · funext b; simp only [cepsKernelBridgeJetModel, hG, hRp, hRm, hDen]
  · funext b; simp only [cepsKernelEntranceJetModel, hL, hSlope, hQ, hDen]

theorem cepsKernelGJetModel_moving_slopes_analyticAt (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z : ℂ) {a d t : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (hd : AnalyticAt ℂ d 0) (ht : AnalyticAt ℂ t 0) :
    AnalyticAt ℂ (fun b => dslope (cepsKernelGJetModel p N lam z b) (a b) (d b)) 0 ∧
    AnalyticAt ℂ (fun b => dslope (dslope (cepsKernelGJetModel p N lam z b) (a b)) (d b) (t b)) 0 := by
  let R : ℝ := 2 * (1 + ‖a 0‖ + ‖d 0‖ + ‖t 0‖)
  have hR : 0 < R := by dsimp [R]; positivity
  have ha0 : a 0 ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0)]
  have hd0 : d 0 ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0)]
  have ht0 : t 0 ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0)]
  obtain ⟨B, hB, hG⟩ := cepsKernelGJetModel_differentiableOn_joint p N lam z hR
  exact ⟨cepsNormal_moving_dslope_analyticAt_of_differentiableOn hB hG ha hd ha0 hd0,
    cepsNormal_moving_second_dslope_analyticAt_of_differentiableOn hB hG ha hd ht ha0 hd0 ht0⟩

theorem cepsKernelFiniteSlopes_analyticAt (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z : ℂ) :
    AnalyticAt ℂ (cepsKernelDenominatorJetModel p N lam z) 0 ∧
    AnalyticAt ℂ (cepsKernelEntranceSlopeJetModel p N lam z) 0 := by
  have hRm := (cepsCumulantRootModel_differentiable p N lam z (-1) N).analyticAt 0
  have hRp := (cepsCumulantRootModel_differentiable p N lam z 1 N).analyticAt 0
  have hmark : AnalyticAt ℂ (fun b : ℂ => b * z) 0 := by fun_prop
  exact cepsKernelGJetModel_moving_slopes_analyticAt p N lam z hRm hRp hmark

theorem cepsKernelBridgeJetModel_analyticAt (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z : ℂ)
    (hDen : cepsKernelDenominatorJetModel p N lam z 0 ≠ 0) :
    AnalyticAt ℂ (cepsKernelBridgeJetModel p N lam z) 0 := by
  have hp := cepsKernelGJetModel_curve_analyticAt p N lam z
    ((cepsCumulantRootModel_differentiable p N lam z 1 N).analyticAt 0)
  have hm := cepsKernelGJetModel_curve_analyticAt p N lam z
    ((cepsCumulantRootModel_differentiable p N lam z (-1) N).analyticAt 0)
  exact (hp.neg.mul hm).div (cepsKernelFiniteSlopes_analyticAt p N lam z).1 hDen

theorem cepsKernelEntranceJetModel_analyticAt (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z : ℂ)
    (hVar : p (cepsJetCode (.inl 0)) ≠ 0)
    (hDen : cepsKernelDenominatorJetModel p N lam z 0 ≠ 0) :
    AnalyticAt ℂ (cepsKernelEntranceJetModel p N lam z) 0 := by
  have hμ : AnalyticAt ℂ (fun b : ℂ => b * lam) 0 := by fun_prop
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount lam z) 0 := by unfold cepsComplexScaledDiscount; fun_prop
  have hζ : AnalyticAt ℂ (fun b : ℂ => b ^ 2 * z) 0 := by fun_prop
  have hL := (cepsCanonJetPolynomial_curve_analyticAt p N hμ hq hζ).cexp
  have hmark : AnalyticAt ℂ (fun b : ℂ => b * z) 0 := by fun_prop
  have hQ := cepsCumulantJetQuotient_curve_analyticAt p N lam z hmark
  have hQ0 : cepsCumulantJetQuotient p N lam z 0 (0 * z) ≠ 0 := by
    rw [cepsCumulantJetQuotient_zero]
    exact div_ne_zero (by exact_mod_cast hVar) (by norm_num)
  have hsl := cepsKernelFiniteSlopes_analyticAt p N lam z
  exact (hL.neg.mul hsl.2).div (hQ.mul hsl.1) (mul_ne_zero hQ0 hDen)

end PGM
