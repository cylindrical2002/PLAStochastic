import PLAStochastic.Index.KEP.ReferenceScale.BridgeFirstAverage

/-!
# Uniform actual bridge and first pin budgets at every positive length

All density, class, derivative, support and short-length inputs are discharged
on the unchanged reference orbit. The same positive class rate is kept in the
entire physical bridge length, including one and two steps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReferenceFirst_nonpos {eps : ℝ} (heps : kepReferenceClassicalThreshold ≤ eps)
    {j : ℕ} (_hj : 1 ≤ j) {x : ℝ} (hx : x ≤ 0) :
    gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j) x = 0 := by
  have hm := kepReferenceSpan_pos heps j
  have hmx := mul_nonpos_of_nonneg_of_nonpos hm.le hx
  unfold gammaScaledFirst gammaMixtureFirst
  rw [gammaMixtureDensity_succ_of_nonpos _ 1 hmx,
    gammaMixtureDensity_succ_of_nonpos _ 2 hmx, sub_self, mul_zero]

theorem kepReference_bridge_first_full_length_uniform :
    ∃ C κ eps0 : ℝ, 1 ≤ C ∧ 0 < κ ∧ κ ≤ 1 ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        ∀ w : ℝ, 2 ≤ w →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let r := κ / (2 * w ^ 2)
        (∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ n : ℕ,
          ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
            |kepFixedBridge (kepLogStep f σ) w s n x y| ≤
              C * Real.exp (-r * (n + 1 : ℕ))) ∧
        (∀ n : ℕ, ∀ x y : ℝ, (x = 0 ∨ x = w) → (y = 0 ∨ y = w) →
          (∫ s in Ioc (Real.log (1 / 2)) (Real.log 2),
            |kepFixedBridgeRight (kepLogStep f σ) (kepLogStepFirst f' σ) w s n x y|) ≤
              C * Real.sqrt (1 + kepReferenceSecondNorm eps j) *
                Real.exp (-r * (n + 1 : ℕ))) := by
  obtain ⟨D, θ, vlo, vhi, K, L, e0, hD, -, hvlo, hvhi, -, -, he0, hband⟩ :=
    kepReferenceBand_uniform
  let B := 2 * D * Real.exp 1
  let A := 3 * (2 + 8 * D) * Real.exp 2
  let C := 1 + B + A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hCB : B ≤ C := by dsimp [C]; linarith
  have hCA : A ≤ C := by dsimp [C]; linarith
  refine ⟨C, kepTruncatedKappa D vlo vhi, e0, by dsimp [C]; linarith,
    kepTruncatedKappa_pos hD hvlo hvhi, min_le_right _ _, he0, ?_⟩
  intro eps he heps j hj σ hσ w hw
  dsimp only
  let f := (kepReferenceDensity heps hj).density
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  have H (a : ℝ) (ha : a ∈ Icc (1 / 2 : ℝ) 2) :
      KrBand D θ vlo vhi K L (kepReferenceLaw eps j) f w w a σ (σ * a) := by
    obtain ⟨hf, hr⟩ := hband eps he heps j hj w a (by linarith) ha.1 ha.2
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using hf
    · simpa only [neg_one_mul] using hr
  constructor
  · intro s hs n x hx y hy
    have ha : Real.exp s ∈ Icc (1 / 2 : ℝ) 2 := by
      constructor
      · have hh := Real.exp_le_exp.mpr hs.1.le
        rwa [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)] at hh
      · have hh := Real.exp_le_exp.mpr hs.2
        rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
    have HB := H (Real.exp s) ha
    rw [kepLogBridge_eq_krDens (kepReferenceLaw eps j) HB.hf HB.hf0 HB.hfD HB.hνf hσ s n hx hy]
    exact (krDens_le_exp_full_length (kepReferenceLaw eps j) HB n x y).trans
      (mul_le_mul_of_nonneg_right hCB (Real.exp_pos _).le)
  · intro n x y hx hy
    have hc := kepReferenceDensity_classical heps hj
    have hcf' : Continuous f' := continuous_iff_continuousAt.mpr
      fun t => (hc.2.2.1 t).continuousAt
    have hh := kepLogBridgeRight_first_boundary_average (kepReferenceLaw eps j)
      hD hvlo hvhi hw H hσ hcf' hc.2.2.2.2.1
      (fun t ht => kepReferenceFirst_nonpos heps hj ht) n hx hy
    have hcoef : ((2 + 8 * D) * Real.exp 2 * ∫ t, |f' t|) ≤
        A * Real.sqrt (1 + kepReferenceSecondNorm eps j) := by
      have hi := kepReferenceFirstNorm_le_sqrt heps hj
      have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2 + 8 * D) * Real.exp 2)
      convert hm using 1 <;> first | rfl | (dsimp [A]; ring)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact hcoef.trans (mul_le_mul_of_nonneg_right hCA (Real.sqrt_nonneg _))

end

end PGM
