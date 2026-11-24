import PLAStochastic.Index.GEP.RawDisc.OfSurvivalBound
import PLAStochastic.Index.GEP.Universality.Defs

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: (U) along the positive mixture paths

For `ν` regular and `σ` a direction law (`SigmaLaw A θσ`), the mixture `ν_t = (1 - t) ν + t σ`,
`t ∈ [0, tMix A θσ]`, lies in the moment class of `momClass_mix`.  Hence (`pw_univClass_mix`)
it belongs to the class of (U), `UnivClass (vlo/2) (vhi+1) κ₃ (BMix D θ A) (θMix θ θσ)`, with
`κ₃ = βMix · (vhi+1)^{3/2}` depending on the regular class only, and it has the bounded density
part `(1 - t) f_ν ≤ D` of mass `1 - t ≥ 1/2` (`pw_smoothPart_mix`).  Since `tMix ≤ 1/4`, (U)
therefore applies to every pair `(ν_t, ν)` (`pw_univMix`): the variance bracket and `κ₃` are fixed
before the output weight `γ`, while `(B, θ)` may depend on `(A, θσ)`.

Wald's identity `E S_T = C_ε` holds on the moment class (`pw_integral_stopSum`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-- The third-moment constant of the (U) class used along the mixture paths. -/
def pwKap3 (D θ vlo vhi : ℝ) : ℝ := βMix D θ vlo * Real.sqrt (vhi + 1) ^ 3

theorem βMix_nonneg (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) : 0 ≤ βMix D θ vlo := by
  unfold βMix kapNu; positivity

/-- **Laws of the moment class are in the class of (U)**. -/
theorem pw_univClass_of_momClass {b β vmin B θ' : ℝ} {ρ : ProbabilityMeasure ℝ} (hβ : 0 ≤ β)
    (hρ : MomClass b β vmin ρ) (hE : ExpMom θ' B ρ) :
    UnivClass vmin b (β * Real.sqrt b ^ 3) B θ' ρ := by
  have h3 : MemLp (fun x : ℝ => x - 1) 3 (ρ : Measure ℝ) :=
    hρ.memLp3.sub (memLp_const 1)
  have hi : Integrable (fun x : ℝ => |x - 1| ^ 3) (ρ : Measure ℝ) := by
    have h := (integrable_norm_rpow_iff h3.aestronglyMeasurable (by norm_num) (by norm_num)).2 h3
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat] at h
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine ⟨hρ.pos, hρ.mean, hρ.var_ge, hρ.var_le, ?_, ?_⟩
  · rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    refine hρ.third_le.trans ?_
    gcongr
    exact hρ.var_le
  · rw [← ofReal_integral_eq_lintegral_ofReal hE.integrable
      (Eventually.of_forall fun x => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hE.le

/-- **The mixture is in the class of (U)** for `t ≤ tMix`. -/
theorem pw_univClass_mix (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) {A θσ : ℝ}
    (hθσ : 0 < θσ) {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hσ : SigmaLaw A θσ σ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (tMix A θσ)) :
    UnivClass (vlo / 2) (vhi + 1) (pwKap3 D θ vlo vhi) (BMix D θ A) (θMix θ θσ)
      (mixPM ν σ t) := by
  have ht' : t ∈ Icc (0 : ℝ) 1 :=
    ⟨ht.1, ht.2.trans ((tMix_le A θσ hθσ).trans (by norm_num))⟩
  exact pw_univClass_of_momClass (βMix_nonneg hD hθ hvlo) (momClass_mix hθ hvlo hθσ hν hσ ht)
    (expMom_mix hθ hvlo hν hσ ht')

/-- **The bounded density part of the mixture**: `(1 - t) f_ν ≤ D`, of mass `1 - t`. -/
theorem pw_smoothPart_mix {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) : SmoothPart D (1 / 2) (mixPM ν σ t) := by
  obtain ⟨f, hfm, hf0, hfneg, hfle, hνf⟩ := hν.density
  have hD := hν.D_nonneg
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, by linarith⟩
  have h1t : 0 ≤ 1 - t := by linarith
  refine ⟨⟨fun x => (1 - t) * f x, measurable_const.mul hfm, fun x => mul_nonneg h1t (hf0 x),
    fun x => ?_, ?_, ?_⟩⟩
  · show (1 - t) * f x ≤ D
    by_cases hx : x ≤ 0
    · rw [hfneg x hx, mul_zero]; exact hD
    · have h1 : f x ≤ D := (hfle x).trans (by
        have : Real.exp (-θ * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        nlinarith)
      nlinarith [hf0 x]
  · have e : (fun x => ENNReal.ofReal ((1 - t) * f x)) =
        ENNReal.ofReal (1 - t) • fun x => ENNReal.ofReal (f x) := by
      funext x
      rw [ENNReal.ofReal_mul h1t]
      rfl
    have hmass : ∫⁻ x, ENNReal.ofReal (f x) = 1 := by
      have h := measure_univ (μ := (ν : Measure ℝ))
      rw [hνf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
      exact h
    have e2 : ∫⁻ x, ENNReal.ofReal ((1 - t) * f x) = ENNReal.ofReal (1 - t) := by
      simp_rw [ENNReal.ofReal_mul h1t]
      rw [lintegral_const_mul _ hfm.ennreal_ofReal, hmass, mul_one]
    rw [e2]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have e : (fun x => ENNReal.ofReal ((1 - t) * f x)) =
        ENNReal.ofReal (1 - t) • fun x => ENNReal.ofReal (f x) := by
      funext x
      rw [ENNReal.ofReal_mul h1t]
      rfl
    rw [e, withDensity_smul _ hfm.ennreal_ofReal, ← hνf, coe_mixPM_of_mem ν σ ht1]
    exact Measure.le_add_right le_rfl

/-- **(U) along the mixture paths**: for every direction law, `d_γ(rawLaw ν_t, rawLaw ν)` is
`O(ε^{-β})` uniformly in `t ∈ [0, tMix]`, with `γ` fixed by the regular class. -/
theorem pw_univMix (hU : GEPUniversality) :
    ∃ βU : ℝ, 1 / 2 < βU ∧ ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
      ∃ γ : ℝ, 0 < γ ∧ ∀ A θσ : ℝ, 0 < θσ → ∃ K e0 : ℝ, ∀ eps, e0 ≤ eps →
        ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
          ∀ t ∈ Icc (0 : ℝ) (tMix A θσ),
            dEtaL γ (rawLaw eps (mixPM ν σ t)) (rawLaw eps ν) ≤
              ENNReal.ofReal (K * eps ^ (-βU)) := by
  obtain ⟨βU, hβU, hU'⟩ := hU
  refine ⟨βU, hβU, fun D θ vlo vhi hD hθ hvlo hv => ?_⟩
  obtain ⟨γ, hγ, hU''⟩ := hU' (vlo / 2) (vhi + 1) (pwKap3 D θ vlo vhi) (by positivity)
    (by linarith)
  refine ⟨γ, hγ, fun A θσ hθσ => ?_⟩
  obtain ⟨K, e0, hK⟩ := hU'' (BMix D θ A) (θMix θ θσ) D (1 / 2) (θMix_pos hθ hθσ)
    (by norm_num)
  refine ⟨K, e0, fun eps heps ν σ hν hσ t ht => ?_⟩
  have htm := tMix_le A θσ hθσ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨le_rfl, (tMix_pos A θσ hθσ).le⟩
  have hU0 := pw_univClass_mix hD hθ hvlo hθσ hν hσ h0
  have hS0 := pw_smoothPart_mix (σ := σ) hν hθ le_rfl (by norm_num)
  rw [mixPM_zero] at hU0 hS0
  exact hK eps heps _ _ (pw_univClass_mix hD hθ hvlo hθσ hν hσ ht)
    (pw_smoothPart_mix hν hθ ht.1 (by linarith [ht.2])) hU0 hS0

/-! ## Wald's identity on the moment class -/

/-- **Wald**: `E S_T = C_ε` for a law of the moment class. -/
theorem pw_integral_stopSum {b β vmin eps : ℝ} (hvmin0 : 0 < vmin) (heps : epsZero b β ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) :
    ∫ g, stopSum eps g ∂(iidLaw ρ) = lawC eps ρ := by
  obtain ⟨-, -, -, -, hfin, hT1, -⟩ := momClass_setup hvmin0 heps hρ
  have hv0 : 0 < lawVar ρ := hvmin0.trans_le hρ.var_ge
  have hσ : 0 < Real.sqrt (lawVar ρ) := Real.sqrt_pos.2 hv0
  have hσ2 : Real.sqrt (lawVar ρ) ^ 2 = lawVar ρ := Real.sq_sqrt hv0.le
  have hX : GapLaw (iidLaw ρ) gapCoord 1 (Real.sqrt (lawVar ρ))
      (∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ)) :=
    gapLaw_iidLaw hρ.memLp3 hρ.mean one_pos hσ2.symm hσ le_rfl
  have hZ : IIDPairs (iidLaw ρ) (inputPairs gapCoord) := IIDPairs.inputPairs hX.iid
  have hW := integral_nextGap (eps := eps) (C := lawC eps ρ) hZ hX hfin hT1 rfl
  rw [← one_mul (lawC eps ρ), ← hW]
  exact integral_congr_ae (Eventually.of_forall fun g =>
    stopSum_fst eps (seq (inputPairs gapCoord) g))

end

end PGM
