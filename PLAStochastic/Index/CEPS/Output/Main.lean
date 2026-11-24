import PLAStochastic.Index.CEPS.Output.Assembly
import PLAStochastic.ForMathlib.Analysis.SpecificLimits.TwoScaleSum

/-!
# Track O: the high-frequency bound of the actual one-layer output (interface T2)

`research/2026-10-02-lean-ceps/design.md`, interface T2;
`research/2026-09-29-ceps-full-expansion/output-closure.md` (O10)–(O14).

**Theorem** (`norm_charFun_lawPhi_le`). For every `r` and class parameters there is a
constant `K = outHighConst r D θ vlo E κ` such that for `ε ≥ outHighEps r D θ vlo vhi`, every
`ν` in `RegLaw D θ vlo vhi` with a density `f` in the input class `OutInput r E κ`, and every
real `u`,

`|u|^r |∫ e^{iux} d(lawPhi ε ν)(x)| ≤ K ε^{r+2}`.

Proof: `φ(u) = ∑_n ∫_{T = n} e^{iuS_n/C}` (`T < ∞` a.s.); each term is a cone integral
(`setIntegral_stop_eq_cone`), zero for `n ≤ 2ε` (`not_stopsAt_of_le`) and otherwise bounded by
`perLength_bound` at `τ = u/C` with the stopping weight `min(L_n, S_n)`
(`outMeasure_stop_le_min`); the two-scale sum (`tsum_twoScale_le`, `min_stop_rpow_le`) gives
`∑_n ≤ K' ε^{2-r}`, and `C ≤ cPlus ε²/regV vlo` (`momClass_oneLayer`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

namespace PGM

/-- The constant of the high-frequency bound. -/
def outHighConst (r : ℕ) (D θ vlo E κ : ℝ) : ℝ :=
  (cPlus / regV vlo) ^ r * (outLengthConst r E κ * stopConst r vlo E κ *
    ((1 + r.factorial / stopRateShort D θ κ ^ r) * (1 + 1 / stopRateLong r vlo)))

/-- The threshold of the high-frequency bound. -/
def outHighEps (r : ℕ) (D θ vlo vhi : ℝ) : ℝ :=
  max (epsZero (regB vhi) (regBeta D θ vlo)) (17 * r + 1)

/-- **High-frequency bound of the actual one-layer output** (interface T2). -/
theorem norm_charFun_lawPhi_le (r : ℕ) {D θ vlo vhi E κ : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {eps : ℝ} (heps : outHighEps r D θ vlo vhi ≤ eps)
    {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} (hreg : RegLaw D θ vlo vhi ν)
    (h : OutInput r E κ f ν) (u : ℝ) :
    |u| ^ r * ‖∫ x, Complex.exp (Complex.I * u * x) ∂(lawPhi eps ν : Measure ℝ)‖ ≤
      outHighConst r D θ vlo E κ * eps ^ (r + 2) := by
  classical
  have heps0 : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps := (le_max_left _ _).trans heps
  have hepsr : (17 * r + 1 : ℝ) ≤ eps := (le_max_right _ _).trans heps
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps0
  have heps0' : 0 < eps := by linarith
  have hmom := hreg.momClass hθ hvlo
  have hv := regV_pos hvlo
  obtain ⟨hfin, hClow, hCup⟩ := momClass_oneLayer hv heps0 hmom
  set C := lawC eps ν with hCdef
  have hb : 0 < regB vhi := by
    have := hreg.var_ge
    have h1 : vlo ≤ vhi := this.trans hreg.var_le
    exact lt_of_lt_of_le hvlo (h1.trans (le_max_left _ _))
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hClow
  -- the characteristic function on the canonical space
  set F : (ℕ → ℝ) → ℂ := fun g => Complex.exp (Complex.I * u * ↑(stopSum eps g / C)) with hF
  have hFm : Measurable F := by
    refine Complex.measurable_exp.comp ?_
    exact measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_stopSum eps).div_const C))
  have hφ : ∫ x, Complex.exp (Complex.I * u * x) ∂(lawPhi eps ν : Measure ℝ) =
      ∫ g, F g ∂(iidLaw ν) := by
    change ∫ x, Complex.exp (Complex.I * u * x) ∂((iidLaw ν).map
      (fun g => stopSum eps g / lawC eps ν)) = _
    have hcont : Continuous fun x : ℝ => Complex.exp (Complex.I * u * x) := by fun_prop
    rw [integral_map ((measurable_stopSum eps).div_const _).aemeasurable
      hcont.aestronglyMeasurable]
  set s : ℕ → Set (ℕ → ℝ) := fun n => {g | gapSegLen eps g = n} with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n =>
    (isStoppingRule_gapSegLen eps).measurable (measurableSet_singleton _)
  have hsd : Pairwise (Function.onFun Disjoint s) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun g hg hg' => hnm ?_
    have : (n : ℕ∞) = m := hg.symm.trans hg'
    exact_mod_cast this
  have hFi : Integrable F (iidLaw ν) := by
    refine (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [hF]
    simp only
    rw [show Complex.I * u * ↑(stopSum eps g / C) = ↑(u * (stopSum eps g / C)) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hunion : (iidLaw ν).restrict (⋃ n, s n) = iidLaw ν := by
    refine Measure.restrict_eq_self_of_ae_mem (hfin.mono fun g hg => ?_)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hg
    exact Set.mem_iUnion.mpr ⟨n, hn.symm⟩
  have hsum : HasSum (fun n => ∫ g in s n, F g ∂(iidLaw ν)) (∫ g, F g ∂(iidLaw ν)) := by
    have := hasSum_integral_iUnion hsm hsd hFi.integrableOn
    rwa [hunion] at this
  -- each length
  set Q : ℕ → ℝ := fun n => min (stopLong r vlo eps n) (stopShort r D θ E κ eps n) with hQ
  set gg : ℕ → ℝ := fun n => if 2 * eps < n then
    outLengthConst r E κ * (Real.sqrt n ^ r)⁻¹ * Q n ^ (1 / 4 : ℝ) else 0 with hgg
  have hterm : ∀ n, ‖((|u| ^ r : ℝ) : ℂ) * ∫ g in s n, F g ∂(iidLaw ν)‖ ≤ C ^ r * gg n := by
    intro n
    have hcone_eq : ∫ g in s n, F g ∂(iidLaw ν) =
        ∫ x, coneIntegrand {z : Fin n → ℝ | stopsAt eps z} f (u / C) x := by
      rw [← setIntegral_stop_eq_cone h.pos h.measurable_f h.density eps (u / C) n]
      refine setIntegral_congr_fun (hsm n) fun g hg => ?_
      have hgn : gapSegLen eps g = n := hg
      simp only [hF, stopSum, hgn, ENat.toNat_natCast]
      congr 1
      push_cast
      ring
    rw [hcone_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hn : 2 * eps < n
    · have hn17 : 17 * r + 1 ≤ n := by
        have : (17 * r + 1 : ℝ) < n := by linarith
        exact_mod_cast this.le
      have hn1 : 1 ≤ n := by omega
      have hQ0 : 0 ≤ Q n := le_min (stopLong_nonneg _ _ _ _) (stopShort_nonneg _ _ _ _ _ _ _)
      have hper := perLength_bound h hn17 (measurableSet_stopsAt eps n)
        (fun c hc x => by simp only [Set.mem_ofPred_eq]; exact stopsAt_smul hc x) hQ0
        (fun β hβ hH => outMeasure_stop_le_min h hreg hθ hvlo heps0 hn1 β hβ hH) (u / C)
      have hu : |u| ^ r = C ^ r * |u / C| ^ r := by
        rw [abs_div, abs_of_pos hC0, div_pow, mul_div_cancel₀ _ (pow_pos hC0 r).ne']
      simp only [hgg, if_pos hn]
      rw [hu, mul_assoc]
      exact mul_le_mul_of_nonneg_left hper (pow_nonneg hC0.le r)
    · have hempty : ∀ x : Fin n → ℝ, coneIntegrand {z : Fin n → ℝ | stopsAt eps z} f (u / C) x = 0 :=
        fun x => indicator_of_notMem (s := {z : Fin n → ℝ | stopsAt eps z})
          (not_stopsAt_of_le heps0'.le (not_lt.mp hn) x) _
      simp only [hempty, integral_zero, norm_zero, mul_zero, hgg, if_neg hn]
      exact le_refl _
  -- the two-scale sum
  set a := stopRateLong r vlo with ha
  set b := stopRateShort D θ κ with hbdef
  have ha0 : 0 < a := stopRateLong_pos r hvlo
  have hb0 : 0 < b := stopRateShort_pos hD hθ h.κpos
  set M := outLengthConst r E κ * stopConst r vlo E κ with hM
  have hM0 : 0 ≤ M := mul_nonneg (outLengthConst_nonneg r E κ) (stopConst_nonneg r vlo E κ)
  have hgg0 : ∀ n, 0 ≤ gg n := by
    intro n
    simp only [hgg]
    split_ifs
    · have := outLengthConst_nonneg r E κ
      have hQ0 : 0 ≤ Q n := le_min (stopLong_nonneg _ _ _ _) (stopShort_nonneg _ _ _ _ _ _ _)
      have := Real.rpow_nonneg hQ0 (1 / 4 : ℝ)
      positivity
    · exact le_refl _
  have hggz : gg 0 = 0 := by
    simp only [hgg]
    rw [if_neg (by push_cast; linarith)]
  have hggb : ∀ n : ℕ, 1 ≤ n → gg n ≤ M * ((Real.sqrt n ^ r)⁻¹ * Real.exp (-(a * n / eps ^ 2)) *
      Real.exp (-(b * eps ^ 2 / n))) := by
    intro n hn1
    simp only [hgg]
    split_ifs with hn
    · have hmaj := min_stop_rpow_le (r := r) (E := E) (κ := κ) hD hθ hvlo heps1 hn h.κpos
      have hK := outLengthConst_nonneg r E κ
      have hs0 : 0 ≤ (Real.sqrt n ^ r)⁻¹ := by positivity
      calc outLengthConst r E κ * (Real.sqrt n ^ r)⁻¹ * Q n ^ (1 / 4 : ℝ)
          ≤ outLengthConst r E κ * (Real.sqrt n ^ r)⁻¹ * (stopConst r vlo E κ *
              (Real.exp (-(a * n / eps ^ 2)) * Real.exp (-(b * eps ^ 2 / n)))) :=
            mul_le_mul_of_nonneg_left hmaj (mul_nonneg hK hs0)
        _ = _ := by rw [hM]; ring
    · have : 0 ≤ (Real.sqrt n ^ r)⁻¹ := by positivity
      positivity
  obtain ⟨hgs, hgle⟩ := tsum_twoScale_le ha0 hb0 heps1 hM0 hgg0 hggz hggb
  have hsum2 : HasSum (fun n => C ^ r * gg n) (C ^ r * ∑' n, gg n) := hgs.hasSum.mul_left _
  have hmain := (hsum.mul_left ((|u| ^ r : ℝ) : ℂ)).norm_le_of_bounded hsum2 hterm
  rw [hφ]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hmain
  refine hmain.trans ?_
  have hCr : C ^ r ≤ (cPlus * eps ^ 2 / regV vlo) ^ r := pow_le_pow_left₀ hC0.le hCup r
  have hT0 : 0 ≤ ∑' n, gg n := tsum_nonneg hgg0
  calc C ^ r * ∑' n, gg n
      ≤ (cPlus * eps ^ 2 / regV vlo) ^ r *
          (M * ((1 + r.factorial / b ^ r) * (1 + 1 / a)) * (eps ^ 2 / eps ^ r)) :=
        mul_le_mul hCr hgle hT0 (pow_nonneg (by have := cPlus_pos; positivity) r)
    _ = outHighConst r D θ vlo E κ * eps ^ (r + 2) := by
        rw [outHighConst, ← ha, ← hbdef, ← hM]
        field_simp
        ring

end PGM
