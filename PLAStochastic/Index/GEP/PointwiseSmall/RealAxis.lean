import PLAStochastic.Index.GEP.PointwiseSmall.MixtureClass
import PLAStochastic.Index.GEP.PointwiseSmall.WeightedW1Tests
import PLAStochastic.Index.GEP.Response.OfInterfaces
import PLAStochastic.Index.GEP.Response.KappaBound

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: real-axis smallness from (U)

`PwUnivMix βU` is the form of (U) along the positive mixture paths (`pw_univMix`).  With the
layer-cake bound `pw_abs_sub_le_dEtaL` it gives, for every test `χ` with
`|χ(s)| ≤ L e^{γ' s}` (`OutTest γ' L χ`) and `t ∈ [0, tMix]`,
`|E_{ν_t} φ(v_t S_T/ε²) - E_ν φ(v S_T/ε²)| ≤ L K ε^{-βU}` (`pw_real_test`), `φ = testFn χ`.
The weight `γ' = min γ_U (gamMix vlo / (2 (vhi + 1)))` makes `w e^{γ' w}` integrable under every
`rawLaw ε ν_t` (`stopExp_mix`).  Specialisations: the first and second raw moments
`pwM1 = E[v S_T/ε²] = v C/ε²` (Wald, `pwM1_eq`) and `pwM2 = E[(v S_T/ε²)²]`
(`pw_real_moments`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-- (U) along the positive mixture paths, with rate exponent `βU`. -/
def PwUnivMix (βU : ℝ) : Prop :=
  ∀ D θ vlo vhi : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi →
    ∃ γ : ℝ, 0 < γ ∧ ∀ A θσ : ℝ, 0 < θσ → ∃ K e0 : ℝ, ∀ eps, e0 ≤ eps →
      ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        ∀ t ∈ Icc (0 : ℝ) (tMix A θσ),
          dEtaL γ (rawLaw eps (mixPM ν σ t)) (rawLaw eps ν) ≤ ENNReal.ofReal (K * eps ^ (-βU))

theorem pwUnivMix_of_univ (hU : GEPUniversality) : ∃ βU : ℝ, 1 / 2 < βU ∧ PwUnivMix βU :=
  pw_univMix hU

/-- The first raw moment `E[v S_T/ε²]`. -/
def pwM1 (eps : ℝ) (ρ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ g, lawVar ρ * stopSum eps g / eps ^ 2 ∂(iidLaw ρ)

/-- The second raw moment `E[(v S_T/ε²)²]`. -/
def pwM2 (eps : ℝ) (ρ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ g, (lawVar ρ * stopSum eps g / eps ^ 2) ^ 2 ∂(iidLaw ρ)

/-- Wald for the first raw moment. -/
theorem pwM1_eq {b β vmin eps : ℝ} (hvmin0 : 0 < vmin) (heps : epsZero b β ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) :
    pwM1 eps ρ = lawVar ρ * lawC eps ρ / eps ^ 2 := by
  rw [pwM1, integral_div, integral_const_mul, pw_integral_stopSum hvmin0 heps hρ]

theorem dEtaL_mono {γ₁ γ₂ : ℝ} (h : γ₁ ≤ γ₂) (μ ρ : ProbabilityMeasure ℝ) :
    dEtaL γ₁ μ ρ ≤ dEtaL γ₂ μ ρ := by
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
  gcongr
  exact le_of_lt hx

theorem testFn_nonneg_arg {χ : ℝ → ℝ} {y : ℝ} (hy : y ≤ 0) : testFn χ y = 0 := by
  rw [testFn, Set.Ioo_eq_empty (not_lt.2 hy), Measure.restrict_empty, integral_zero_measure]

/-- **Real-axis smallness of the tests** along the mixture path. -/
theorem pw_real_test {βU : ℝ} (hUM : PwUnivMix βU) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) :
    ∃ γ' : ℝ, 0 < γ' ∧ ∀ A θσ : ℝ, 0 < θσ → ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps →
      ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        ∀ t ∈ Icc (0 : ℝ) (tMix A θσ), ∀ (χ : ℝ → ℝ) (L : ℝ), OutTest γ' L χ →
          |∫ g, testFn χ (lawVar (mixPM ν σ t) * stopSum eps g / eps ^ 2)
              ∂(iidLaw (mixPM ν σ t)) -
            ∫ g, testFn χ (lawVar ν * stopSum eps g / eps ^ 2) ∂(iidLaw ν)| ≤
            L * (K * eps ^ (-βU)) := by
  obtain ⟨γU, hγU, hU⟩ := hUM D θ vlo vhi hD hθ hvlo hv
  have hg := gamMix_pos hvlo
  set γ' := min γU (gamMix vlo / (2 * (vhi + 1))) with hγ'
  have hvhi : 0 < vhi + 1 := by linarith
  have hγ'0 : 0 < γ' := lt_min hγU (by positivity)
  refine ⟨γ', hγ'0, fun A θσ hθσ => ?_⟩
  obtain ⟨K, eU, hK⟩ := hU A θσ hθσ
  obtain ⟨e₁, he₁1, hmix⟩ := stopExp_mix (vhi := vhi) (A := A) hD hθ hvlo hθσ
  refine ⟨max K 0, max (max eU e₁) (epsZero (vhi + 1) (βMix D θ vlo)), le_max_right _ _,
    he₁1.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  intro eps heps ν σ hν hσ t ht χ L hχ
  have heU : eU ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have he₁ : e₁ ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have hez : epsZero (vhi + 1) (βMix D θ vlo) ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := he₁1.trans he₁
  have heps2 : 0 < eps ^ 2 := by positivity
  have hmeas := hχ.measurable_testFn
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨le_rfl, (tMix_pos A θσ hθσ).le⟩
  -- facts for a point of the segment
  have hfacts : ∀ s ∈ Icc (0 : ℝ) (tMix A θσ),
      ((rawLaw eps (mixPM ν σ s) : Measure ℝ) (Iio 0) = 0 ∧
        Integrable (fun x => x * Real.exp (γ' * x)) (rawLaw eps (mixPM ν σ s) : Measure ℝ)) ∧
      ∫ x, testFn χ x ∂(rawLaw eps (mixPM ν σ s) : Measure ℝ) =
        ∫ g, testFn χ (lawVar (mixPM ν σ s) * stopSum eps g / eps ^ 2)
          ∂(iidLaw (mixPM ν σ s)) := by
    intro s hs
    set ρ := mixPM ν σ s with hρ
    have hm := momClass_mix hθ hvlo hθσ hν hσ hs
    have hv0 : 0 ≤ lawVar ρ := (by positivity : (0 : ℝ) ≤ vlo / 2).trans hm.var_ge
    have hW : Measurable fun g => lawVar ρ * stopSum eps g / eps ^ 2 :=
      (measurable_const.mul (measurable_stopSum eps)).div_const _
    have hmap : (rawLaw eps ρ : Measure ℝ) =
        (iidLaw ρ).map (fun g => lawVar ρ * stopSum eps g / eps ^ 2) := rfl
    have hSnn : ∀ᵐ g ∂(iidLaw ρ), 0 ≤ stopSum eps g := by
      filter_upwards [ae_pos_iidLaw hm.pos] with g hg
      exact rawAsm_stopSum_nonneg fun j => (hg j).le
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hmap, Measure.map_apply hW measurableSet_Iio]
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hSnn] with g hg
      simp only [Set.mem_preimage, Set.mem_Iio, not_lt]
      positivity
    · rw [hmap]
      refine (integrable_map_measure (by fun_prop) hW.aemeasurable).2 ?_
      set c := 2 * γ' * lawVar ρ with hc
      have hc0 : 0 ≤ c := by positivity
      have hcg : c ≤ gamMix vlo := by
        have h1 : γ' ≤ gamMix vlo / (2 * (vhi + 1)) := min_le_right _ _
        rw [le_div_iff₀ (by positivity)] at h1
        have h2 := hm.var_le
        rw [hc]
        nlinarith
      obtain ⟨hint, -⟩ := (hmix eps he₁ ν σ hν hσ s hs).2.2 c hc0 hcg
      refine (hint.const_mul (1 / γ')).mono' ?_ ?_
      · exact (by fun_prop : Measurable fun x : ℝ => x * Real.exp (γ' * x)).comp_aemeasurable
          hW.aemeasurable |>.aestronglyMeasurable
      · filter_upwards [hSnn] with g hg
        have hw0 : 0 ≤ lawVar ρ * stopSum eps g / eps ^ 2 := by positivity
        simp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h := mul_exp_le_exp_div (η := γ') (θ := 2 * γ')
          (x := lawVar ρ * stopSum eps g / eps ^ 2) (by linarith)
        have e1 : 2 * γ' * (lawVar ρ * stopSum eps g / eps ^ 2) = c * stopSum eps g / eps ^ 2 := by
          rw [hc]; ring
        rw [e1, show 2 * γ' - γ' = γ' by ring] at h
        calc lawVar ρ * stopSum eps g / eps ^ 2 * Real.exp (γ' * (lawVar ρ * stopSum eps g /
              eps ^ 2)) ≤ Real.exp (c * stopSum eps g / eps ^ 2) / γ' := h
          _ = 1 / γ' * Real.exp (c * stopSum eps g / eps ^ 2) := by ring
    · rw [hmap, integral_map hW.aemeasurable hmeas.aestronglyMeasurable]
  obtain ⟨⟨h1pos, h1int⟩, h1eq⟩ := hfacts t ht
  obtain ⟨⟨h0pos, h0int⟩, h0eq⟩ := hfacts 0 h0
  rw [mixPM_zero] at h0pos h0int h0eq
  have hdU := hK eps heU ν σ hν hσ t ht
  have hd : dEtaL γ' (rawLaw eps (mixPM ν σ t)) (rawLaw eps ν) ≤
      ENNReal.ofReal (max K 0 * eps ^ (-βU)) :=
    (dEtaL_mono (min_le_left _ _) _ _).trans (hdU.trans (ENNReal.ofReal_le_ofReal (by
      gcongr; exact le_max_left _ _)))
  have hfin : dEtaL γ' (rawLaw eps (mixPM ν σ t)) (rawLaw eps ν) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd
  have h := pw_abs_sub_le_dEtaL h1pos h0pos hχ.1 hγ'0.le hχ.2 h1int h0int hfin
  rw [h1eq, h0eq] at h
  have hL : 0 ≤ L := by
    have h := hχ.2 0 le_rfl
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact (abs_nonneg _).trans h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hL)
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hd

theorem outTest_one (γ : ℝ) (hγ : 0 ≤ γ) : OutTest γ 1 (fun _ => (1 : ℝ)) :=
  ⟨measurable_const, fun x hx => by
    rw [abs_one, one_mul]; exact Real.one_le_exp (by positivity)⟩

theorem outTest_two_mul {γ : ℝ} (hγ : 0 < γ) : OutTest γ (2 / γ) (fun t => 2 * t) :=
  ⟨by fun_prop, fun x hx => by
    rw [abs_of_nonneg (by positivity)]
    have h := le_exp_div (η := γ) (t := x) hγ
    calc 2 * x ≤ 2 * (Real.exp (γ * x) / γ) := by linarith
      _ = 2 / γ * Real.exp (γ * x) := by ring⟩

/-- **Real-axis smallness of the raw moments** along the mixture path. -/
theorem pw_real_moments {βU : ℝ} (hUM : PwUnivMix βU) (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (A θσ : ℝ) (hθσ : 0 < θσ) :
    ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps →
      ∀ ν σ : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        ∀ t ∈ Icc (0 : ℝ) (tMix A θσ),
          |pwM1 eps (mixPM ν σ t) - pwM1 eps ν| ≤ K * eps ^ (-βU) ∧
          |pwM2 eps (mixPM ν σ t) - pwM2 eps ν| ≤ K * eps ^ (-βU) := by
  obtain ⟨γ', hγ', hR⟩ := pw_real_test hUM hD hθ hvlo hv
  obtain ⟨K, e0, hK, he0, hK'⟩ := hR A θσ hθσ
  refine ⟨(1 + 2 / γ') * K, e0, by positivity, he0, fun eps heps ν σ hν hσ t ht => ?_⟩
  have heps0 : 0 < eps := by linarith
  -- a.e. nonnegativity of the raw variable
  have hnn : ∀ ρ : ProbabilityMeasure ℝ, (ρ : Measure ℝ) (Iic 0) = 0 → 0 ≤ lawVar ρ →
      ∀ᵐ g ∂(iidLaw ρ), 0 ≤ lawVar ρ * stopSum eps g / eps ^ 2 := by
    intro ρ hρ hv0
    filter_upwards [ae_pos_iidLaw hρ] with g hg
    have := rawAsm_stopSum_nonneg (eps := eps) fun j => (hg j).le
    positivity
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨le_rfl, (tMix_pos A θσ hθσ).le⟩
  have hmt := momClass_mix hθ hvlo hθσ hν hσ ht
  have hm0 := momClass_mix hθ hvlo hθσ hν hσ h0
  rw [mixPM_zero] at hm0
  have hvt : 0 ≤ lawVar (mixPM ν σ t) := (by positivity : (0 : ℝ) ≤ vlo / 2).trans hmt.var_ge
  have hv0 : 0 ≤ lawVar ν := (by positivity : (0 : ℝ) ≤ vlo / 2).trans hm0.var_ge
  have hte : ∀ (ρ : ProbabilityMeasure ℝ), (ρ : Measure ℝ) (Iic 0) = 0 → 0 ≤ lawVar ρ →
      (∫ g, testFn (fun _ => (1 : ℝ)) (lawVar ρ * stopSum eps g / eps ^ 2) ∂(iidLaw ρ) =
        pwM1 eps ρ) ∧
      (∫ g, testFn (fun t => 2 * t) (lawVar ρ * stopSum eps g / eps ^ 2) ∂(iidLaw ρ) =
        pwM2 eps ρ) := by
    intro ρ hρ hvρ
    refine ⟨integral_congr_ae ?_, integral_congr_ae ?_⟩
    · filter_upwards [hnn ρ hρ hvρ] with g hg
      rcases hg.eq_or_lt with h | h
      · rw [← h, testFn_nonneg_arg le_rfl]
      · exact testFn_one h
    · filter_upwards [hnn ρ hρ hvρ] with g hg
      rcases hg.eq_or_lt with h | h
      · rw [← h, testFn_nonneg_arg le_rfl]; ring
      · exact testFn_two_mul h
  obtain ⟨e1t, e2t⟩ := hte _ hmt.pos hvt
  obtain ⟨e10, e20⟩ := hte _ hm0.pos hv0
  have h1 := hK' eps heps ν σ hν hσ t ht _ 1 (outTest_one γ' hγ'.le)
  have h2 := hK' eps heps ν σ hν hσ t ht _ (2 / γ') (outTest_two_mul hγ')
  rw [e1t, e10] at h1
  rw [e2t, e20] at h2
  have hδ : 0 ≤ K * eps ^ (-βU) := by positivity
  constructor
  · calc _ ≤ 1 * (K * eps ^ (-βU)) := h1
      _ ≤ (1 + 2 / γ') * K * eps ^ (-βU) := by
          have : 0 ≤ 2 / γ' * (K * eps ^ (-βU)) := by positivity
          nlinarith
  · calc _ ≤ 2 / γ' * (K * eps ^ (-βU)) := h2
      _ ≤ (1 + 2 / γ') * K * eps ^ (-βU) := by nlinarith

end

end PGM
