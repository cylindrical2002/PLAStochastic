import PLAStochastic.Index.CEPS.Jets.Defs
import PLAStochastic.Index.CEPS.Jets.Derivative
import PLAStochastic.Index.CEPS.Jets.LineShift
import PLAStochastic.Index.CEPS.Jets.Transform

/-!
# X8: consistency of the jets with the canonical factor

For a law with density `f` (step `W = 1 - X`, density `f_W(y) = f(1 - y)` in the step class
`(D, θ, v)`) and any canonical domain `dom`:

* `cepsJet_cumulant_eq`: `ψ₀^{(k+2)}(0) = κ_{k+2}(f)` (`ψ₀ = cepsCgf ρW`);
* `cepsJet_contour_eq`: there is `r > 0` (depending on `dom`) such that if
  `∫ |f - f_Λ| ≤ r` and `f ∈ CepsSobolevClass N η` (`η > 0`), then for `j + 2 ≤ N`
  `∂_q^n ∂_ζ^m ∂_t^j (dom.canonL ρW)(0; 0, 0) = cepsJet f (cepsJetCode (inr (j, m, n)))`
  (real drift `t` first, then `ζ`, then `q`, as in WP3's mixed bounds).

Route: root removal on `dom`'s line (`canonL_eq_cepsRootFreeL`), the derivative formula of the
root-free factor (`iteratedDeriv_cepsRootFreeL`, separation and log bounds from C-1), the line
shift from `c₀(dom)` to the jet line `c_*` (`cepsContourJetC_eq_of_strip`; on the strip `Re F̃` is
bounded below by C-1 for `dom` when `c_* ≤ c₀` and by C-1 for `Λ` plus `L¹`-closeness otherwise),
and realness (`cepsContourJetC_eq_ofReal_re`).

`cepsJetLaw_eq_cepsJet`: the law version agrees with the density version.
-/

noncomputable section

open MeasureTheory Complex Set Filter Topology
open PGM.WienerHopf

namespace PGM

/-! ### The law version -/

theorem cepsLawDensity_ae_eq {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x)) :
    cepsLawDensity ν =ᵐ[volume] f := by
  have h := Measure.rnDeriv_withDensity (volume : Measure ℝ) hf.ennreal_ofReal
  rw [← hν] at h
  filter_upwards [h] with x hx
  rw [cepsLawDensity, hx, ENNReal.toReal_ofReal (hf0 x)]

theorem cepsJetAt_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) (i : CepsJetIdx) :
    cepsJetAt f i = cepsJetAt g i := by
  rcases i with k | ⟨j, m, n⟩
  · simp only [cepsJetAt, cepsCumulant, cepsJetMoment_congr_ae h]
  · simp only [cepsJetAt, cepsJetTransform_congr_ae h]

/-- The jet vector of a law is that of any of its densities. -/
theorem cepsJetLaw_eq_cepsJet {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x)) :
    cepsJetLaw ν = cepsJet f := by
  funext i
  exact cepsJetAt_congr_ae (cepsLawDensity_ae_eq hf hf0 hν) _

/-! ### Cumulants -/

/-- **Consistency, cumulants.** `ψ₀^{(k+2)}(0) = κ_{k+2}`. -/
theorem cepsJet_cumulant_eq {ρW : Measure ℝ} {fW f : ℝ → ℝ} {D θ v : ℝ}
    (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) (hfW : ∀ y, fW y = f (1 - y))
    (k : ℕ) : iteratedDeriv (k + 2) (cepsCgf ρW) 0 = (cepsJet f (cepsJetCode (.inl k)) : ℂ) := by
  rw [cepsJet_code]
  exact iteratedDeriv_cepsCgf_zero_eq hW hθ hD hfW (k + 2)

/-! ### Contour jets -/

/-- Nested derivatives at the origin only see a neighbourhood. -/
theorem nested_iteratedDeriv_congr {F G : ℝ → ℂ → ℂ → ℂ} {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c)
    (h : ∀ t : ℝ, |t| < a → ∀ q : ℂ, ‖q‖ < b → ∀ ζ : ℂ, ζ.re < c → F t q ζ = G t q ζ)
    (j m n : ℕ) :
    iteratedDeriv n (fun q : ℂ => iteratedDeriv m (fun ζ : ℂ =>
      iteratedDeriv j (fun t : ℝ => F t q ζ) 0) 0) 0 =
    iteratedDeriv n (fun q : ℂ => iteratedDeriv m (fun ζ : ℂ =>
      iteratedDeriv j (fun t : ℝ => G t q ζ) 0) 0) 0 := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hb] with q hq
  apply Filter.EventuallyEq.iteratedDeriv_eq
  have hU : IsOpen {ζ : ℂ | ζ.re < c} := isOpen_lt continuous_re continuous_const
  filter_upwards [hU.mem_nhds (show (0 : ℂ) ∈ {ζ : ℂ | ζ.re < c} by simpa using hc)] with ζ hζ
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha] with t ht
  exact h t (mem_ball_zero_real_iff.mp ht) q (by rwa [Metric.mem_ball, dist_zero_right] at hq)
    ζ hζ

theorem cepsJetF_sub_cepsJetF (s w₁ w₂ : ℂ) :
    cepsJetF s w₁ - cepsJetF s w₂ = (w₂ - w₁) * ((s ^ 2 - 1) / s ^ 2) := by
  unfold cepsJetF; ring

theorem norm_sq_sub_one_div_sq_le {s : ℂ} {a : ℝ} (ha : 0 < a) (hs : a ≤ s.re) :
    ‖(s ^ 2 - 1) / s ^ 2‖ ≤ 1 + 1 / a ^ 2 := by
  have hsn : a ≤ ‖s‖ := hs.trans (re_le_norm s)
  have hs0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hsn; linarith
  rw [show (s ^ 2 - 1) / s ^ 2 = 1 - 1 / s ^ 2 by field_simp]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_div, norm_one, norm_pow]
  gcongr

variable {D θ v : ℝ}

/-- The radius of `L¹`-closeness to `f_Λ` used by `cepsJet_contour_eq`. -/
def CepsCanonDomain.jetRadius (dom : CepsCanonDomain D θ v) : ℝ :=
  cepsRef.dom.d₀ / (2 * Real.exp cepsJetLine * (1 + 1 / dom.c₀ ^ 2))

theorem CepsCanonDomain.jetRadius_pos (dom : CepsCanonDomain D θ v) : 0 < dom.jetRadius := by
  have := cepsRef.dom.d₀_pos cepsRef.hD
  have := dom.c₀_pos
  unfold CepsCanonDomain.jetRadius
  positivity

theorem integrable_cepsLambdaDensity : Integrable cepsLambdaDensity := by
  obtain ⟨η, hη, hS⟩ := exists_cepsSobolevClass_cepsLambdaDensity 0
  simpa using hS.integrable_iteratedDeriv hη.le (k := 0) le_rfl

/-- `Re F̃ ≥ d` on the strip between the domain line and the jet line. -/
theorem CepsCanonDomain.strip_re_cepsJetF_ge (dom : CepsCanonDomain D θ v) {ρW : Measure ℝ}
    {fW f : ℝ → ℝ} (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
    (hfW : ∀ y, fW y = f (1 - y)) (hneg : ∀ x, x < 0 → f x = 0) (hfi : Integrable f)
    (hclose : ∫ x, |f x - cepsLambdaDensity x| ≤ dom.jetRadius) {s : ℂ}
    (hs1 : min dom.c₀ cepsJetLine ≤ s.re) (hs2 : s.re ≤ max dom.c₀ cepsJetLine) :
    min dom.d₀ (cepsRef.dom.d₀ / 2) ≤ (cepsJetF s (cepsJetTransform f s)).re := by
  have hc := dom.c₀_pos
  have hcs := cepsJetLine_pos
  have hspos : 0 < s.re := lt_of_lt_of_le (lt_min hc hcs) hs1
  rcases le_total cepsJetLine dom.c₀ with hle | hle
  · rw [max_eq_left hle] at hs2
    have h := (dom.re_cepsJetF_ge_of_band hW hθ hD hspos (by linarith)).1
    rw [stepTransform_eq_cepsJetTransform hW hfW] at h
    exact (min_le_left _ _).trans h
  · rw [max_eq_right hle] at hs2
    rw [min_eq_left hle] at hs1
    have h := (cepsRef.dom.re_cepsJetF_ge_of_band cepsRef.hW cepsRef.hθ cepsRef.hD hspos
      (by unfold cepsJetLine at hs2; linarith [cepsRef.dom.c₀_pos])).1
    rw [stepTransform_cepsRefStep] at h
    refine (min_le_right _ _).trans ?_
    have hd0 := cepsRef.dom.d₀_pos cepsRef.hD
    -- closeness of the transforms
    have hsub : cepsJetTransform f s - cepsJetTransform cepsLambdaDensity s =
        cepsJetTransform (fun x => f x - cepsLambdaDensity x) s :=
      (cepsJetTransform_sub hfi integrable_cepsLambdaDensity hneg
        (fun x hx => cepsLambdaDensity_of_nonpos hx.le) hspos.le).symm
    have hT : ‖cepsJetTransform f s - cepsJetTransform cepsLambdaDensity s‖ ≤
        Real.exp cepsJetLine * dom.jetRadius := by
      rw [hsub]
      refine (norm_cepsJetTransform_le (hfi.sub integrable_cepsLambdaDensity)
        (fun x hx => by
          show f x - cepsLambdaDensity x = 0
          rw [hneg x hx, cepsLambdaDensity_of_nonpos hx.le, sub_zero])
        hspos.le).trans ?_
      exact mul_le_mul (Real.exp_le_exp.mpr hs2) hclose (integral_nonneg fun _ => abs_nonneg _)
        (Real.exp_pos _).le
    have hR := norm_sq_sub_one_div_sq_le hc hs1
    have hdiff : ‖cepsJetF s (cepsJetTransform f s) -
        cepsJetF s (cepsJetTransform cepsLambdaDensity s)‖ ≤ cepsRef.dom.d₀ / 2 := by
      rw [cepsJetF_sub_cepsJetF, norm_mul, norm_sub_rev]
      calc ‖cepsJetTransform f s - cepsJetTransform cepsLambdaDensity s‖ *
            ‖(s ^ 2 - 1) / s ^ 2‖
          ≤ Real.exp cepsJetLine * dom.jetRadius * (1 + 1 / dom.c₀ ^ 2) :=
            mul_le_mul hT hR (norm_nonneg _) (by have := dom.jetRadius_pos; positivity)
        _ = cepsRef.dom.d₀ / 2 := by
            unfold CepsCanonDomain.jetRadius; field_simp
    have hre := (abs_le.mp (abs_re_le_norm (cepsJetF s (cepsJetTransform f s) -
      cepsJetF s (cepsJetTransform cepsLambdaDensity s)))).1
    rw [sub_re] at hre
    linarith

/-- **Consistency, contour jets.** -/
theorem cepsJet_contour_eq (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D) :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {N : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) → 0 < η →
      CepsSobolevClass N η f → ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ j m n : ℕ, j + 2 ≤ N →
        iteratedDeriv n (fun q : ℂ => iteratedDeriv m (fun ζ : ℂ =>
          iteratedDeriv j (fun t : ℝ => dom.canonL ρW t q ζ) 0) 0) 0 =
        (cepsJet f (cepsJetCode (.inr (j, m, n))) : ℂ) := by
  refine ⟨dom.jetRadius, dom.jetRadius_pos, ?_⟩
  intro ρW fW f N η hW hfW hneg hη hfS hclose j m n hj
  have hc := dom.c₀_pos
  have hcs := cepsJetLine_pos
  have hM : ∀ s, stepTransform ρW s = cepsJetTransform f s := stepTransform_eq_cepsJetTransform hW hfW
  have hMf : stepTransform ρW = cepsJetTransform f := funext hM
  have hfi : Integrable f := by simpa using hfS.integrable_iteratedDeriv hη.le (k := 0) (Nat.zero_le _)
  have hxf : Integrable fun x => x * f x := by
    have h1 := integrable_pow_mul_of_sobolev hfS hη 1
    refine (hfi.sub h1).congr (ae_of_all _ fun x => ?_)
    show f x - (1 - x) ^ 1 * f x = x * f x
    ring
  -- step 1: root removal
  rw [nested_iteratedDeriv_congr (G := fun t q ζ => cepsRootFreeL dom.c₀ (stepTransform ρW) t q ζ)
    dom.μ₀_pos dom.q₀_pos hc (fun t ht q hq ζ hζ =>
      dom.canonL_eq_cepsRootFreeL hW hθ hD ht.le hq.le hζ) j m n]
  -- step 2: the derivative formula on the domain line
  have hline : ∀ y : ℝ, ((dom.c₀ : ℂ) + y * I).re = dom.c₀ := fun y => by simp
  set K := 2 ^ N * Real.exp dom.c₀ * cepsSobolev N η f with hKdef
  have hK : 0 ≤ K := by have := cepsSobolev_nonneg N η f; positivity
  have hdec : ∀ y : ℝ, (1 + ‖(dom.c₀ : ℂ) + y * I‖) ^ N *
      ‖stepTransform ρW (dom.c₀ + y * I)‖ ≤ K := by
    intro y
    rw [hM]
    have := norm_cepsJetTransform_le_sobolev hfS hη.le hneg (s := (dom.c₀ : ℂ) + y * I)
      (by rw [hline]; exact hc.le)
    rwa [hline] at this
  have hTc : Continuous fun y : ℝ => stepTransform ρW (dom.c₀ + y * I) := by
    simp only [hM]
    exact (continuousOn_cepsJetTransform hfi hneg).comp_continuous (by fun_prop)
      (fun y => by simp only [Set.mem_ofPred_eq, hline]; exact hc.le)
  have hsep : ∀ y : ℝ, ∀ t : ℝ, |t| < dom.μ₀ → ∀ q : ℂ, ‖q‖ < dom.q₀ →
      min dom.g (cepsVarLo D * dom.c₀ ^ 2 / 32) ≤
        ‖1 - cexp (t * (dom.c₀ + y * I) - q) * stepTransform ρW (dom.c₀ + y * I)‖ := by
    intro y t ht q hq
    have ht' : ‖(t : ℂ)‖ ≤ dom.μ₀ := by rw [norm_real, Real.norm_eq_abs]; exact ht.le
    have h := dom.norm_cepsD_ge hW hθ hD (μ := t) (q := q) (ζ := (dom.c₀ : ℂ) + y * I) ht'
      (by simp [dom.η_pos.le]) hq.le (by rw [hline, abs_of_pos hc]) (by rw [hline, abs_of_pos hc]; linarith)
    rwa [cepsD, ← CepsCanonDomain.cexp_mul_sub] at h
  have hδ : 0 < min dom.g (cepsVarLo D * dom.c₀ ^ 2 / 32) :=
    lt_min dom.g_pos (by have := cepsVarLo_pos hD; positivity)
  have hslit : ∀ y : ℝ, ∀ t : ℝ, |t| < dom.μ₀ → ∀ q : ℂ, ‖q‖ < dom.q₀ →
      cepsJetF (dom.c₀ + y * I) (cexp (t * (dom.c₀ + y * I) - q) *
        stepTransform ρW (dom.c₀ + y * I)) ∈ slitPlane := fun y t ht q hq =>
    (dom.log_cepsJetF_eq hW hθ hD ht.le hq.le y).2
  set K₁ := |dom.CL| + 9 * dom.c₀ / 8 with hK₁def
  have hK₁ : 0 ≤ K₁ := by positivity
  have hlog : ∀ y : ℝ, ∀ t : ℝ, |t| < dom.μ₀ → ∀ q : ℂ, ‖q‖ < dom.q₀ →
      ‖Complex.log (cepsJetF (dom.c₀ + y * I) (cexp (t * (dom.c₀ + y * I) - q) *
        stepTransform ρW (dom.c₀ + y * I)))‖ ≤
        K₁ * (‖stepTransform ρW (dom.c₀ + y * I)‖ + ‖(dom.c₀ : ℂ) + y * I‖⁻¹) := by
    intro y t ht q hq
    have ht' : ‖(t : ℂ)‖ ≤ dom.μ₀ := by rw [norm_real, Real.norm_eq_abs]; exact ht.le
    rw [(dom.log_cepsJetF_eq hW hθ hD ht.le hq.le y).1]
    have h1 := dom.norm_log_cepsF_le hW hθ hD (γ := 1) (by norm_num) le_rfl ht'
      (by simp [dom.η_pos.le]) hq.le (ζ := (dom.c₀ : ℂ) + y * I)
      (by rw [hline, abs_of_pos hc]) (by rw [hline, abs_of_pos hc]; linarith)
    have h2 := (dom.quadQuot_facts hW hθ hD ht.le hq.le (s := (dom.c₀ : ℂ) + y * I)
      (by rw [hline])).2
    have hM0 := norm_nonneg (stepTransform ρW ((dom.c₀ : ℂ) + y * I))
    have hs0 := inv_nonneg.mpr (norm_nonneg ((dom.c₀ : ℂ) + y * I))
    calc ‖Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) t q (dom.c₀ + y * I)) +
          Complex.log (cepsQuad D θ ρW t q (dom.c₀ + y * I) / (dom.c₀ + y * I) ^ 2)‖
        ≤ dom.CL * (‖stepTransform ρW (dom.c₀ + y * I)‖ + 1 / ‖(dom.c₀ : ℂ) + y * I‖) +
          9 * dom.c₀ / 8 / ‖(dom.c₀ : ℂ) + y * I‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ |dom.CL| * (‖stepTransform ρW (dom.c₀ + y * I)‖ + ‖(dom.c₀ : ℂ) + y * I‖⁻¹) +
          9 * dom.c₀ / 8 * ‖(dom.c₀ : ℂ) + y * I‖⁻¹ := by
          rw [one_div, div_eq_mul_inv]
          gcongr
          exact le_abs_self _
      _ ≤ K₁ * (‖stepTransform ρW (dom.c₀ + y * I)‖ + ‖(dom.c₀ : ℂ) + y * I‖⁻¹) := by
          rw [hK₁def]; nlinarith
  rw [iteratedDeriv_cepsRootFreeL hc hδ hK hK₁ dom.μ₀_pos dom.q₀_pos hTc hdec hsep hslit hlog
    j m n hj, hMf]
  -- step 3: shift to the jet line
  have hstrip := fun {s : ℂ} (h1 : min dom.c₀ cepsJetLine ≤ s.re)
      (h2 : s.re ≤ max dom.c₀ cepsJetLine) =>
    dom.strip_re_cepsJetF_ge hW hθ hD hfW hneg hfi hclose h1 h2
  have hd : 0 < min dom.d₀ (cepsRef.dom.d₀ / 2) :=
    lt_min (dom.d₀_pos hD) (by have := cepsRef.dom.d₀_pos cepsRef.hD; positivity)
  have hshift : cepsContourJetC (min dom.c₀ cepsJetLine) (cepsJetTransform f) j m n =
      cepsContourJetC (max dom.c₀ cepsJetLine) (cepsJetTransform f) j m n := by
    refine cepsContourJetC_eq_of_strip (lt_min hc hcs) (min_le_max) hd
      (K := 2 ^ N * Real.exp (max dom.c₀ cepsJetLine) * cepsSobolev N η f)
      (fun s hs => differentiableAt_cepsJetTransform hfi hxf hneg
        (lt_of_lt_of_le (lt_min hc hcs) hs.1))
      (fun s hs => hstrip hs.1 hs.2) (fun s hs => ?_) j m n hj
    have hs0 : 0 ≤ s.re := (lt_min hc hcs).le.trans hs.1
    refine (norm_cepsJetTransform_le_sobolev hfS hη.le hneg hs0).trans ?_
    have := cepsSobolev_nonneg N η f
    gcongr
    exact hs.2
  have hlineq : cepsContourJetC dom.c₀ (cepsJetTransform f) j m n =
      cepsContourJetC cepsJetLine (cepsJetTransform f) j m n := by
    rcases le_total dom.c₀ cepsJetLine with hle | hle
    · rwa [min_eq_left hle, max_eq_right hle] at hshift
    · rw [min_eq_right hle, max_eq_left hle] at hshift
      exact hshift.symm
  rw [hlineq]
  -- step 4: realness
  have hjl : ∀ y : ℝ, ((cepsJetLine : ℂ) + y * I).re = cepsJetLine := fun y => by simp
  rw [cepsContourJetC_eq_ofReal_re (fun y => ?_) (fun y => ?_) j m n, cepsJet_code]
  · rfl
  · rw [show (cepsJetLine : ℂ) + -(y : ℂ) * I = (starRingEnd ℂ) ((cepsJetLine : ℂ) + y * I) by
      apply Complex.ext <;> simp]
    exact cepsJetTransform_conj f _
  · refine mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le hd (hstrip ?_ ?_)))
    · rw [hjl]; exact min_le_right _ _
    · rw [hjl]; exact le_max_right _ _

end PGM
