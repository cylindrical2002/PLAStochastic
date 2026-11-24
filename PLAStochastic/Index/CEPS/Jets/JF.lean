import PLAStochastic.Index.CEPS.Jets.Consistency
import PLAStochastic.Index.CEPS.Jets.Compose
import PLAStochastic.Index.CEPS.Jets.ContourBounds
import PLAStochastic.Index.CEPS.Jets.Family

/-!
# X8: the interface JF

Along every family with `CepsFamilyExpansion ν m η P g` (and eventually regular), each jet of
`ν ε` has an expansion of order `P` in `ε⁻¹` whose `n`-th coefficient is `cepsJetCoeff i n g`:

* cumulants (`m = 0`): the moments are linear in the density, so the moment series of the family
  are `M_k(f_Λ) + ∑ h^n M_k(g_n)` up to `O(h^{P+1})`; the cumulant recursion is a ring operation
  (`cepsCumulant_hasSeriesExpansion`);
* contour jets `(j, m, l)` (`m = j + 2`): on the jet line the transforms expand as
  `M^{f_ε} = M^Λ + ∑ h^p M^{g_p} + O(h^{P+1} (1 + |s|)^{-(j+2)})` (integration by parts; the
  coefficients vanish on the negative half-line), the integrands are holomorphic in the transform
  value on a disc of common radius (`cepsContour_integrand_data`), and
  `hasInverseExpansion_re_integral_comp` gives the expansion with the Taylor coefficients of the
  complexified family.

`cepsJF_of_eq`: any `CepsJetData` with `jet = cepsJetLaw` and `jetCoeff = cepsJetCoeff`
satisfies `CepsJF`.
-/

noncomputable section

open MeasureTheory Complex Set Filter Topology

namespace PGM

theorem HasInverseExpansionAtOrder.of_eq_on {f g : ℝ → ℝ} {a : ℕ → ℝ} {P : ℕ} {e₀ : ℝ}
    (h : HasInverseExpansionAtOrder f a P) (he : ∀ eps, e₀ ≤ eps → g eps = f eps) :
    HasInverseExpansionAtOrder g a P := by
  obtain ⟨K, e1, hK⟩ := h
  refine ⟨K, max e₀ e1, fun eps heps => ?_⟩
  rw [he eps ((le_max_left _ _).trans heps)]
  exact hK eps ((le_max_right _ _).trans heps)

theorem CepsSobolevClass.integrable_self {m : ℕ} {η : ℝ} {φ : ℝ → ℝ}
    (hφ : CepsSobolevClass m η φ) (hη : 0 ≤ η) : Integrable φ := by
  simpa using hφ.integrable_iteratedDeriv hη (k := 0) (Nat.zero_le _)

theorem sum_range_succ_eq_add_sum_Icc (a : ℕ → ℝ) (P : ℕ) :
    ∑ n ∈ Finset.range (P + 1), a n = a 0 + ∑ n ∈ Finset.Icc 1 P, a n := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ P + 1)]
    ring

/-! ### Linear algebra of the remainder -/

section Remainder

variable {f₁ : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {P : ℕ} {e : ℝ}

theorem cepsJetTransform_remainder (hf₁ : Integrable f₁) (hneg₁ : ∀ x, x < 0 → f₁ x = 0)
    (hg : ∀ n ∈ Finset.Icc 1 P, Integrable (g n))
    (hgneg : ∀ n ∈ Finset.Icc 1 P, ∀ x, x < 0 → g n x = 0) {s : ℂ} (hs : 0 ≤ s.re) :
    cepsJetTransform (fun x => f₁ x - cepsLambdaDensity x -
        ∑ n ∈ Finset.Icc 1 P, e ^ n * g n x) s =
      cepsJetTransform f₁ s - cepsJetTransform cepsLambdaDensity s -
        ∑ n ∈ Finset.Icc 1 P, ((e : ℂ)) ^ n * cepsJetTransform (g n) s := by
  have hΛneg : ∀ x, x < 0 → cepsLambdaDensity x = 0 := fun x hx =>
    cepsLambdaDensity_of_nonpos hx.le
  have hS : Integrable fun x => ∑ n ∈ Finset.Icc 1 P, e ^ n * g n x :=
    integrable_finsetSum _ fun n hn => (hg n hn).const_mul _
  have hSneg : ∀ x, x < 0 → ∑ n ∈ Finset.Icc 1 P, e ^ n * g n x = 0 := fun x hx =>
    Finset.sum_eq_zero fun n hn => by rw [hgneg n hn x hx, mul_zero]
  rw [cepsJetTransform_sub (f := fun x => f₁ x - cepsLambdaDensity x)
    (hf₁.sub integrable_cepsLambdaDensity) hS
    (fun x hx => by rw [hneg₁ x hx, hΛneg x hx, sub_zero]) hSneg hs,
    cepsJetTransform_sub hf₁ integrable_cepsLambdaDensity hneg₁ hΛneg hs,
    cepsJetTransform_sum _ (fun n => e ^ n) g hg hgneg hs]
  push_cast
  rfl

theorem cepsJetMoment_remainder {η : ℝ} (hη : 0 < η) {m : ℕ}
    (hf₁ : CepsSobolevClass m η f₁) (hΛ : CepsSobolevClass m η cepsLambdaDensity)
    (hg : ∀ n ∈ Finset.Icc 1 P, CepsSobolevClass m η (g n)) (k : ℕ) :
    cepsJetMoment (fun x => f₁ x - cepsLambdaDensity x -
        ∑ n ∈ Finset.Icc 1 P, e ^ n * g n x) k =
      cepsJetMoment f₁ k - cepsJetMoment cepsLambdaDensity k -
        ∑ n ∈ Finset.Icc 1 P, e ^ n * cepsJetMoment (g n) k := by
  have h1 := integrable_pow_mul_of_sobolev hf₁ hη k
  have h2 := integrable_pow_mul_of_sobolev hΛ hη k
  have hgi : ∀ n ∈ Finset.Icc 1 P, Integrable fun x => (1 - x) ^ k * g n x := fun n hn =>
    integrable_pow_mul_of_sobolev (hg n hn) hη k
  have hS : Integrable fun x => (1 - x) ^ k * ∑ n ∈ Finset.Icc 1 P, e ^ n * g n x := by
    refine (integrable_finsetSum _ fun n hn => (hgi n hn).const_mul (e ^ n)).congr
      (ae_of_all _ fun x => ?_)
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [cepsJetMoment_sub (f := fun x => f₁ x - cepsLambdaDensity x)
      ((h1.sub h2).congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)) hS,
    cepsJetMoment_sub h1 h2, cepsJetMoment_sum _ (fun n => e ^ n) g hgi]

end Remainder

/-! ### Cumulant jets -/

theorem cepsJetLaw_expansion_cumulant (k P : ℕ) {ν : ℝ → ProbabilityMeasure ℝ}
    {g : ℕ → ℝ → ℝ} {η : ℝ} (hreg : CepsEventuallyRegular ν) (hη : 0 < η)
    (hfam : CepsFamilyExpansion ν 0 η P g) :
    HasInverseExpansionAtOrder (fun eps => cepsJetLaw (ν eps) (cepsJetCode (.inl k)))
      (fun n => cepsJetCoeff (cepsJetCode (.inl k)) n g) P := by
  obtain ⟨f, K, e₀, he₀, hK, hf⟩ := hfam.remainder_data hreg
  have hmom : ∀ k', 1 ≤ k' → k' ≤ k + 2 →
      HasSeriesExpansionAtOrder (fun eps => cepsJetMoment (f eps) k') (cepsMomentSeries g k') P := by
    intro k' _ _
    obtain ⟨C, hC, hCb⟩ := abs_cepsJetMoment_le_sobolev 0 hη k'
    refine ⟨C * K, e₀, fun eps heps => ?_⟩
    obtain ⟨-, -, hfS, -, hRS, hRb⟩ := hf eps heps
    have hpoly : inversePolynomial (fun n => PowerSeries.coeff n (cepsMomentSeries g k')) P eps =
        cepsJetMoment cepsLambdaDensity k' +
          ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * cepsJetMoment (g n) k' := by
      rw [inversePolynomial, sum_range_succ_eq_add_sum_Icc]
      simp only [cepsMomentSeries, PowerSeries.coeff_mk, if_true, pow_zero, mul_one]
      congr 1
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_neg (by have := (Finset.mem_Icc.mp hn).1; omega)]
      ring
    rw [hpoly]
    have hrem := cepsJetMoment_remainder (e := eps⁻¹) hη hfS hfam.reference hfam.coeff k'
    have hb := hCb _ hRS
    rw [hrem] at hb
    calc |cepsJetMoment (f eps) k' - (cepsJetMoment cepsLambdaDensity k' +
          ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * cepsJetMoment (g n) k')|
        = |cepsJetMoment (f eps) k' - cepsJetMoment cepsLambdaDensity k' -
          ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * cepsJetMoment (g n) k'| := by ring_nf
      _ ≤ C * cepsSobolev 0 η (fun x => f eps x - cepsLambdaDensity x -
          ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x) := hb
      _ ≤ C * (K * (eps⁻¹) ^ (P + 1)) := mul_le_mul_of_nonneg_left hRb hC
      _ = C * K * (eps⁻¹) ^ (P + 1) := by ring
  have hcum := cepsCumulant_hasSeriesExpansion hmom (k + 2) le_rfl
  refine HasInverseExpansionAtOrder.of_eq_on (f := fun eps => cepsCumulant (f eps) (k + 2))
    (e₀ := e₀) ?_ fun eps heps => ?_
  · have e : (fun n => cepsJetCoeff (cepsJetCode (.inl k)) n g) =
        fun n => PowerSeries.coeff n (cepsCumSeries g (k + 2)) := by
      funext n
      rw [cepsJetCoeff, ofNat_cepsJetCode]
      rfl
    rw [e]
    exact hcum
  · obtain ⟨h0, -, hfS, hν, -, -⟩ := hf eps heps
    rw [cepsJetLaw_eq_cepsJet hfS.continuous.measurable h0 hν, cepsJet_code]
    rfl

/-! ### Contour jets -/

theorem one_add_pow_div_le {c y : ℝ} (j : ℕ) :
    (1 + ‖(c : ℂ) + y * I‖) ^ j * ((1 + ‖(c : ℂ) + y * I‖) ^ (j + 2))⁻¹ ≤ (1 + y ^ 2)⁻¹ := by
  set r := ‖(c : ℂ) + y * I‖
  have hr : 0 ≤ r := norm_nonneg _
  have hy : |y| ≤ r := norm_vline_ge c y
  have hy2 : y ^ 2 ≤ r ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have h1 : 1 + y ^ 2 ≤ (1 + r) ^ 2 := by nlinarith
  rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  exact inv_anti₀ (by positivity) h1

theorem cepsJetLaw_expansion_contour (j m l P : ℕ) {ν : ℝ → ProbabilityMeasure ℝ}
    {g : ℕ → ℝ → ℝ} {η : ℝ} (hreg : CepsEventuallyRegular ν) (hη : 0 < η)
    (hfam : CepsFamilyExpansion ν (j + 2) η P g) :
    HasInverseExpansionAtOrder (fun eps => cepsJetLaw (ν eps) (cepsJetCode (.inr (j, m, l))))
      (fun n => cepsJetCoeff (cepsJetCode (.inr (j, m, l))) n g) P := by
  obtain ⟨ρ, C, hρ, hC, hz₀c, hGd, hGc, hA, hG0⟩ := cepsContour_integrand_data j m l
  obtain ⟨f, K, e₀, he₀, hK, hf⟩ := hfam.remainder_data hreg
  have hgneg := hfam.coeff_eq_zero_of_neg hreg
  set c := cepsJetLine with hcdef
  have hc := cepsJetLine_pos
  have hline : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := fun y => by simp
  set N := j + 2 with hN
  set w : ℝ → ℝ := fun y => ((1 + ‖(c : ℂ) + y * I‖) ^ N)⁻¹ with hw
  have hw0 : ∀ y, 0 ≤ w y := fun y => by positivity
  have hw1 : ∀ y, w y ≤ 1 := fun y =>
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg ((c : ℂ) + y * I)]))
  -- decay of transforms of Sobolev functions vanishing on the negative half-line
  have hdecay : ∀ φ : ℝ → ℝ, CepsSobolevClass N η φ → (∀ x, x < 0 → φ x = 0) → ∀ y : ℝ,
      ‖cepsJetTransform φ (c + y * I)‖ ≤ 2 ^ N * Real.exp c * cepsSobolev N η φ * w y := by
    intro φ hφ hφneg y
    have h := norm_cepsJetTransform_le_sobolev hφ hη.le hφneg (s := (c : ℂ) + y * I)
      (by rw [hline]; exact hc.le)
    rw [hline] at h
    rw [hw, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  have hcontT : ∀ φ : ℝ → ℝ, Integrable φ → (∀ x, x < 0 → φ x = 0) →
      Continuous fun y : ℝ => cepsJetTransform φ (c + y * I) := fun φ hφ hφneg =>
    (continuousOn_cepsJetTransform hφ hφneg).comp_continuous (by fun_prop)
      (fun y => by simp only [Set.mem_ofPred_eq, hline]; exact hc.le)
  have hgS : ∀ p ∈ Finset.Icc 1 P, CepsSobolevClass N η (g p) := hfam.coeff
  set Kd := ∑ p ∈ Finset.Icc 1 P, 2 ^ N * Real.exp c * cepsSobolev N η (g p) with hKd
  have hcomp := hasInverseExpansion_re_integral_comp (G := fun y w =>
      cepsJetIntegrand j m l (c + y * I) w)
    (z₀ := fun y => cepsJetTransform cepsLambdaDensity (c + y * I))
    (d := fun p y => cepsJetTransform (g p) (c + y * I))
    (Z := fun eps y => cepsJetTransform (f eps) (c + y * I))
    (A := fun y => C * (1 + ‖(c : ℂ) + y * I‖) ^ j) (w := w) (K_d := Kd)
    (K_R := 2 ^ N * Real.exp c * K) (ε₀ := e₀) (P := P)
    ((m.factorial : ℂ) * (2 * Real.pi : ℂ)⁻¹) (cepsJetCorr j m l) hρ hGd hGc hz₀c hA ?_ hw0 hw1
    hG0 ?_ ?_ ?_ ?_
  · have h := hcomp.of_eq_on
      (g := fun eps => cepsJetLaw (ν eps) (cepsJetCode (.inr (j, m, l)))) (e₀ := e₀)
      (fun eps heps => by
        obtain ⟨h0, -, hfS, hν, -, -⟩ := hf eps heps
        rw [cepsJetLaw_eq_cepsJet hfS.continuous.measurable h0 hν, cepsJet_code]
        rfl)
    · have e : (fun n => cepsJetCoeff (cepsJetCode (.inr (j, m, l))) n g) =
          fun n => (iteratedDeriv n (fun h : ℂ =>
            (m.factorial : ℂ) * (2 * Real.pi : ℂ)⁻¹ * (∫ y : ℝ, cepsJetIntegrand j m l (c + y * I)
              (cepsJetTransform cepsLambdaDensity (c + y * I) +
                ∑ p ∈ Finset.Icc 1 n, h ^ p * cepsJetTransform (g p) (c + y * I))) +
              cepsJetCorr j m l) 0 / (n.factorial : ℂ)).re := by
        funext n
        rw [cepsJetCoeff, ofNat_cepsJetCode]
        rfl
      rw [e]
      exact h
  · -- integrability of `A w`
    refine (integrable_inv_one_add_sq.const_mul C).mono'
      (Continuous.aestronglyMeasurable (by
        refine (continuous_const.mul ((by fun_prop : Continuous fun y : ℝ =>
          1 + ‖(c : ℂ) + y * I‖).pow j)).mul ?_
        exact ((by fun_prop : Continuous fun y : ℝ => 1 + ‖(c : ℂ) + y * I‖).pow N).inv₀
          fun y => (by positivity : (0 : ℝ) < (1 + ‖(c : ℂ) + y * I‖) ^ N).ne'))
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (hw0 y)), hw, mul_assoc]
    exact mul_le_mul_of_nonneg_left (one_add_pow_div_le j) hC
  · intro p hp
    exact hcontT (g p) ((hgS p hp).integrable_self hη.le) (hgneg p hp)
  · intro p hp y
    refine (hdecay (g p) (hgS p hp) (hgneg p hp) y).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hw0 y)
    exact Finset.single_le_sum (f := fun p => 2 ^ N * Real.exp c * cepsSobolev N η (g p))
      (fun p _ => by have := cepsSobolev_nonneg N η (g p); positivity) hp
  · intro eps heps
    obtain ⟨-, hneg, hfS, -, -, -⟩ := hf eps heps
    exact hcontT (f eps) (hfS.integrable_self hη.le) hneg
  · intro eps heps y
    obtain ⟨-, hneg, hfS, -, hRS, hRb⟩ := hf eps heps
    have hs : 0 ≤ ((c : ℂ) + y * I).re := by rw [hline]; exact hc.le
    have hrem := cepsJetTransform_remainder (e := eps⁻¹) (hfS.integrable_self hη.le) hneg
      (fun n hn => (hgS n hn).integrable_self hη.le) hgneg hs
    have hRneg : ∀ x, x < 0 → f eps x - cepsLambdaDensity x -
        ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x = 0 := fun x hx => by
      rw [hneg x hx, cepsLambdaDensity_of_nonpos hx.le,
        Finset.sum_eq_zero fun n hn => by rw [hgneg n hn x hx, mul_zero]]
      ring
    have hb := hdecay _ hRS hRneg y
    rw [hrem] at hb
    refine hb.trans ?_
    have := hw0 y
    have : 0 ≤ 2 ^ N * Real.exp c := by positivity
    calc 2 ^ N * Real.exp c * cepsSobolev N η (fun x => f eps x - cepsLambdaDensity x -
          ∑ n ∈ Finset.Icc 1 P, (eps⁻¹) ^ n * g n x) * w y
        ≤ 2 ^ N * Real.exp c * (K * (eps⁻¹) ^ (P + 1)) * w y := by gcongr
      _ = 2 ^ N * Real.exp c * K * (eps⁻¹) ^ (P + 1) * w y := by ring

/-! ### JF -/

/-- **JF, expansion.** -/
theorem cepsJetLaw_expansion (i P : ℕ) : ∃ m : ℕ, ∀ (ν : ℝ → ProbabilityMeasure ℝ)
    (g : ℕ → ℝ → ℝ) (η : ℝ), CepsEventuallyRegular ν → 0 < η → CepsFamilyExpansion ν m η P g →
      HasInverseExpansionAtOrder (fun eps => cepsJetLaw (ν eps) i)
        (fun n => cepsJetCoeff i n g) P := by
  obtain ⟨idx, rfl⟩ : ∃ idx : CepsJetIdx, i = cepsJetCode idx :=
    ⟨Denumerable.ofNat CepsJetIdx i, (Denumerable.encode_ofNat i).symm⟩
  rcases idx with k | ⟨j, m, l⟩
  · exact ⟨0, fun ν g η hreg hη hfam => cepsJetLaw_expansion_cumulant k P hreg hη hfam⟩
  · exact ⟨j + 2, fun ν g η hreg hη hfam => cepsJetLaw_expansion_contour j m l P hreg hη hfam⟩

/-- **JF.** Jet data built from `cepsJetLaw` and `cepsJetCoeff` satisfy the interface `CepsJF`. -/
theorem cepsJF_of_eq {J : CepsJetData} (hjet : J.jet = cepsJetLaw)
    (hcoeff : J.jetCoeff = cepsJetCoeff) : CepsJF J where
  triangular i n g g' h := by rw [hcoeff]; exact cepsJetCoeff_triangular i n g g' h
  expansion i P := by
    obtain ⟨m, hm⟩ := cepsJetLaw_expansion i P
    refine ⟨m, fun ν g η hreg hη hfam => ?_⟩
    rw [hjet, hcoeff]
    exact hm ν g η hreg hη hfam

end PGM
