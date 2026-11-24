import PLAStochastic.Swing.Ladder.Law.StrongNonlattice

/-! # Uniform bounds for the parameterised ladder law

The common Lebesgue component on `[1,2]` gives three estimates that do not
depend on the drift beyond the interval `[0,M]`:

* the Laplace transform at `-1` is bounded away from `1`, hence the renewal
  measure is uniformly finite on bounded intervals;
* the ladder mean is bounded below by the component mass;
* together with the compact exponential tail this bounds every fixed
  polynomial moment uniformly.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- `1 - e^{-λ} ≥ λ/2` on the unit interval. -/
theorem one_sub_exp_neg_ge_half {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    lam/2 ≤ 1 - Real.exp (-lam) := by
  have hexp : 1 + lam ≤ Real.exp lam := by
    have := Real.add_one_le_exp lam
    linarith
  have hpos : (0 : ℝ) < 1 + lam := by linarith
  have hinv : Real.exp (-lam) ≤ 1/(1+lam) := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos lam), one_div]
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  have hfrac : 1/(1+lam) ≤ 1 - lam/2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

/-- The Laplace transform of a positive law with a common `[1,2]` component is
bounded away from one, uniformly in everything but the component mass. -/
theorem ladderLaplace_le_of_minorization {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {c lam : ℝ} (hc0 : 0 ≤ c) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hpos : ν (Iic 0) = 0)
    (hmin : ENNReal.ofReal c • volume.restrict (Icc (1 : ℝ) 2) ≤ ν) :
    ladderLaplace ν lam ≤ ENNReal.ofReal (1-c*lam/2) := by
  set κ : Measure ℝ := ENNReal.ofReal c • volume.restrict (Icc (1 : ℝ) 2) with hκdef
  have hvol : volume (Icc (1 : ℝ) 2) = 1 := by
    rw [Real.volume_Icc]; norm_num
  have hκuniv : κ univ = ENNReal.ofReal c := by
    rw [hκdef, Measure.smul_apply, Measure.restrict_apply_univ, hvol, smul_eq_mul, mul_one]
  have hκfin : IsFiniteMeasure κ := ⟨by rw [hκuniv]; exact ENNReal.ofReal_lt_top⟩
  have hc1 : c ≤ 1 := by
    have h : κ univ ≤ ν univ := hmin univ
    rw [hκuniv, measure_univ] at h
    exact ENNReal.ofReal_le_one.mp h
  set ρ : Measure ℝ := ν - κ with hρdef
  have hsum : ρ + κ = ν := Measure.sub_add_cancel_of_le hmin
  have hρle : ρ ≤ ν := by
    rw [hρdef]
    exact Measure.sub_le
  have hρuniv : ρ univ = ENNReal.ofReal (1-c) := by
    rw [hρdef, Measure.sub_apply MeasurableSet.univ hmin, measure_univ, hκuniv,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hc0]
  have hρpos : ρ (Iic 0) = 0 := le_antisymm (hpos ▸ hρle (Iic 0)) zero_le
  have hρae : ∀ᵐ x ∂ρ, ENNReal.ofReal (Real.exp (-lam*x)) ≤ 1 := by
    have hset : ∀ᵐ x ∂ρ, x ∉ Iic (0 : ℝ) := by
      rw [ae_iff]
      convert hρpos using 2
      ext x
      simp
    filter_upwards [hset] with x hx
    have hx0 : 0 < x := by simpa using hx
    refine ENNReal.ofReal_le_one.mpr ?_
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith
  have hρbound : (∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂ρ) ≤ ENNReal.ofReal (1-c) := by
    calc (∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂ρ) ≤ ∫⁻ _x : ℝ, 1 ∂ρ :=
          lintegral_mono_ae hρae
      _ = ρ univ := by simp
      _ = ENNReal.ofReal (1-c) := hρuniv
  have hκbound : (∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂κ) ≤
      ENNReal.ofReal (c*Real.exp (-lam)) := by
    have hpt : ∀ x ∈ Icc (1 : ℝ) 2, ENNReal.ofReal (Real.exp (-lam*x)) ≤
        ENNReal.ofReal (Real.exp (-lam)) := by
      intro x hx
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      nlinarith [hx.1]
    calc (∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂κ)
        = ENNReal.ofReal c * ∫⁻ x in Icc (1 : ℝ) 2, ENNReal.ofReal (Real.exp (-lam*x)) := by
          rw [hκdef, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal c * ∫⁻ _x in Icc (1 : ℝ) 2, ENNReal.ofReal (Real.exp (-lam)) := by
          refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc hpt)
      _ = ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-lam)) := by
          rw [setLIntegral_const, hvol, mul_one]
      _ = ENNReal.ofReal (c*Real.exp (-lam)) := (ENNReal.ofReal_mul hc0).symm
  have hsplit : ladderLaplace ν lam =
      (∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂ρ) +
        ∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂κ := by
    rw [ladderLaplace, ← hsum, lintegral_add_measure]
  have hhalf := one_sub_exp_neg_ge_half hlam0 hlam1
  have hexp0 : 0 ≤ Real.exp (-lam) := (Real.exp_pos _).le
  rw [hsplit]
  calc (∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂ρ) +
        ∫⁻ x, ENNReal.ofReal (Real.exp (-lam*x)) ∂κ
      ≤ ENNReal.ofReal (1-c) + ENNReal.ofReal (c*Real.exp (-lam)) :=
        add_le_add hρbound hκbound
    _ = ENNReal.ofReal (1-c+c*Real.exp (-lam)) := by
        rw [← ENNReal.ofReal_add (by linarith) (by positivity)]
    _ ≤ ENNReal.ofReal (1-c*lam/2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith

/-! ### The mean of a law with a common `[1,2]` component -/

/-- The lintegral form of the ladder mean lower bound. -/
theorem lintegral_ofReal_ge_of_minorization {ν : Measure ℝ} {c : ℝ}
    (hmin : ENNReal.ofReal c • volume.restrict (Icc (1 : ℝ) 2) ≤ ν) :
    ENNReal.ofReal c ≤ ∫⁻ x, ENNReal.ofReal x ∂ν := by
  set κ : Measure ℝ := ENNReal.ofReal c • volume.restrict (Icc (1 : ℝ) 2) with hκdef
  have hvol : volume (Icc (1 : ℝ) 2) = 1 := by
    rw [Real.volume_Icc]; norm_num
  have hlow : ENNReal.ofReal c ≤ ∫⁻ x, ENNReal.ofReal x ∂ν := by
    have hκint : ENNReal.ofReal c ≤ ∫⁻ x, ENNReal.ofReal x ∂κ := by
      have hpt : ∀ x ∈ Icc (1 : ℝ) 2, ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal x :=
        fun x hx => ENNReal.ofReal_le_ofReal hx.1
      calc ENNReal.ofReal c
          = ENNReal.ofReal c * (ENNReal.ofReal (1 : ℝ) * volume (Icc (1 : ℝ) 2)) := by
            simp [hvol]
        _ = ENNReal.ofReal c * ∫⁻ _x in Icc (1 : ℝ) 2, ENNReal.ofReal (1 : ℝ) := by
            rw [setLIntegral_const]
        _ ≤ ENNReal.ofReal c * ∫⁻ x in Icc (1 : ℝ) 2, ENNReal.ofReal x :=
            mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc hpt)
        _ = ∫⁻ x, ENNReal.ofReal x ∂κ := by
            rw [hκdef, lintegral_smul_measure, smul_eq_mul]
    exact hκint.trans (lintegral_mono' hmin le_rfl)
  exact hlow

theorem ladder_mean_ge_of_minorization {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {c : ℝ} (hc0 : 0 ≤ c)
    (hmin : ENNReal.ofReal c • volume.restrict (Icc (1 : ℝ) 2) ≤ ν)
    (hint : Integrable (fun x : ℝ => x) ν) (hnn : 0 ≤ᵐ[ν] fun x : ℝ => x) :
    c ≤ ∫ x, x ∂ν := by
  have hlow : ENNReal.ofReal c ≤ ∫⁻ x, ENNReal.ofReal x ∂ν :=
    lintegral_ofReal_ge_of_minorization hmin
  have heq : (∫ x, x ∂ν) = (∫⁻ x, ENNReal.ofReal x ∂ν).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn measurable_id.aestronglyMeasurable
  have hfin : (∫⁻ x, ENNReal.ofReal x ∂ν) ≠ ⊤ := by
    have h := hint.2
    rw [hasFiniteIntegral_iff_ofReal hnn] at h
    exact h.ne
  rw [heq]
  have := ENNReal.toReal_mono hfin hlow
  rwa [ENNReal.toReal_ofReal hc0] at this

/-! ### The actual Gaussian ladder family -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianPDFReal_std_le_one (y : ℝ) : gaussianPDFReal 0 1 y ≤ 1 := by
  have hpi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2*Real.pi*((1 : ℝ≥0) : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    push_cast
    linarith
  have hexp : Real.exp (-(y-0)^2/(2*((1 : ℝ≥0) : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hsq : (0 : ℝ) ≤ (y-0)^2 := sq_nonneg _
    push_cast
    linarith
  simp only [gaussianPDFReal]
  have hinv : (Real.sqrt (2*Real.pi*((1 : ℝ≥0) : ℝ)))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hsqrt
  calc (Real.sqrt (2*Real.pi*((1 : ℝ≥0) : ℝ)))⁻¹ *
        Real.exp (-(y-0)^2/(2*((1 : ℝ≥0) : ℝ))) ≤ 1 * 1 :=
        mul_le_mul hinv hexp (Real.exp_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem gaussianAscendingLadderCommonDensity_le_one (M : ℝ) :
    gaussianAscendingLadderCommonDensity M ≤ 1 :=
  gaussianPDFReal_std_le_one (M+2)

theorem gaussianAscendingLadderLaw_Iic_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    gaussianAscendingLadderLaw X μ a (Iic 0) = 0 := by
  have hae := gaussianAscendingLadderLaw_positive_ae hX hi hG ha
  rw [ae_iff] at hae
  convert hae using 2
  ext u
  simp

/-- Uniform Laplace bound for the actual ladder law on `(0,M]`. -/
theorem gaussianAscendingLadderLaw_laplace_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a lam : ℝ} (ha : 0 < a) (haM : a ≤ M) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ladderLaplace (gaussianAscendingLadderLaw X μ a) lam ≤
      ENNReal.ofReal (1 - gaussianAscendingLadderCommonDensity M*lam/2) := by
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  exact ladderLaplace_le_of_minorization
    (gaussianAscendingLadderCommonDensity_pos M).le hlam0 hlam1
    (gaussianAscendingLadderLaw_Iic_zero hX hi hG ha)
    (gaussianAscendingLadderLaw_common_minorization hX (hG 0) ha.le haM)

/-- The ladder renewal measure of the actual positive-drift Gaussian walk grows
at most linearly, with a constant uniform over `0 < a ≤ M`.  No renewal theorem
is used: the bound comes from one optimised Laplace transform value. -/
theorem gaussianAscendingLadderRenewal_Icc_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a b : ℝ} (ha : 0 < a) (haM : a ≤ M) (hb : 0 ≤ b) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Icc 0 b) ≤
      ENNReal.ofReal (2*Real.exp 1*(1+b)/gaussianAscendingLadderCommonDensity M) := by
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hc := gaussianAscendingLadderCommonDensity_pos M
  have hc1 := gaussianAscendingLadderCommonDensity_le_one M
  set c := gaussianAscendingLadderCommonDensity M with hcdef
  have hb1 : (0 : ℝ) < 1+b := by linarith
  set lam : ℝ := 1/(1+b) with hlamdef
  have hlam0 : 0 < lam := by
    rw [hlamdef]
    positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one hb1]
    linarith
  have hq0 : (0 : ℝ) ≤ 1 - c*lam/2 := by nlinarith
  have hq1 : 1 - c*lam/2 < 1 := by nlinarith
  have hbound := ladderRenewalMeasure_Icc_le (gaussianAscendingLadderLaw X μ a)
    (b := b) (lam := lam) (q := 1 - c*lam/2) hlam0.le hq0 hq1
    (gaussianAscendingLadderLaw_laplace_le hX hi hG ha haM hlam0.le hlam1)
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hden : 1 - (1 - c*lam/2) = c*lam/2 := by ring
  rw [hden]
  have hexp : Real.exp (lam*b) ≤ Real.exp 1 := by
    refine Real.exp_le_exp.mpr ?_
    rw [hlamdef, div_mul_eq_mul_div, one_mul, div_le_one hb1]
    linarith
  have hpos : (0 : ℝ) < c*lam/2 := by positivity
  rw [div_le_div_iff₀ hpos (by positivity : (0 : ℝ) < c)]
  have hlamval : lam*(1+b) = 1 := by
    rw [hlamdef]
    field_simp
  have hkey : 2*Real.exp 1*(1+b)*(c*lam/2) = Real.exp 1*c*(lam*(1+b)) := by ring
  rw [hkey, hlamval, mul_one]
  exact mul_le_mul_of_nonneg_right hexp hc.le

/-- The ladder mean is bounded below by the common component mass, uniformly
over `δ ≤ a ≤ M`. -/
theorem gaussianAscendingLadderHeight_mean_ge
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) :
    gaussianAscendingLadderCommonDensity M ≤
      ∫ ω, gaussianAscendingLadderHeight X a ω ∂μ := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hHint : Integrable (gaussianAscendingLadderHeight X a) μ :=
    gaussianAscendingLadderHeight_integrable_compact hX hi hG hδ hδa haM
  have hmeas : Measurable (gaussianAscendingLadderHeight X a) :=
    gaussianAscendingLadderHeight_measurable hX a
  have hlaw : (gaussianAscendingLadderLaw X μ a) =
      μ.map (gaussianAscendingLadderHeight X a) := rfl
  have hmap : (∫ x, x ∂(gaussianAscendingLadderLaw X μ a)) =
      ∫ ω, gaussianAscendingLadderHeight X a ω ∂μ :=
    integral_map hmeas.aemeasurable aestronglyMeasurable_id
  have hint' : Integrable (fun x : ℝ => x) (gaussianAscendingLadderLaw X μ a) := by
    rw [hlaw]
    exact (integrable_map_measure aestronglyMeasurable_id hmeas.aemeasurable).mpr hHint
  have hnn : 0 ≤ᵐ[gaussianAscendingLadderLaw X μ a] fun x : ℝ => x := by
    rw [Filter.EventuallyLE, ae_iff]
    have hset : {x : ℝ | ¬ (0 : ℝ) ≤ x} = {x : ℝ | x < 0} := by
      ext x
      simp
    have hpre : (gaussianAscendingLadderHeight X a) ⁻¹' {x : ℝ | x < 0} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact gaussianAscendingLadderHeight_nonneg (X := X) a ω
    show gaussianAscendingLadderLaw X μ a {x : ℝ | ¬ (0 : ℝ) ≤ x} = 0
    have hmsIio : MeasurableSet {x : ℝ | x < 0} := by
      have : {x : ℝ | x < 0} = Iio (0 : ℝ) := by ext x; simp
      rw [this]
      exact measurableSet_Iio
    rw [hset, hlaw, Measure.map_apply hmeas hmsIio, hpre, measure_empty]
  rw [← hmap]
  exact ladder_mean_ge_of_minorization (gaussianAscendingLadderCommonDensity_pos M).le
    (gaussianAscendingLadderLaw_common_minorization hX (hG 0) ha.le haM) hint' hnn

end SwingRepair
