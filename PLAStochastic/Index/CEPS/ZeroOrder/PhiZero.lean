import PLAStochastic.Index.CEPS.ZeroOrder.Limit
import PLAStochastic.Index.CEPS.Glue.Main

/-!
# C-16: the zero-order coefficient is `φ_Λ`

Blueprint C-16 (`research/2026-10-02-lean-ceps/blueprint-CS.md` §5, Prop J item 3) and the
WP11a prescription (`track-WP11a.md` §交接 2): the zero-order output coefficient is the
characteristic function of `Λ`.

* `cepsLambdaChar_bound_of_T1Mid`: `CepsT3.lambdaChar_bound` from any `CepsT1Mid`
  (`Λ` is itself in every input class; let `ε → ∞` in the mid bound);
* `cepsT1Low_phi_zero_on_class`: from any `CepsT1Low J`, `Φ₀(u; J ν) = φ_Λ(u)` on the class;
* `cepsGk_zero_eq_on_class`: on the class, the zero-order normal coefficient is
  `Ĝ₀(iy; J ν) = φ_Λ(−c₀(J ν) y / 4)` (from S-9, C-10 at order `0`, and T5 at order `0`);
* `cepsGkLambda`: the replacement `Ĝ₀(iy; p) := φ_Λ(−c₀(p) y / 4)` for all `p`, which keeps
  `CepsNormalLowExpansion` and `CepsNormalCoeffReg` (`cepsNormalLowExpansion_gkLambda`,
  `cepsNormalCoeffReg_gkLambda`) and makes `Φ₀(u; p) = φ_Λ(u)` for every `p` with
  `c₀(p) ≠ 0` (`cepsLowCoeff_gkLambda_zero`);
* `cepsCsAdjust`: the off-class adjustment `C₀(p) ≠ 0` that keeps `CepsNormalMeanExpansion`
  (`cepsNormalMeanExpansion_adjust`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ## Exponentially small terms vanish -/

theorem tendsto_const_mul_pow_mul_exp_neg {c : ℝ} (hc : 0 < c) (K : ℝ) (p : ℕ) :
    Tendsto (fun eps : ℝ => K * eps ^ p * Real.exp (-c * eps)) atTop (𝓝 0) := by
  obtain ⟨K₁, hK₁, hb⟩ := exists_pow_mul_exp_neg_le p 1 hc
  refine squeeze_zero_norm' ?_ (by simpa using tendsto_inv_atTop_zero.const_mul (|K| * K₁))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with eps he
  have h0 : 0 ≤ eps := zero_le_one.trans he
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg h0 _),
    abs_of_nonneg (Real.exp_pos _).le, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg K)
  simpa only [pow_one] using hb eps he

/-! ## `Λ` belongs to every input class -/

theorem cepsSobolev_zero_fun (m : ℕ) (η : ℝ) : cepsSobolev m η (fun _ => 0) = 0 := by
  unfold cepsSobolev
  refine Finset.sum_eq_zero fun r _ => ?_
  simp

theorem cepsInputClass_cepsLambda {D θ v : ℝ} (hreg : RegLaw D θ v v cepsLambda) {m : ℕ}
    {η : ℝ} (hη : CepsSobolevClass m η cepsLambdaDensity) {r : ℝ} (hr : 0 ≤ r) :
    CepsInputClass D θ v v m η r cepsLambda :=
  ⟨hreg, hη, ⟨cepsLambdaDensity, cepsLambdaDensity_nonneg, hη, cepsLambda_eq_withDensity, by
    simpa only [sub_self, cepsSobolev_zero_fun] using hr⟩⟩

/-! ## `lambdaChar_bound` from T1-mid -/

/-- **C-16 (decay of `φ_Λ`).** Any mid-band bound of the output characteristic function gives
the stretched-exponential decay of `φ_Λ`: `Λ` is in the class and `cepsOutChar eps Λ u → φ_Λ(u)`. -/
theorem cepsLambdaChar_bound_of_T1Mid (h : CepsT1Mid) :
    ∃ K c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ u, ‖cepsLambdaChar u‖ ≤ K * cepsStretchedWeight c d u := by
  obtain ⟨δ, hδ0, -, m, H⟩ := h
  obtain ⟨D, θ, hD, hθ, hreg⟩ := exists_regLaw_cepsLambda
  obtain ⟨η, hη, hcls⟩ := exists_cepsSobolevClass_cepsLambdaDensity m
  have hv := BrownianAffine.optimalDispersionConstant_pos
  obtain ⟨r, hr, c, U, K, eps₀, hc, d, H'⟩ := H D θ _ _ η hD hθ hv le_rfl hη
  have hmem := cepsInputClass_cepsLambda hreg hcls hr.le
  have hbig : ∀ u, U ≤ |u| → ‖cepsLambdaChar u‖ ≤ K * cepsStretchedWeight c d u := by
    intro u hu
    have h1 : Tendsto (fun eps => ‖cepsOutChar eps cepsLambda u‖) atTop
        (𝓝 ‖cepsLambdaChar u‖) :=
      (cepsOutChar_tendsto_cepsLambdaChar hD hθ hv le_rfl hreg u).norm
    have h2 : Tendsto (fun eps : ℝ => K * cepsStretchedWeight c d u + K * eps ^ d *
        Real.exp (-c * eps)) atTop (𝓝 (K * cepsStretchedWeight c d u)) := by
      simpa using tendsto_const_nhds.add (tendsto_const_mul_pow_mul_exp_neg hc K d)
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [eventually_ge_atTop eps₀,
      (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 + δ)).eventually_ge_atTop |u|]
      with eps he1 he3
    exact (H' eps he1 cepsLambda hmem u hu he3).trans
      (le_of_eq (by unfold cepsStretchedWeight; ring))
  refine ⟨max K (Real.exp (c * Real.sqrt |U|)), c, hc, d, fun u => ?_⟩
  have hw := cepsStretchedWeight_nonneg c d u
  by_cases hu : U ≤ |u|
  · exact (hbig u hu).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)
  · push Not at hu
    have h1 : ‖cepsLambdaChar u‖ ≤ 1 := by
      rw [← cepsChar_cepsLambda]; exact norm_cepsChar_le_one _ _
    refine h1.trans ?_
    have hU : |u| ≤ |U| := hu.le.trans (le_abs_self U)
    have hs : Real.sqrt |u| ≤ Real.sqrt |U| := Real.sqrt_le_sqrt hU
    have hexp : 1 ≤ Real.exp (c * Real.sqrt |U|) * Real.exp (-c * Real.sqrt |u|) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hpow : 1 ≤ (1 + |u|) ^ d := one_le_pow₀ (by linarith [abs_nonneg u])
    unfold cepsStretchedWeight
    calc (1 : ℝ) ≤ Real.exp (c * Real.sqrt |U|) * Real.exp (-c * Real.sqrt |u|) := hexp
      _ ≤ Real.exp (c * Real.sqrt |U|) * ((1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) := by
          rw [← mul_assoc, mul_comm (Real.exp (c * Real.sqrt |U|)) ((1 + |u|) ^ d), mul_assoc]
          exact le_mul_of_one_le_left (by positivity) hpow
      _ ≤ max K (Real.exp (c * Real.sqrt |U|)) * ((1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ## `phi_zero` on the class from T1-low -/

/-- **C-16 (identification on the class).** From any low-band expansion, the zero-order
coefficient at the jets of a class member is `φ_Λ`. -/
theorem cepsT1Low_phi_zero_on_class {J : CepsJetData} (hlow : CepsT1Low J) :
    ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ u : ℝ, J.phi 0 u (J.jet ν) = cepsLambdaChar u := by
  obtain ⟨m, H⟩ := hlow 0
  refine ⟨m, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r, hr, K, eps₀, d, H'⟩ := H D θ vlo vhi η hD hθ hvlo hv hη 1 one_pos
  refine ⟨r, hr, fun ν hν u => ?_⟩
  have hlim1 := cepsOutChar_tendsto_cepsLambdaChar hD hθ hvlo hv hν.reg u
  have hlim2 : Tendsto (fun eps => cepsOutChar eps ν u) atTop (𝓝 (J.phi 0 u (J.jet ν))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun eps : ℝ => K * eps⁻¹ * (1 + |u|) ^ d) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.const_mul K).mul_const ((1 + |u|) ^ d)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [eventually_ge_atTop eps₀,
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.sqrt |u|)] with eps he hl
    have hu : |u| ≤ (1 * Real.log eps) ^ 2 := by
      rw [one_mul, ← Real.sq_sqrt (abs_nonneg u)]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hl 2
    have := H' eps he ν hν u hu
    simpa only [zero_add, Finset.sum_range_one, pow_zero, one_smul, pow_one] using this
  exact tendsto_nhds_unique hlim2 hlim1

/-! ## The zero-order normal coefficient on the class -/

/-- **C-16 (normal side).** On the class, `Ĝ₀(iy; J ν) = φ_Λ(−c₀(J ν) y / 4)`: compare the
actual transform at `t = y / (4ε²)` (S-9) with the output characteristic function at
`u = −y (C_ε/ε²) / 4`, whose limit is `φ_Λ(−c₀ y / 4)` by T5 at order `0`. -/
theorem cepsGk_zero_eq_on_class {J : CepsJetData} {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ}
    {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hT5 : CepsT5 J) (hclose : CepsNormalClose Gn)
    (hexp : CepsNormalLowExpansion J Gn Gk) :
    ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ y : ℝ, Gk 0 (J.jet ν) y = cepsLambdaChar (-(J.scal 0 (J.jet ν)) * y / 4) := by
  obtain ⟨m5, H5⟩ := hT5 0
  obtain ⟨m0, H0⟩ := hclose
  obtain ⟨me, He⟩ := hexp 0
  refine ⟨max m5 (max m0 me), fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r5, hr5, K5, e5, H5'⟩ := H5 D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨r0, hr0, K0, c0, t0, e0, hc0, ht0, p0, H0'⟩ := H0 D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨re, hre, Ke, R, ee, hR, de, He'⟩ := He D θ vlo vhi η hD hθ hvlo hv hη
  refine ⟨min r5 (min r0 re), lt_min hr5 (lt_min hr0 hre), fun ν hν y => ?_⟩
  have hν5 : CepsInputClass D θ vlo vhi m5 η r5 ν :=
    hν.mono (le_max_left _ _) (min_le_left _ _)
  have hν0 : CepsInputClass D θ vlo vhi m0 η r0 ν :=
    hν.mono ((le_max_left _ _).trans (le_max_right _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
  have hνe : CepsInputClass D θ vlo vhi me η re ν :=
    hν.mono ((le_max_right _ _).trans (le_max_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _))
  have hm := hν.reg.momClass hθ hvlo
  have hvm := regV_pos hvlo
  -- T5 at order `0`: `C_ε / ε² → c₀`
  have hs : Tendsto (fun eps => lawC eps ν / eps ^ 2) atTop (𝓝 (J.scal 0 (J.jet ν))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using tendsto_inv_atTop_zero.const_mul K5)
    filter_upwards [eventually_ge_atTop e5] with eps he
    have := H5' eps he ν hν5
    simpa only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one,
      Real.norm_eq_abs] using this
  have hU : Tendsto (fun eps => -(y * (lawC eps ν / eps ^ 2)) / 4) atTop
      (𝓝 (-(J.scal 0 (J.jet ν)) * y / 4)) := by
    have := ((hs.const_mul y).neg).div_const 4
    refine this.congr' (Eventually.of_forall fun eps => rfl) |>.trans ?_
    rw [show -(y * J.scal 0 (J.jet ν)) / 4 = -(J.scal 0 (J.jet ν)) * y / 4 by ring]
  have hlim1 := cepsOutChar_tendsto_cepsLambdaChar_of_tendsto hD hθ hvlo hv hν.reg hU
  -- C-10 at order `0`: `Ĝ(b, iy) → Ĝ₀(iy; J ν)`
  have hlim2 : Tendsto (fun eps => Gn eps ν (Complex.I * y)) atTop (𝓝 (Gk 0 (J.jet ν) y)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using (tendsto_inv_atTop_zero.const_mul Ke).mul_const ((1 + |y|) ^ de))
    filter_upwards [eventually_ge_atTop ee,
      (tendsto_pow_atTop two_ne_zero).eventually_ge_atTop (|y| / R)] with eps he hy
    have hy' : |y| ≤ R * eps ^ 2 := by rwa [div_le_iff₀ hR, mul_comm] at hy
    have := He' eps he ν hνe y hy'
    simpa only [zero_add, Finset.sum_range_one, pow_zero, Complex.ofReal_one, one_mul,
      pow_one] using this
  -- S-9: the two sides are exponentially close
  have hclose' : Tendsto (fun eps => cepsOutChar eps ν (-(y * (lawC eps ν / eps ^ 2)) / 4) -
      Gn eps ν (Complex.I * y)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_pow_mul_exp_neg hc0 K0 p0)
    filter_upwards [eventually_ge_atTop e0, eventually_gt_atTop (0 : ℝ),
      (tendsto_pow_atTop two_ne_zero).eventually_ge_atTop (|y| / (4 * t0)),
      eventually_ge_atTop (epsZero (regB vhi) (regBeta D θ vlo))] with eps he hpos hy hez
    obtain ⟨_, _, _, _, _, _, hCm, _⟩ := momClass_setup hvm hez hm
    have hvν : 0 < lawVar ν := hvm.trans_le hm.var_ge
    have hC : 0 < lawC eps ν := (by positivity : 0 < eps ^ 2 / lawVar ν / 128).trans_le hCm
    have ht : |y / (4 * eps ^ 2)| ≤ t0 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * eps ^ 2), div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hy
      linarith
    have h := H0' eps he ν hν0 (y / (4 * eps ^ 2)) ht
    have e1 : (4 * eps ^ 2 * (y / (4 * eps ^ 2)) : ℝ) = y := by
      field_simp
    have e2 : (-((-(y * (lawC eps ν / eps ^ 2)) / 4) / lawC eps ν) : ℝ) = y / (4 * eps ^ 2) := by
      field_simp
    rw [e1] at h
    rw [cepsOutChar_eq_actual, e2]
    exact h
  have hlim3 : Tendsto (fun eps => Gn eps ν (Complex.I * y)) atTop
      (𝓝 (cepsLambdaChar (-(J.scal 0 (J.jet ν)) * y / 4))) := by
    have := hlim1.sub hclose'
    simpa only [sub_sub_cancel, sub_zero] using this
  exact tendsto_nhds_unique hlim2 hlim3

/-! ## The replacement `Ĝ₀(iy; p) := φ_Λ(−c₀(p) y / 4)` -/

/-- The zero-order normal coefficient replaced by its identified value for every jet vector. -/
def cepsGkLambda (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ) (sc : ℕ → (ℕ → ℝ) → ℝ) (j : ℕ) (p : ℕ → ℝ)
    (y : ℝ) : ℂ :=
  if j = 0 then cepsLambdaChar (-(sc 0 p) * y / 4) else Gk j p y

theorem cepsGkLambda_zero (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ) (sc : ℕ → (ℕ → ℝ) → ℝ) (p : ℕ → ℝ)
    (y : ℝ) : cepsGkLambda Gk sc 0 p y = cepsLambdaChar (-(sc 0 p) * y / 4) := if_pos rfl

theorem cepsGkLambda_succ (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ) (sc : ℕ → (ℕ → ℝ) → ℝ) (j : ℕ)
    (p : ℕ → ℝ) (y : ℝ) : cepsGkLambda Gk sc (j + 1) p y = Gk (j + 1) p y :=
  if_neg (Nat.succ_ne_zero j)

/-- On the class, the replacement does not change the coefficient functions. -/
theorem cepsGkLambda_eq_on_class {J : CepsJetData} {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ}
    {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hT5 : CepsT5 J) (hclose : CepsNormalClose Gn)
    (hexp : CepsNormalLowExpansion J Gn Gk) :
    ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
        ∀ j : ℕ, cepsGkLambda Gk J.scal j (J.jet ν) = Gk j (J.jet ν) := by
  obtain ⟨m, H⟩ := cepsGk_zero_eq_on_class hT5 hclose hexp
  refine ⟨m, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r, hr, H'⟩ := H D θ vlo vhi η hD hθ hvlo hv hη
  refine ⟨r, hr, fun ν hν j => funext fun y => ?_⟩
  cases j with
  | zero => rw [cepsGkLambda_zero, H' ν hν y]
  | succ j => exact cepsGkLambda_succ Gk J.scal j _ y

theorem cepsNormalLowExpansion_gkLambda {J : CepsJetData}
    {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ} {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hT5 : CepsT5 J)
    (hclose : CepsNormalClose Gn) (hexp : CepsNormalLowExpansion J Gn Gk) :
    CepsNormalLowExpansion J Gn (cepsGkLambda Gk J.scal) := by
  obtain ⟨mi, Hi⟩ := cepsGkLambda_eq_on_class hT5 hclose hexp
  intro N
  obtain ⟨me, He⟩ := hexp N
  refine ⟨max mi me, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨ri, hri, Hi'⟩ := Hi D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨re, hre, K, R, e, hR, d, He'⟩ := He D θ vlo vhi η hD hθ hvlo hv hη
  refine ⟨min ri re, lt_min hri hre, K, R, e, hR, d, fun eps he ν hν y hy => ?_⟩
  have hid := Hi' ν (hν.mono (le_max_left _ _) (min_le_left _ _))
  have h := He' eps he ν (hν.mono (le_max_right _ _) (min_le_right _ _)) y hy
  simpa only [hid] using h

theorem cepsNormalCoeffReg_gkLambda {J : CepsJetData}
    {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ} {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hT5 : CepsT5 J)
    (hclose : CepsNormalClose Gn) (hexp : CepsNormalLowExpansion J Gn Gk)
    (hreg : CepsNormalCoeffReg J Gk) : CepsNormalCoeffReg J (cepsGkLambda Gk J.scal) := by
  obtain ⟨mi, Hi⟩ := cepsGkLambda_eq_on_class hT5 hclose hexp
  intro N
  obtain ⟨mr, Hr⟩ := hreg N
  refine ⟨max mi mr, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨ri, hri, Hi'⟩ := Hi D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨rr, hrr, B, d, Hr'⟩ := Hr D θ vlo vhi η hD hθ hvlo hv hη
  refine ⟨min ri rr, lt_min hri hrr, B, d, fun ν hν j hj => ?_⟩
  rw [Hi' ν (hν.mono (le_max_left _ _) (min_le_left _ _)) j]
  exact Hr' ν (hν.mono (le_max_right _ _) (min_le_right _ _)) j hj

/-! ## `phi_zero` for every jet vector -/

theorem lowCompCoeff_zero (g : ℕ → ℝ → ℂ) (c : ℕ → ℝ) (ω : ℝ) :
    lowCompCoeff g c ω 0 = g 0 (ω / c 0) := by
  simp [lowCompCoeff, compSeries]

/-- With the replacement, `Φ₀(u; p) = φ_Λ(u)` for every `p` with `c₀(p) ≠ 0`. -/
theorem cepsLowCoeff_gkLambda_zero (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ) (sc : ℕ → (ℕ → ℝ) → ℝ)
    {p : ℕ → ℝ} (h : sc 0 p ≠ 0) (u : ℝ) :
    cepsLowCoeff (cepsGkLambda Gk sc) sc 0 u p = cepsLambdaChar u := by
  rw [cepsLowCoeff, lowCompCoeff_zero, pow_zero, one_mul, cepsGkLambda_zero]
  congr 1
  field_simp

/-- **C-16 (`CepsT3.phi_zero`).** -/
theorem cepsT3_phi_zero_of_gkLambda {J : CepsJetData} {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ}
    (hphi : ∀ k u p, J.phi k u p = cepsLowCoeff (cepsGkLambda Gk J.scal) J.scal k u p)
    (hsc : ∀ p, J.scal 0 p ≠ 0) : ∀ u p, J.phi 0 u p = cepsLambdaChar u := fun u p => by
  rw [hphi, cepsLowCoeff_gkLambda_zero Gk J.scal (hsc p)]

/-! ## The off-class adjustment `C₀(p) ≠ 0` -/

/-- `C₀` replaced by `1` where it vanishes; the other coefficients are unchanged. -/
def cepsCsAdjust (Cs : ℕ → (ℕ → ℝ) → ℝ) (k : ℕ) (p : ℕ → ℝ) : ℝ :=
  if Cs 0 p = 0 ∧ k = 0 then 1 else Cs k p

theorem cepsCsAdjust_zero_ne_zero (Cs : ℕ → (ℕ → ℝ) → ℝ) (p : ℕ → ℝ) :
    cepsCsAdjust Cs 0 p ≠ 0 := by
  unfold cepsCsAdjust
  split_ifs with h
  · exact one_ne_zero
  · exact fun h0 => h ⟨h0, rfl⟩

theorem cepsCsAdjust_of_ne {Cs : ℕ → (ℕ → ℝ) → ℝ} {p : ℕ → ℝ} (h : Cs 0 p ≠ 0) (k : ℕ) :
    cepsCsAdjust Cs k p = Cs k p := if_neg fun h' => h h'.1

theorem cepsCsAdjust_succ (Cs : ℕ → (ℕ → ℝ) → ℝ) (k : ℕ) (p : ℕ → ℝ) :
    cepsCsAdjust Cs (k + 1) p = Cs (k + 1) p := if_neg fun h' => Nat.succ_ne_zero k h'.2

/-- The scalar coefficients `4 (1/2)ᵏ C_k` built from the adjusted `C_k` never vanish at
order `0`. -/
theorem cepsCsAdjust_scal_zero_ne_zero (Cs : ℕ → (ℕ → ℝ) → ℝ) (p : ℕ → ℝ) :
    (4 * (2⁻¹ : ℝ) ^ 0 * cepsCsAdjust Cs 0 p) ≠ 0 := by
  have := cepsCsAdjust_zero_ne_zero Cs p
  simpa using this

/-- The mean expansion survives the adjustment: on the class, `C₀(J ν) ≥ c_lo / 4 > 0` by
T5 at order `0`, so the adjusted coefficients agree with the original ones there. -/
theorem cepsNormalMeanExpansion_adjust {J : CepsJetData}
    {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ} {Dn : ℝ → ProbabilityMeasure ℝ → ℂ}
    {Cs : ℕ → (ℕ → ℝ) → ℝ} (hclose : CepsNormalClose Gn) (htaylor : CepsNormalTaylor Gn Dn)
    (hmean : CepsNormalMeanExpansion J Dn Cs) :
    CepsNormalMeanExpansion J Dn (cepsCsAdjust Cs) := by
  let J' : CepsJetData := { J with scal := fun k p => 4 * (2⁻¹) ^ k * Cs k p }
  have hmean' : CepsNormalMeanExpansion J' Dn Cs := hmean
  have hT5 : CepsT5 J' := cepsT5_of_normal hclose htaylor hmean' fun _ _ => rfl
  obtain ⟨mb, Hb⟩ := cepsT5_scal_bounds hT5 0
  intro P
  obtain ⟨mm, Hm⟩ := hmean P
  refine ⟨max mb mm, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨rb, hrb, c_lo, B, hclo, Hb'⟩ := Hb D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨rm, hrm, K, e, Hm'⟩ := Hm D θ vlo vhi η hD hθ hvlo hv hη
  refine ⟨min rb rm, lt_min hrb hrm, K, e, fun eps he ν hν => ?_⟩
  have hb : c_lo ≤ 4 * (2⁻¹ : ℝ) ^ 0 * Cs 0 (J.jet ν) :=
    (Hb' ν (hν.mono (le_max_left _ _) (min_le_left _ _))).1
  have hne : Cs 0 (J.jet ν) ≠ 0 := by
    intro h0
    rw [h0] at hb
    simp at hb
    linarith
  have h := Hm' eps he ν (hν.mono (le_max_right _ _) (min_le_right _ _))
  simpa only [cepsCsAdjust_of_ne hne] using h

end

end PGM
