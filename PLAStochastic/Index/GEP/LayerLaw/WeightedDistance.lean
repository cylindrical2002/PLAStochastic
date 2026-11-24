import PLAStochastic.Index.GEP.LayerLaw.Defs

/-!
# The weighted distance on the regular class

Elementary facts about `dEta` and `lawVar` on `RegLaw` used by the assembly
(`closure-assembly.md` §2–3):

* monotonicity of the class in its parameters;
* the tail bound `ν(x, ∞) ≤ (D/θ) e^{-θx}` and the diameter bound
  `dEta η ν ρ ≤ D / (θ (θ - η))` for `0 ≤ η < θ`;
* symmetry and the triangle inequality of `dEta` on the class;
* the comparison `dEta ≤ K W₂` and `|Δ lawVar| ≤ K W₂` of `closure-assembly.md` §3;
* `|log a - log b| ≤ |a - b| / c` for `a, b ≥ c > 0`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {D θ vlo vhi : ℝ}

/-! ### Auxiliary facts -/

theorem RegLaw.D_nonneg {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) : 0 ≤ D := by
  obtain ⟨f, -, hf0, -, hfD, -⟩ := h.density
  simpa using (hf0 0).trans (hfD 0)

/-- `∫_c^∞ C e^{-b x} dx = (C / b) e^{-b c}` as a lower integral. -/
theorem lintegral_Ioi_ofReal_mul_exp {b : ℝ} (hb : 0 < b) {C : ℝ} (hC : 0 ≤ C) (c : ℝ) :
    ∫⁻ x in Ioi c, ENNReal.ofReal (C * Real.exp (-b * x)) =
      ENNReal.ofReal (C / b * Real.exp (-b * c)) := by
  have hi : IntegrableOn (fun x => C * Real.exp (-b * x)) (Ioi c) :=
    (integrableOn_exp_mul_Ioi (by linarith) c).const_mul C
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun x => mul_nonneg hC (Real.exp_pos _).le)]
  congr 1
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) c, neg_div_neg_eq]
  ring

theorem RegLaw.measure_Ioi_le {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (x : ℝ) :
    (ν : Measure ℝ) (Ioi x) ≤ ENNReal.ofReal (D / θ * Real.exp (-θ * x)) := by
  obtain ⟨f, -, -, -, hfD, hν⟩ := h.density
  rw [hν, withDensity_apply _ measurableSet_Ioi,
    ← lintegral_Ioi_ofReal_mul_exp hθ h.D_nonneg x]
  exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hfD y)

theorem RegLaw.one_sub_cdf_le' {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (x : ℝ) :
    1 - cdf (ν : Measure ℝ) x ≤ D / θ * Real.exp (-θ * x) := by
  have hc : 1 - cdf (ν : Measure ℝ) x = (ν : Measure ℝ).real (Ioi x) := by
    rw [cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  rw [hc, measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (div_nonneg h.D_nonneg hθ.le) (Real.exp_pos _).le) (h.measure_Ioi_le hθ x)

theorem RegLaw.abs_cdf_sub_le {ν ρ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hρ : RegLaw D θ vlo vhi ρ) (hθ : 0 < θ) (x : ℝ) :
    |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x| ≤ D / θ * Real.exp (-θ * x) := by
  have h1 := hν.one_sub_cdf_le' hθ x
  have h2 := hρ.one_sub_cdf_le' hθ x
  have h3 := cdf_le_one (ν : Measure ℝ) x
  have h4 := cdf_le_one (ρ : Measure ℝ) x
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem measurable_dEta_integrand (η : ℝ) (ν ρ : ProbabilityMeasure ℝ) :
    Measurable fun x => Real.exp (η * x) * |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x| :=
  (measurable_const.mul measurable_id).exp.mul
    (continuous_abs.measurable.comp
      ((monotone_cdf (ν : Measure ℝ)).measurable.sub (monotone_cdf (ρ : Measure ℝ)).measurable))

theorem RegLaw.integrableOn_dEta {ν ρ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hρ : RegLaw D θ vlo vhi ρ) {η : ℝ} (hηθ : η < θ) (hθ : 0 < θ) :
    IntegrableOn
      (fun x => Real.exp (η * x) * |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x|) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := η - θ) (by linarith) 0).const_mul
    (D / θ)) (measurable_dEta_integrand η ν ρ).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
  calc Real.exp (η * x) * |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x|
      ≤ Real.exp (η * x) * (D / θ * Real.exp (-θ * x)) :=
        mul_le_mul_of_nonneg_left (hν.abs_cdf_sub_le hρ hθ x) (Real.exp_pos _).le
    _ = D / θ * Real.exp ((η - θ) * x) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- `E_ν e^{a X} ≤ D / (θ - a)` on the class, as a lower integral. -/
theorem RegLaw.lintegral_exp_le {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) {a : ℝ}
    (ha : a < θ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a * x)) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal (D / (θ - a)) := by
  obtain ⟨f, hfm, hf0, hfz, hfD, hν⟩ := h.density
  have hD := h.D_nonneg
  have hg : Measurable fun x => ENNReal.ofReal (Real.exp (a * x)) :=
    (measurable_const.mul measurable_id).exp.ennreal_ofReal
  rw [hν, lintegral_withDensity_eq_lintegral_mul _ hfm.ennreal_ofReal hg]
  calc ∫⁻ x, ((fun x => ENNReal.ofReal (f x)) * fun x => ENNReal.ofReal (Real.exp (a * x))) x
      ≤ ∫⁻ x, (Ioi (0 : ℝ)).indicator
          (fun x => ENNReal.ofReal (D * Real.exp (-(θ - a) * x))) x := by
        refine lintegral_mono fun x => ?_
        simp only [Pi.mul_apply]
        rcases le_or_gt x 0 with hx | hx
        · rw [hfz x hx]; simp
        · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx), ← ENNReal.ofReal_mul (hf0 x)]
          apply ENNReal.ofReal_le_ofReal
          calc f x * Real.exp (a * x) ≤ D * Real.exp (-θ * x) * Real.exp (a * x) :=
                mul_le_mul_of_nonneg_right (hfD x) (Real.exp_pos _).le
            _ = D * Real.exp (-(θ - a) * x) := by
                rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ = ENNReal.ofReal (D / (θ - a)) := by
        rw [lintegral_indicator measurableSet_Ioi,
          lintegral_Ioi_ofReal_mul_exp (by linarith) hD 0, mul_zero, Real.exp_zero, mul_one]

/-- Cauchy–Schwarz for lower integrals of real functions. -/
theorem lintegral_abs_mul_le_sqrt {α : Type*} [MeasurableSpace α] (μ : Measure α) {a b : α → ℝ}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    ∫⁻ x, ENNReal.ofReal (|a x| * |b x|) ∂μ ≤
      (∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ x, ENNReal.ofReal (b x ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x => ENNReal.ofReal |a x|) (g := fun x => ENNReal.ofReal |b x|)
    (continuous_abs.measurable.comp_aemeasurable ha).ennreal_ofReal
    (continuous_abs.measurable.comp_aemeasurable hb).ennreal_ofReal
  have e1 : ∀ c : ℝ, ENNReal.ofReal |c| ^ (2 : ℝ) = ENNReal.ofReal (c ^ 2) := by
    intro c
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg c) (by norm_num), Real.rpow_two, sq_abs]
  calc ∫⁻ x, ENNReal.ofReal (|a x| * |b x|) ∂μ
      = ∫⁻ x, ((fun x => ENNReal.ofReal |a x|) * fun x => ENNReal.ofReal |b x|) x ∂μ := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ _ := h
    _ = _ := by simp only [e1]

theorem lintegral_sq_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {a : α → ℝ}
    (hi : Integrable (fun x => a x ^ 2) μ) {w : ℝ} (hw : 0 ≤ w)
    (hle : ∫ x, a x ^ 2 ∂μ ≤ w ^ 2) :
    (∫⁻ x, ENNReal.ofReal (a x ^ 2) ∂μ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal w := by
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => sq_nonneg (a x)),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => sq_nonneg (a x)) (by norm_num),
    ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_sq hw))

/-- `|F_ν(x) - F_ρ(x)| ≤ π{min ≤ x < max}` for a coupling `π` of `ν` and `ρ`. -/
theorem abs_cdf_sub_le_coupling {ν ρ : ProbabilityMeasure ℝ} {π : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure π] (h1 : π.map Prod.fst = (ν : Measure ℝ))
    (h2 : π.map Prod.snd = (ρ : Measure ℝ)) (x : ℝ) :
    |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x| ≤
      π.real {p | min p.1 p.2 ≤ x ∧ x < max p.1 p.2} := by
  have e1 : cdf (ν : Measure ℝ) x = π.real {p | p.1 ≤ x} := by
    rw [cdf_eq_real, ← h1, measureReal_def, Measure.map_apply measurable_fst measurableSet_Iic]
    rfl
  have e2 : cdf (ρ : Measure ℝ) x = π.real {p | p.2 ≤ x} := by
    rw [cdf_eq_real, ← h2, measureReal_def, Measure.map_apply measurable_snd measurableSet_Iic]
    rfl
  rw [e1, e2]
  refine (abs_measureReal_sub_le_measureReal_symmDiff
    (measurableSet_le measurable_fst measurable_const).nullMeasurableSet
    (measurableSet_le measurable_snd measurable_const).nullMeasurableSet).trans
    (measureReal_mono fun p hp => ?_)
  rcases Set.mem_symmDiff.mp hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
  · exact ⟨(min_le_left _ _).trans hp1, (not_le.mp hp2).trans_le (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans hp1, (not_le.mp hp2).trans_le (le_max_left _ _)⟩

/-- Tonelli: `∫_0^∞ e^{ηx} π{min ≤ x < max} dx ≤ E_π |X - Y| e^{η max(X, Y)}`. -/
theorem lintegral_exp_mul_measure_le {π : Measure (ℝ × ℝ)} [SFinite π] {η : ℝ} (hη : 0 ≤ η) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (η * x)) *
        π {p | min p.1 p.2 ≤ x ∧ x < max p.1 p.2} ≤
      ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| * |Real.exp (η * max p.1 p.2)|) ∂π := by
  have hU : MeasurableSet {q : ℝ × (ℝ × ℝ) | min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2} :=
    (measurableSet_le ((measurable_fst.comp measurable_snd).min
      (measurable_snd.comp measurable_snd)) measurable_fst).inter
      (measurableSet_lt measurable_fst ((measurable_fst.comp measurable_snd).max
        (measurable_snd.comp measurable_snd)))
  have hG : Measurable ({q : ℝ × (ℝ × ℝ) | min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2}.indicator
      fun q => ENNReal.ofReal (Real.exp (η * q.1))) :=
    ((measurable_const.mul measurable_fst).exp.ennreal_ofReal).indicator hU
  have hT : ∀ x : ℝ, MeasurableSet {p : ℝ × ℝ | min p.1 p.2 ≤ x ∧ x < max p.1 p.2} := fun x =>
    (measurableSet_le (measurable_fst.min measurable_snd) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_fst.max measurable_snd))
  calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (η * x)) *
        π {p | min p.1 p.2 ≤ x ∧ x < max p.1 p.2}
      = ∫⁻ x in Ioi (0 : ℝ), (∫⁻ p,
          {q : ℝ × (ℝ × ℝ) | min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2}.indicator
            (fun q => ENNReal.ofReal (Real.exp (η * q.1))) (x, p) ∂π) := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_indicator_const (hT x)]
        rfl
    _ = ∫⁻ p, (∫⁻ x in Ioi (0 : ℝ),
          {q : ℝ × (ℝ × ℝ) | min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2}.indicator
            (fun q => ENNReal.ofReal (Real.exp (η * q.1))) (x, p)) ∂π :=
        lintegral_lintegral_swap hG.aemeasurable
    _ ≤ ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| * |Real.exp (η * max p.1 p.2)|) ∂π := by
        refine lintegral_mono fun p => ?_
        have hpt : ∀ x : ℝ,
            {q : ℝ × (ℝ × ℝ) | min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2}.indicator
              (fun q => ENNReal.ofReal (Real.exp (η * q.1))) (x, p) ≤
            (Ico (min p.1 p.2) (max p.1 p.2)).indicator
              (fun _ => ENNReal.ofReal (Real.exp (η * max p.1 p.2))) x := by
          intro x
          by_cases hx : min p.1 p.2 ≤ x ∧ x < max p.1 p.2
          · rw [Set.indicator_of_mem (show (x, p) ∈ {q : ℝ × (ℝ × ℝ) |
                min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2} from hx),
              Set.indicator_of_mem (show x ∈ Ico (min p.1 p.2) (max p.1 p.2) from hx)]
            exact ENNReal.ofReal_le_ofReal
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2.le hη))
          · rw [Set.indicator_of_notMem (show (x, p) ∉ {q : ℝ × (ℝ × ℝ) |
                min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2} from hx)]
            exact zero_le
        calc ∫⁻ x in Ioi (0 : ℝ),
              {q : ℝ × (ℝ × ℝ) | min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2}.indicator
                (fun q => ENNReal.ofReal (Real.exp (η * q.1))) (x, p)
            ≤ ∫⁻ x, {q : ℝ × (ℝ × ℝ) | min q.2.1 q.2.2 ≤ q.1 ∧ q.1 < max q.2.1 q.2.2}.indicator
                (fun q => ENNReal.ofReal (Real.exp (η * q.1))) (x, p) :=
              setLIntegral_le_lintegral _ _
          _ ≤ ∫⁻ x, (Ico (min p.1 p.2) (max p.1 p.2)).indicator
                (fun _ => ENNReal.ofReal (Real.exp (η * max p.1 p.2))) x := lintegral_mono hpt
          _ = ENNReal.ofReal (Real.exp (η * max p.1 p.2)) *
                ENNReal.ofReal (max p.1 p.2 - min p.1 p.2) := by
              rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
          _ = ENNReal.ofReal (|p.1 - p.2| * |Real.exp (η * max p.1 p.2)|) := by
              rw [abs_of_pos (Real.exp_pos _), max_sub_min_eq_abs, abs_sub_comm, mul_comm,
                ENNReal.ofReal_mul (abs_nonneg _)]

/-! ### The statements -/

theorem RegLaw.mono {D' θ' vlo' vhi' : ℝ} {ν : ProbabilityMeasure ℝ}
    (h : RegLaw D θ vlo vhi ν) (hD : D ≤ D') (hθ : θ' ≤ θ) (hθ' : 0 ≤ θ')
    (hlo : vlo' ≤ vlo) (hhi : vhi ≤ vhi') : RegLaw D' θ' vlo' vhi' ν := by
  -- `0 ≤ θ'` is not needed: `f = 0` on `x ≤ 0`, and `θ' ≤ θ` handles `x > 0`.
  have _ := hθ'
  obtain ⟨f, hfm, hf0, hfz, hfD, hν⟩ := h.density
  have hD0 : 0 ≤ D := h.D_nonneg
  refine ⟨⟨f, hfm, hf0, hfz, fun x => ?_, hν⟩, h.mean, hlo.trans h.var_ge, h.var_le.trans hhi⟩
  rcases le_or_gt x 0 with hx | hx
  · rw [hfz x hx]; exact mul_nonneg (hD0.trans hD) (Real.exp_pos _).le
  · calc f x ≤ D * Real.exp (-θ * x) := hfD x
      _ ≤ D' * Real.exp (-θ' * x) :=
        mul_le_mul hD (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (hD0.trans hD)

theorem RegLaw.cdf_eq_zero {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) {x : ℝ}
    (hx : x ≤ 0) : cdf (ν : Measure ℝ) x = 0 := by
  obtain ⟨f, -, -, hfz, -, hν⟩ := h.density
  have h0 : (ν : Measure ℝ) (Iic x) = 0 := by
    rw [hν, withDensity_apply _ measurableSet_Iic]
    refine (setLIntegral_congr_fun measurableSet_Iic (g := fun _ => (0 : ENNReal)) ?_).trans
      (by simp)
    intro y hy
    simp [hfz y (le_trans hy hx)]
  rw [cdf_eq_real, measureReal_def, h0, ENNReal.toReal_zero]

theorem RegLaw.one_sub_cdf_le {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) {x : ℝ} (hx : 0 ≤ x) :
    1 - cdf (ν : Measure ℝ) x ≤ D / θ * Real.exp (-θ * x) := by
  -- The tail bound holds for every `x`; `0 ≤ x` is not needed.
  have _ := hx
  exact h.one_sub_cdf_le' hθ x

theorem dEta_nonneg (η : ℝ) (ν ρ : ProbabilityMeasure ℝ) : 0 ≤ dEta η ν ρ :=
  integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)

theorem dEta_self (η : ℝ) (ν : ProbabilityMeasure ℝ) : dEta η ν ν = 0 := by
  simp [dEta]

theorem dEta_comm (η : ℝ) (ν ρ : ProbabilityMeasure ℝ) : dEta η ν ρ = dEta η ρ ν := by
  simp only [dEta, abs_sub_comm]

theorem dEta_le_diam {ν ρ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hρ : RegLaw D θ vlo vhi ρ) {η : ℝ} (hη : 0 ≤ η) (hηθ : η < θ) :
    dEta η ν ρ ≤ D / (θ * (θ - η)) := by
  have hθ : 0 < θ := by linarith
  have hθη : θ - η ≠ 0 := by linarith
  have hηθ' : η - θ ≠ 0 := by linarith
  calc dEta η ν ρ ≤ ∫ x in Ioi (0 : ℝ), D / θ * Real.exp ((η - θ) * x) := by
        refine integral_mono_of_nonneg
          (ae_of_all _ fun x => mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
          ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _) (ae_of_all _ fun x => ?_)
        calc Real.exp (η * x) * |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x|
            ≤ Real.exp (η * x) * (D / θ * Real.exp (-θ * x)) :=
              mul_le_mul_of_nonneg_left (hν.abs_cdf_sub_le hρ hθ x) (Real.exp_pos _).le
          _ = D / θ * Real.exp ((η - θ) * x) := by
              rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    _ = D / (θ * (θ - η)) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith), mul_zero, Real.exp_zero]
        field_simp
        ring

theorem dEta_triangle {μ ν ρ : ProbabilityMeasure ℝ} (hμ : RegLaw D θ vlo vhi μ)
    (hν : RegLaw D θ vlo vhi ν) (hρ : RegLaw D θ vlo vhi ρ) {η : ℝ} (hη : 0 ≤ η)
    (hηθ : η < θ) : dEta η μ ρ ≤ dEta η μ ν + dEta η ν ρ := by
  have hθ : 0 < θ := by linarith
  have i1 := hμ.integrableOn_dEta hν hηθ hθ
  have i2 := hν.integrableOn_dEta hρ hηθ hθ
  unfold dEta
  rw [← integral_add i1 i2]
  refine integral_mono_of_nonneg
    (ae_of_all _ fun x => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (i1.add i2)
    (ae_of_all _ fun x => ?_)
  dsimp only
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (Real.exp_pos _).le

theorem abs_lawVar_sub_le_diam {ν ρ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hρ : RegLaw D θ vlo vhi ρ) : |lawVar ν - lawVar ρ| ≤ vhi - vlo := by
  have := hν.var_ge
  have := hν.var_le
  have := hρ.var_ge
  have := hρ.var_le
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- `d_η ≤ K W₂` on the class (`closure-assembly.md` §3). -/
theorem dEta_le_of_W2Le {ν ρ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hρ : RegLaw D θ vlo vhi ρ) {η : ℝ} (hη : 0 ≤ η) (h2η : 2 * η < θ) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : W2Le ν ρ w) : dEta η ν ρ ≤ Real.sqrt (2 * D / (θ - 2 * η)) * w := by
  obtain ⟨π, hπ, h1, h2, hint, hle⟩ := hw
  have hD := hν.D_nonneg
  have hK0 : 0 ≤ 2 * D / (θ - 2 * η) := div_nonneg (by linarith) (by linarith)
  have hmeas := measurable_dEta_integrand η ν ρ
  unfold dEta
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun x => mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
    hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Real.sqrt_nonneg _) hw0) ?_
  -- the exponential moment of `max`
  have hB : ∫⁻ p, ENNReal.ofReal (Real.exp (η * max p.1 p.2) ^ 2) ∂π ≤
      ENNReal.ofReal (2 * D / (θ - 2 * η)) := by
    have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (η * max p.1 p.2) ^ 2) ≤
        ENNReal.ofReal (Real.exp (2 * η * p.1)) + ENNReal.ofReal (Real.exp (2 * η * p.2)) := by
      intro p
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      rw [sq, ← Real.exp_add]
      rcases le_total p.1 p.2 with hp | hp
      · rw [max_eq_right hp, show η * p.2 + η * p.2 = 2 * η * p.2 by ring]
        linarith [Real.exp_pos (2 * η * p.1)]
      · rw [max_eq_left hp, show η * p.1 + η * p.1 = 2 * η * p.1 by ring]
        linarith [Real.exp_pos (2 * η * p.2)]
    have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (2 * η * x)) :=
      (measurable_const.mul measurable_id).exp.ennreal_ofReal
    calc ∫⁻ p, ENNReal.ofReal (Real.exp (η * max p.1 p.2) ^ 2) ∂π
        ≤ ∫⁻ p, (ENNReal.ofReal (Real.exp (2 * η * p.1)) +
            ENNReal.ofReal (Real.exp (2 * η * p.2))) ∂π := lintegral_mono hpt
      _ = ∫⁻ p, ENNReal.ofReal (Real.exp (2 * η * p.1)) ∂π +
            ∫⁻ p, ENNReal.ofReal (Real.exp (2 * η * p.2)) ∂π :=
          lintegral_add_left (hm.comp measurable_fst) _
      _ = ∫⁻ x, ENNReal.ofReal (Real.exp (2 * η * x)) ∂(ν : Measure ℝ) +
            ∫⁻ x, ENNReal.ofReal (Real.exp (2 * η * x)) ∂(ρ : Measure ℝ) := by
          rw [← h1, ← h2, lintegral_map hm measurable_fst, lintegral_map hm measurable_snd]
      _ ≤ ENNReal.ofReal (D / (θ - 2 * η)) + ENNReal.ofReal (D / (θ - 2 * η)) :=
          add_le_add (hν.lintegral_exp_le h2η) (hρ.lintegral_exp_le h2η)
      _ = ENNReal.ofReal (2 * D / (θ - 2 * η)) := by
          rw [← ENNReal.ofReal_add (div_nonneg hD (by linarith)) (div_nonneg hD (by linarith))]
          congr 1; ring
  have hB' : (∫⁻ p, ENNReal.ofReal (Real.exp (η * max p.1 p.2) ^ 2) ∂π) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (2 * D / (θ - 2 * η))) := by
    calc _ ≤ (ENNReal.ofReal (2 * D / (θ - 2 * η))) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hB (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (2 * D / (θ - 2 * η))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num), Real.sqrt_eq_rpow]
  have hA := lintegral_sq_rpow_le hint hw0 hle
  have hCS := lintegral_abs_mul_le_sqrt π (a := fun p : ℝ × ℝ => p.1 - p.2)
    (b := fun p : ℝ × ℝ => Real.exp (η * max p.1 p.2))
    (measurable_fst.sub measurable_snd).aemeasurable
    (measurable_const.mul (measurable_fst.max measurable_snd)).exp.aemeasurable
  calc ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (η * x) * |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x|)
      ≤ ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (η * x)) *
          π {p | min p.1 p.2 ≤ x ∧ x < max p.1 p.2} := by
        refine lintegral_mono fun x => ?_
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        gcongr
        calc ENNReal.ofReal |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x|
            ≤ ENNReal.ofReal (π.real {p | min p.1 p.2 ≤ x ∧ x < max p.1 p.2}) :=
              ENNReal.ofReal_le_ofReal (abs_cdf_sub_le_coupling h1 h2 x)
          _ = π {p | min p.1 p.2 ≤ x ∧ x < max p.1 p.2} := ofReal_measureReal
    _ ≤ ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| * |Real.exp (η * max p.1 p.2)|) ∂π :=
        lintegral_exp_mul_measure_le hη
    _ ≤ ENNReal.ofReal w * ENNReal.ofReal (Real.sqrt (2 * D / (θ - 2 * η))) :=
        hCS.trans (mul_le_mul' hA hB')
    _ = ENNReal.ofReal (Real.sqrt (2 * D / (θ - 2 * η)) * w) := by
        rw [← ENNReal.ofReal_mul hw0, mul_comm]

/-- `|Δ v| ≤ K W₂` on the class (`closure-assembly.md` §3). -/
theorem abs_lawVar_sub_le_of_W2Le {ν ρ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hρ : RegLaw D θ vlo vhi ρ) (hvhi : 0 ≤ vhi) {w : ℝ} (hw0 : 0 ≤ w) (hw : W2Le ν ρ w) :
    |lawVar ν - lawVar ρ| ≤ 2 * Real.sqrt vhi * w := by
  obtain ⟨π, hπ, h1, h2, hint, hle⟩ := hw
  have hsm : ∀ μ : Measure ℝ, AEStronglyMeasurable (fun x : ℝ => (x - 1) ^ 2) μ := fun μ =>
    ((measurable_id.sub_const 1).pow_const 2).aestronglyMeasurable
  have hν' : lawVar ν = ∫ p, (p.1 - 1) ^ 2 ∂π := by
    rw [lawVar, hν.mean, ← h1, integral_map measurable_fst.aemeasurable (hsm _)]
  have hρ' : lawVar ρ = ∫ p, (p.2 - 1) ^ 2 ∂π := by
    rw [lawVar, hρ.mean, ← h2, integral_map measurable_snd.aemeasurable (hsm _)]
  have t12 : Integrable (fun p : ℝ × ℝ => (p.1 - 1) ^ 2) π →
      Integrable (fun p : ℝ × ℝ => (p.2 - 1) ^ 2) π := by
    intro hi
    refine Integrable.mono' ((hi.const_mul 2).add (hint.const_mul 2))
      ((measurable_snd.sub_const 1).pow_const 2).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_pow, sq_abs]
    nlinarith [sq_nonneg (p.1 - 1 + (p.1 - p.2))]
  have t21 : Integrable (fun p : ℝ × ℝ => (p.2 - 1) ^ 2) π →
      Integrable (fun p : ℝ × ℝ => (p.1 - 1) ^ 2) π := by
    intro hi
    refine Integrable.mono' ((hi.const_mul 2).add (hint.const_mul 2))
      ((measurable_fst.sub_const 1).pow_const 2).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_pow, sq_abs]
    nlinarith [sq_nonneg (p.2 - 1 - (p.1 - p.2))]
  have hK : 0 ≤ 2 * Real.sqrt vhi * w :=
    mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) hw0
  by_cases hI : Integrable (fun p : ℝ × ℝ => (p.1 - 1) ^ 2) π
  · have hI2 := t12 hI
    have hA := lintegral_sq_rpow_le hint hw0 hle
    have hB1 := lintegral_sq_rpow_le hI (Real.sqrt_nonneg vhi)
      (by rw [← hν', Real.sq_sqrt hvhi]; exact hν.var_le)
    have hB2 := lintegral_sq_rpow_le hI2 (Real.sqrt_nonneg vhi)
      (by rw [← hρ', Real.sq_sqrt hvhi]; exact hρ.var_le)
    have hma : AEMeasurable (fun p : ℝ × ℝ => p.1 - p.2) π :=
      (measurable_fst.sub measurable_snd).aemeasurable
    have hC1 := (lintegral_abs_mul_le_sqrt π hma
      (measurable_fst.sub_const 1).aemeasurable).trans (mul_le_mul' hA hB1)
    have hC2 := (lintegral_abs_mul_le_sqrt π hma
      (measurable_snd.sub_const 1).aemeasurable).trans (mul_le_mul' hA hB2)
    have hdiff : lawVar ν - lawVar ρ = ∫ p, (p.1 - p.2) * ((p.1 - 1) + (p.2 - 1)) ∂π := by
      rw [hν', hρ', ← integral_sub hI hI2]
      congr 1; ext p; ring
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => |(p.1 - p.2) * ((p.1 - 1) + (p.2 - 1))|) π :=
      (continuous_abs.measurable.comp ((measurable_fst.sub measurable_snd).mul
        ((measurable_fst.sub_const 1).add (measurable_snd.sub_const 1)))).aestronglyMeasurable
    have hm1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (|p.1 - p.2| * |p.1 - 1|) :=
      ((continuous_abs.measurable.comp (measurable_fst.sub measurable_snd)).mul
        (continuous_abs.measurable.comp (measurable_fst.sub_const 1))).ennreal_ofReal
    rw [hdiff]
    refine abs_integral_le_integral_abs.trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => abs_nonneg _) hmeas]
    refine ENNReal.toReal_le_of_le_ofReal hK ?_
    calc ∫⁻ p, ENNReal.ofReal |(p.1 - p.2) * ((p.1 - 1) + (p.2 - 1))| ∂π
        ≤ ∫⁻ p, (ENNReal.ofReal (|p.1 - p.2| * |p.1 - 1|) +
            ENNReal.ofReal (|p.1 - p.2| * |p.2 - 1|)) ∂π := by
          refine lintegral_mono fun p => ?_
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [abs_mul, ← mul_add]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ = ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| * |p.1 - 1|) ∂π +
            ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| * |p.2 - 1|) ∂π := lintegral_add_left hm1 _
      _ ≤ ENNReal.ofReal w * ENNReal.ofReal (Real.sqrt vhi) +
            ENNReal.ofReal w * ENNReal.ofReal (Real.sqrt vhi) := add_le_add hC1 hC2
      _ = ENNReal.ofReal (2 * Real.sqrt vhi * w) := by
          rw [← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_add (mul_nonneg hw0 (Real.sqrt_nonneg _))
            (mul_nonneg hw0 (Real.sqrt_nonneg _))]
          congr 1; ring
  · have hI2 : ¬ Integrable (fun p : ℝ × ℝ => (p.2 - 1) ^ 2) π := fun h => hI (t21 h)
    rw [hν', hρ', integral_undef hI, integral_undef hI2, sub_self, abs_zero]
    exact hK

theorem abs_log_sub_log_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / c := by
  have key : ∀ x y : ℝ, c ≤ x → c ≤ y → Real.log x - Real.log y ≤ |x - y| / c := by
    intro x y hx hy
    have hx0 : 0 < x := hc.trans_le hx
    have hy0 : 0 < y := hc.trans_le hy
    rw [← Real.log_div hx0.ne' hy0.ne']
    rcases le_total y x with hxy | hxy
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
      have h2 : x / y - 1 = (x - y) / y := by field_simp
      calc Real.log (x / y) ≤ (x - y) / y := h1.trans h2.le
        _ ≤ (x - y) / c := div_le_div_of_nonneg_left (by linarith) hc hy
        _ = |x - y| / c := by rw [abs_of_nonneg (by linarith)]
    · have : Real.log (x / y) ≤ 0 :=
        Real.log_nonpos (div_pos hx0 hy0).le ((div_le_one hy0).mpr hxy)
      exact this.trans (div_nonneg (abs_nonneg _) hc.le)
  rw [abs_sub_le_iff]
  exact ⟨key a b ha hb, by rw [abs_sub_comm]; exact key b a hb ha⟩

/-- The standard exponential law is in the regular class with parameters `1, 1, 1, 1`. -/
theorem regLaw_expPM : RegLaw 1 1 1 1 expPM := by
  have hmean : lawMean expPM = 1 := integral_id_expMeasure_one
  have hvar : lawVar expPM = 1 := by
    show ∫ x, (x - lawMean expPM) ^ 2 ∂(expMeasure 1) = 1
    rw [hmean, integral_sub_one_sq_expMeasure_one]
  refine ⟨⟨fun x => if 0 < x then Real.exp (-x) else 0, ?_, ?_, ?_, ?_, ?_⟩, hmean,
    hvar.symm.le, hvar.le⟩
  · exact Measurable.ite measurableSet_Ioi (measurable_id.neg.exp) measurable_const
  · intro x; dsimp only; split_ifs <;> positivity
  · intro x hx; simp [not_lt.mpr hx]
  · intro x
    dsimp only
    split_ifs
    · simp
    · positivity
  · show expMeasure 1 = _
    rw [expMeasure_one_eq_withDensity]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with x hx
    rw [exponentialPDF_eq]
    congr 1
    rcases lt_or_gt_of_ne hx with h | h
    · simp [not_le.mpr h, not_lt.mpr h.le]
    · simp [h, h.le]

end

end PGM
