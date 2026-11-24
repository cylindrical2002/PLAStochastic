import PLAStochastic.Index.GEP.Universality.StrongApproxInterface
import PLAStochastic.Index.GEP.LayerLaw.WeightedDistance
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# WP5, D4: weighted-distance tools

Blueprint `kmt-blueprint/main.tex` Lemma 8.6 (`lem:wtools`) for the lower-integral distance
`dEtaL γ μ ρ = ∫_0^∞ e^{γx} |F_μ(x) - F_ρ(x)| dx`:

* (a) `dEtaL_triangle`;
* (b) `dEtaL_le_coupling`, `dEtaL_map_le`: a coupling bound `E |U - V| e^{γ max(U,V)}`;
* (c) `lintegral_exp_le_of_tail_real`, `lintegral_Ioi_exp_mul_tail_le`: an exponential tail
  `P(r ≤ U) ≤ C e^{-cr}` gives `E e^{γ'U} ≤ 1 + C` for `γ' ≤ c/2`, and the weighted tail
  integral beyond `r₀` is at most `(2C/c) e^{-c r₀/2}`;
* (d) `lintegral_exp_mul_measure_Icc_le`: the Tonelli bound for a band `p.1 ≤ x ≤ p.2`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ## (a) Triangle inequality -/

theorem measurable_dEtaL_integrand (γ : ℝ) (μ ρ : ProbabilityMeasure ℝ) :
    Measurable fun x => ENNReal.ofReal
      (Real.exp (γ * x) * |cdf (μ : Measure ℝ) x - cdf (ρ : Measure ℝ) x|) :=
  ((measurable_const.mul measurable_id).exp.mul
    ((monotone_cdf (μ : Measure ℝ)).measurable.sub
      (monotone_cdf (ρ : Measure ℝ)).measurable).abs).ennreal_ofReal

theorem dEtaL_triangle (γ : ℝ) (μ ρ σ : ProbabilityMeasure ℝ) :
    dEtaL γ μ σ ≤ dEtaL γ μ ρ + dEtaL γ ρ σ := by
  unfold dEtaL
  rw [← lintegral_add_left (measurable_dEtaL_integrand γ μ ρ)]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (Real.exp_pos _).le

/-! ## (b) Coupling bound -/

/-- `d_γ(ν, ρ) ≤ E_π |X - Y| e^{γ max(X, Y)}` for a coupling `π` of `ν` and `ρ`. -/
theorem dEtaL_le_coupling {ν ρ : ProbabilityMeasure ℝ} {π : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure π] (h1 : π.map Prod.fst = (ν : Measure ℝ))
    (h2 : π.map Prod.snd = (ρ : Measure ℝ)) {γ : ℝ} (hγ : 0 ≤ γ) :
    dEtaL γ ν ρ ≤ ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| * Real.exp (γ * max p.1 p.2)) ∂π := by
  unfold dEtaL
  calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
        (Real.exp (γ * x) * |cdf (ν : Measure ℝ) x - cdf (ρ : Measure ℝ) x|)
      ≤ ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (γ * x)) *
          π {p | min p.1 p.2 ≤ x ∧ x < max p.1 p.2} := by
        refine lintegral_mono fun x => ?_
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← ofReal_measureReal]
        exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (abs_cdf_sub_le_coupling h1 h2 x))
    _ ≤ ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| * |Real.exp (γ * max p.1 p.2)|) ∂π :=
        lintegral_exp_mul_measure_le hγ
    _ = ∫⁻ p, ENNReal.ofReal (|p.1 - p.2| * Real.exp (γ * max p.1 p.2)) ∂π := by
        simp_rw [abs_of_pos (Real.exp_pos _)]

/-- The law of a measurable real map as a probability measure. -/
def lawPM {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU : Measurable U) : ProbabilityMeasure ℝ :=
  ⟨P.map U, Measure.isProbabilityMeasure_map hU.aemeasurable⟩

theorem coe_lawPM {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {U : Ω → ℝ} (hU : Measurable U) : ((lawPM P hU : ProbabilityMeasure ℝ) : Measure ℝ) = P.map U :=
  rfl

/-- The coupling bound for two random variables on one space. -/
theorem dEtaL_map_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V) {γ : ℝ} (hγ : 0 ≤ γ) :
    dEtaL γ (lawPM P hU) (lawPM P hV) ≤
      ∫⁻ ω, ENNReal.ofReal (|U ω - V ω| * Real.exp (γ * max (U ω) (V ω))) ∂P := by
  have hUV : Measurable fun ω => (U ω, V ω) := hU.prodMk hV
  have h1 : (P.map fun ω => (U ω, V ω)).map Prod.fst = ((lawPM P hU : ProbabilityMeasure ℝ) : Measure ℝ) := by
    rw [coe_lawPM, Measure.map_map measurable_fst hUV]; rfl
  have h2 : (P.map fun ω => (U ω, V ω)).map Prod.snd = ((lawPM P hV : ProbabilityMeasure ℝ) : Measure ℝ) := by
    rw [coe_lawPM, Measure.map_map measurable_snd hUV]; rfl
  have : IsProbabilityMeasure (P.map fun ω => (U ω, V ω)) :=
    Measure.isProbabilityMeasure_map hUV.aemeasurable
  refine (dEtaL_le_coupling h1 h2 hγ).trans (le_of_eq ?_)
  rw [lintegral_map _ hUV]
  exact ((measurable_fst.sub measurable_snd).abs.mul
    (measurable_const.mul (measurable_fst.max measurable_snd)).exp).ennreal_ofReal

/-! ## (c) Exponential tails -/

/-- `∫_0^∞ e^{-a t} dt = 1/a` as a lower integral. -/
theorem lintegral_Ioi_exp_neg_mul {a : ℝ} (ha : 0 < a) (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (K * Real.exp (-(a * t))) = ENNReal.ofReal (K / a) := by
  have hint : IntegrableOn (fun t : ℝ => K * Real.exp (-(a * t))) (Ioi 0) := by
    have h := (exp_neg_integrableOn_Ioi 0 ha).const_mul K
    simp only [neg_mul] at h
    exact h
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t _ => by positivity))]
  congr 1
  rw [integral_const_mul]
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 ha
  simp only [mul_zero, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, smul_eq_mul, mul_one] at h
  rw [h, div_eq_mul_inv]

/-- Layer cake: `E e^{γ'U} = 1 + ∫_0^∞ γ' e^{γ't} P(t ≤ U) dt` for `U ≥ 0`. -/
theorem lintegral_exp_eq_layer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {U : Ω → ℝ} (hU : Measurable U) (hU0 : ∀ ω, 0 ≤ U ω) {γ' : ℝ}
    (hγ : 0 < γ') :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ' * U ω)) ∂P =
      1 + ∫⁻ t in Ioi (0 : ℝ), P {ω | t ≤ U ω} * ENNReal.ofReal (γ' * Real.exp (γ' * t)) := by
  have hg : ∀ x : ℝ, ∫ t in (0 : ℝ)..x, γ' * Real.exp (γ' * t) = Real.exp (γ' * x) - 1 := by
    intro x
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left
      (fun t => Real.exp t) hγ.ne', integral_exp]
    simp only [mul_zero, Real.exp_zero, smul_eq_mul]
    field_simp
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul P (f := U) (g := fun t => γ' * Real.exp (γ' * t))
    (ae_of_all _ hU0) hU.aemeasurable
    (fun t _ => (Continuous.intervalIntegrable (by fun_prop) 0 t))
    (ae_of_all _ fun t => by positivity)
  simp_rw [hg] at hlc
  have e : ∀ ω, ENNReal.ofReal (Real.exp (γ' * U ω)) =
      ENNReal.ofReal (Real.exp (γ' * U ω) - 1) + 1 := by
    intro ω
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by
      have := Real.add_one_le_exp (γ' * U ω)
      have : 0 ≤ γ' * U ω := mul_nonneg hγ.le (hU0 ω)
      linarith) zero_le_one]
    congr 1; ring
  simp_rw [e]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one, hlc,
    add_comm]

/-- **Exponential moment from an exponential tail** (blueprint Lemma 8.6(c), first part):
`P(r ≤ U) ≤ C e^{-cr}` for `r > 0` and `0 < γ' ≤ c/2` give `E e^{γ' U} ≤ 1 + C`. -/
theorem lintegral_exp_le_of_tail_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {U : Ω → ℝ} (hU : Measurable U) (hU0 : ∀ ω, 0 ≤ U ω)
    {C c γ' : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ') (hγc : γ' ≤ c / 2)
    (htail : ∀ r : ℝ, 0 < r → P.real {ω | r ≤ U ω} ≤ C * Real.exp (-(c * r))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (γ' * U ω)) ∂P ≤ ENNReal.ofReal (1 + C) := by
  rw [lintegral_exp_eq_layer P hU hU0 hγ]
  have hcγ : 0 < c - γ' := by linarith
  calc 1 + ∫⁻ t in Ioi (0 : ℝ), P {ω | t ≤ U ω} * ENNReal.ofReal (γ' * Real.exp (γ' * t))
      ≤ 1 + ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (C * γ' * Real.exp (-((c - γ') * t))) := by
        refine add_le_add_right (lintegral_mono_ae
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : t ∈ Ioi (0 : ℝ)) =>
            ?_))) 1
        have ht0 : 0 < t := ht
        rw [← ofReal_measureReal, ← ENNReal.ofReal_mul measureReal_nonneg]
        refine ENNReal.ofReal_le_ofReal ?_
        calc P.real {ω | t ≤ U ω} * (γ' * Real.exp (γ' * t))
            ≤ C * Real.exp (-(c * t)) * (γ' * Real.exp (γ' * t)) :=
              mul_le_mul_of_nonneg_right (htail t ht0) (by positivity)
          _ = C * γ' * Real.exp (-((c - γ') * t)) := by
              rw [show -((c - γ') * t) = -(c * t) + γ' * t by ring, Real.exp_add]; ring
    _ = 1 + ENNReal.ofReal (C * γ' / (c - γ')) := by
        rw [lintegral_Ioi_exp_neg_mul hcγ _ (by positivity)]
    _ ≤ ENNReal.ofReal (1 + C) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : C * γ' / (c - γ') ≤ C := by
          rw [div_le_iff₀ hcγ]
          nlinarith
        linarith

/-- **Weighted tail integral** (blueprint Lemma 8.6(c), second part): for `r₀ ≥ 0`,
`∫_{r₀}^∞ e^{γ' r} P(r ≤ U) dr ≤ (2C/c) e^{-c r₀/2}`. -/
theorem lintegral_Ioi_exp_mul_tail_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {U : Ω → ℝ} {C c γ' : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hγc : γ' ≤ c / 2)
    (htail : ∀ r : ℝ, 0 < r → P.real {ω | r ≤ U ω} ≤ C * Real.exp (-(c * r)))
    (hfin : ∀ r : ℝ, P {ω | r ≤ U ω} ≠ ⊤) {r₀ : ℝ} (hr₀ : 0 ≤ r₀) :
    ∫⁻ r in Ioi r₀, ENNReal.ofReal (Real.exp (γ' * r)) * P {ω | r ≤ U ω} ≤
      ENNReal.ofReal (2 * C / c * Real.exp (-(c * r₀ / 2))) := by
  have hc2 : 0 < c / 2 := by positivity
  calc ∫⁻ r in Ioi r₀, ENNReal.ofReal (Real.exp (γ' * r)) * P {ω | r ≤ U ω}
      ≤ ∫⁻ r in Ioi r₀, ENNReal.ofReal (C * Real.exp (-(c / 2 * r))) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun r hr => ?_))
        have hr0 : 0 < r := lt_of_le_of_lt hr₀ hr
        rw [← ofReal_measureReal (hfin r), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        calc Real.exp (γ' * r) * P.real {ω | r ≤ U ω}
            ≤ Real.exp (γ' * r) * (C * Real.exp (-(c * r))) :=
              mul_le_mul_of_nonneg_left (htail r hr0) (Real.exp_pos _).le
          _ = C * Real.exp (-((c - γ') * r)) := by
              rw [show -((c - γ') * r) = γ' * r + -(c * r) by ring, Real.exp_add]; ring
          _ ≤ C * Real.exp (-(c / 2 * r)) := by
              gcongr
              nlinarith
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (C * Real.exp (-(c / 2 * r₀)) *
          Real.exp (-(c / 2 * r))) := by
        have hmp : MeasurePreserving (fun r : ℝ => r + r₀) volume volume :=
          measurePreserving_add_right volume r₀
        rw [← hmp.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight r₀)]
        have hpre : (fun r : ℝ => r + r₀) ⁻¹' Ioi r₀ = Ioi 0 := by
          ext r; simp
        rw [hpre]
        refine setLIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
        congr 1
        rw [show -(c / 2 * (r + r₀)) = -(c / 2 * r₀) + -(c / 2 * r) by ring, Real.exp_add]
        ring
    _ = ENNReal.ofReal (C * Real.exp (-(c / 2 * r₀)) / (c / 2)) :=
        lintegral_Ioi_exp_neg_mul hc2 _ (by positivity)
    _ = ENNReal.ofReal (2 * C / c * Real.exp (-(c * r₀ / 2))) := by
        congr 1
        rw [show -(c * r₀ / 2) = -(c / 2 * r₀) by ring]
        field_simp

/-! ## (d) The band bound -/

/-- Tonelli: `∫_0^∞ e^{γx} π{p.1 ≤ x ≤ p.2} dx ≤ E_π max(p.2 - p.1, 0) e^{γ p.2}`. -/
theorem lintegral_exp_mul_measure_Icc_le {π : Measure (ℝ × ℝ)} [SFinite π] {γ : ℝ}
    (hγ : 0 ≤ γ) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (γ * x)) * π {p | p.1 ≤ x ∧ x ≤ p.2} ≤
      ∫⁻ p, ENNReal.ofReal (max (p.2 - p.1) 0 * Real.exp (γ * p.2)) ∂π := by
  have hU : MeasurableSet {q : ℝ × (ℝ × ℝ) | q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2} :=
    (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_snd.comp measurable_snd))
  have hG : Measurable ({q : ℝ × (ℝ × ℝ) | q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2}.indicator
      fun q => ENNReal.ofReal (Real.exp (γ * q.1))) :=
    ((measurable_const.mul measurable_fst).exp.ennreal_ofReal).indicator hU
  have hT : ∀ x : ℝ, MeasurableSet {p : ℝ × ℝ | p.1 ≤ x ∧ x ≤ p.2} := fun x =>
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  calc ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (γ * x)) * π {p | p.1 ≤ x ∧ x ≤ p.2}
      = ∫⁻ x in Ioi (0 : ℝ), (∫⁻ p, {q : ℝ × (ℝ × ℝ) | q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2}.indicator
          (fun q => ENNReal.ofReal (Real.exp (γ * q.1))) (x, p) ∂π) := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_indicator_const (hT x)]
        rfl
    _ = ∫⁻ p, (∫⁻ x in Ioi (0 : ℝ), {q : ℝ × (ℝ × ℝ) | q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2}.indicator
          (fun q => ENNReal.ofReal (Real.exp (γ * q.1))) (x, p)) ∂π :=
        lintegral_lintegral_swap hG.aemeasurable
    _ ≤ ∫⁻ p, ENNReal.ofReal (max (p.2 - p.1) 0 * Real.exp (γ * p.2)) ∂π := by
        refine lintegral_mono fun p => ?_
        have hpt : ∀ x : ℝ, {q : ℝ × (ℝ × ℝ) | q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2}.indicator
            (fun q => ENNReal.ofReal (Real.exp (γ * q.1))) (x, p) ≤
            (Icc p.1 p.2).indicator (fun _ => ENNReal.ofReal (Real.exp (γ * p.2))) x := by
          intro x
          by_cases hx : p.1 ≤ x ∧ x ≤ p.2
          · rw [Set.indicator_of_mem (show (x, p) ∈ {q : ℝ × (ℝ × ℝ) |
                q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2} from hx),
              Set.indicator_of_mem (show x ∈ Icc p.1 p.2 from hx)]
            exact ENNReal.ofReal_le_ofReal
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.2 hγ))
          · rw [Set.indicator_of_notMem (show (x, p) ∉ {q : ℝ × (ℝ × ℝ) |
                q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2} from hx)]
            exact zero_le
        calc ∫⁻ x in Ioi (0 : ℝ), {q : ℝ × (ℝ × ℝ) | q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2}.indicator
              (fun q => ENNReal.ofReal (Real.exp (γ * q.1))) (x, p)
            ≤ ∫⁻ x, {q : ℝ × (ℝ × ℝ) | q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2}.indicator
                (fun q => ENNReal.ofReal (Real.exp (γ * q.1))) (x, p) :=
              setLIntegral_le_lintegral _ _
          _ ≤ ∫⁻ x, (Icc p.1 p.2).indicator
                (fun _ => ENNReal.ofReal (Real.exp (γ * p.2))) x := lintegral_mono hpt
          _ = ENNReal.ofReal (Real.exp (γ * p.2)) * ENNReal.ofReal (p.2 - p.1) := by
              rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
          _ = ENNReal.ofReal (max (p.2 - p.1) 0 * Real.exp (γ * p.2)) := by
              rw [ENNReal.ofReal_mul (le_max_right _ _), mul_comm]
              congr 1
              rcases le_or_gt 0 (p.2 - p.1) with h | h
              · rw [max_eq_left h]
              · rw [max_eq_right h.le, ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_zero]

end

end PGM
