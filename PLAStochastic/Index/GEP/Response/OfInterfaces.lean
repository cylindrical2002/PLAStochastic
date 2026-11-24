import PLAStochastic.Index.GEP.Response.Defs
import PLAStochastic.Index.GEP.Additive.OfInputs

/-!
# WP4 reduction: JR §5, mixture-path differentiation and integration by parts

`jointResponse_of_interfaces`: the score calculus along mixture paths (`ScoreCalculus`) and
the derivative decompositions JR (R) (`InfluenceDecomp`) imply `JointResponse`.  Everything
here is proved; the two inputs are the leaves of `PLAStochastic/Index/GEP/Response/Defs.lean`.

Steps (`research/2026-09-28-gep-closure/joint-response.md` §5):
1. `testFn_integral`: Fubini, `∫ (∫_{(0,x)} j) dρ = ∫_0^∞ j(t) ρ(t,∞) dt`.
2. On the class, `∫_0^∞ ν(t,∞) dt = 1` and `∫_0^∞ 2t ν(t,∞) dt = v(ν) + 1`.
3. `inflDecomp_integral_sub_le`: if `J' = a + 2qx + r`, then
   `|∫ J dν₁ - ∫ J dν₀| ≤ |q| |v₁ - v₀| + ε d_η(ν₀, ν₁)` (boundary terms vanish: the primitive
   is taken from `0`, where the laws put no mass, and the tails decay like `e^{-θx}`).
4. `RegLaw.mix`: the class is convex; `v` is affine along the path.
5. Mean value theorem along `s ↦ F(ν_s)`.
6. The output distance: truncated sign tests `signTest` realise `d_η` of the outputs by
   bounded tests (the easy half of the duality), and `R → ∞`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

variable {D θ vlo vhi : ℝ}

/-! ## 1. Fubini for primitives -/

theorem measureReal_Ioi_eq (ρ : ProbabilityMeasure ℝ) (x : ℝ) :
    (ρ : Measure ℝ).real (Ioi x) = 1 - cdf (ρ : Measure ℝ) x := by
  rw [cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

theorem measurable_measureReal_Ioi (ρ : ProbabilityMeasure ℝ) :
    Measurable fun x => (ρ : Measure ℝ).real (Ioi x) := by
  simp_rw [measureReal_Ioi_eq]
  exact measurable_const.sub (monotone_cdf _).measurable

/-- **Fubini for primitives.**  `∫ φ_j dρ = ∫_0^∞ j(t) ρ(t,∞) dt`, where `φ_j = testFn j`. -/
theorem testFn_integral {ρ : Measure ℝ} [IsFiniteMeasure ρ] {j : ℝ → ℝ}
    (hj : AEStronglyMeasurable j (volume.restrict (Ioi (0 : ℝ))))
    (hint : Integrable (fun t => j t * ρ.real (Ioi t)) (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (testFn j) ρ ∧ ∫ x, testFn j x ∂ρ = ∫ t in Ioi 0, j t * ρ.real (Ioi t) := by
  set μ₂ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ₂
  set F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 < p.1}.indicator (fun p => j p.2) with hF_def
  have hFm : AEStronglyMeasurable F (ρ.prod μ₂) :=
    (hj.comp_snd).indicator (measurableSet_lt measurable_snd measurable_fst)
  have hsec : ∀ t, (fun x => F (x, t)) = (Ioi t).indicator (fun _ => j t) := by
    intro t; ext x
    simp only [hF_def, Set.indicator, Set.mem_ofPred_eq, Set.mem_Ioi]
  have hsec' : ∀ x, (fun t => F (x, t)) = (Iio x).indicator j := by
    intro x; ext t
    simp only [hF_def, Set.indicator, Set.mem_ofPred_eq, Set.mem_Iio]
  have hnorm : ∀ t, ∫ x, ‖F (x, t)‖ ∂ρ = ‖j t * ρ.real (Ioi t)‖ := by
    intro t
    have : (fun x => ‖F (x, t)‖) = (Ioi t).indicator (fun _ => ‖j t‖) := by
      ext x; rw [show F (x, t) = (fun x => F (x, t)) x from rfl, hsec t]
      by_cases hx : x ∈ Ioi t <;> simp [hx]
    rw [this, integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, norm_mul,
      Real.norm_of_nonneg measureReal_nonneg, mul_comm]
  have hFi : Integrable F (ρ.prod μ₂) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨ae_of_all _ fun t => ?_, ?_⟩
    · rw [hsec t]; exact (integrable_const _).indicator measurableSet_Ioi
    · simp_rw [hnorm]; exact hint.norm
  have h1 : ∀ x, ∫ t, F (x, t) ∂μ₂ = testFn j x := by
    intro x
    rw [show (∫ t, F (x, t) ∂μ₂) = ∫ t, (fun t => F (x, t)) t ∂μ₂ from rfl, hsec' x, hμ₂,
      setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
    rfl
  have h2 : ∀ t, ∫ x, F (x, t) ∂ρ = j t * ρ.real (Ioi t) := by
    intro t
    rw [show (∫ x, F (x, t) ∂ρ) = ∫ x, (fun x => F (x, t)) x ∂ρ from rfl, hsec t,
      integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]
  refine ⟨?_, ?_⟩
  · have := hFi.integral_prod_left
    simp_rw [h1] at this
    exact this
  · have e1 := integral_prod F hFi
    have e2 := integral_prod_symm F hFi
    simp_rw [h1] at e1
    simp_rw [h2] at e2
    rw [← e1, e2]

/-! ## 2. Tails and moments on the class -/

theorem RegLaw.measure_Iic_zero {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) :
    (ν : Measure ℝ) (Iic 0) = 0 := by
  have h0 := h.cdf_eq_zero (le_refl (0 : ℝ))
  rw [cdf_eq_real, measureReal_def, ENNReal.toReal_eq_zero_iff] at h0
  exact h0.resolve_right (measure_ne_top _ _)

theorem RegLaw.ae_pos {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) :
    ∀ᵐ x ∂(ν : Measure ℝ), 0 < x := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext a; simp [not_lt]
  rw [this]
  exact h.measure_Iic_zero

/-- A.e. statements on `(0,∞)` for Lebesgue measure hold `ν`-a.e. on the class. -/
theorem RegLaw.ae_of_ae_Ioi {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    {p : ℝ → Prop} (hp : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), p x) :
    ∀ᵐ x ∂(ν : Measure ℝ), p x := by
  obtain ⟨f, -, -, -, -, hν⟩ := h.density
  have hac : (ν : Measure ℝ) ≪ volume := by
    rw [hν]; exact withDensity_absolutelyContinuous _ _
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioi 0 → p x :=
    (ae_restrict_iff' measurableSet_Ioi).mp hp
  filter_upwards [hac.ae_le h1, h.ae_pos] with x hx hx0 using hx hx0

theorem RegLaw.measureReal_Ioi_le {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (x : ℝ) : (ν : Measure ℝ).real (Ioi x) ≤ D / θ * Real.exp (-θ * x) := by
  rw [measureReal_Ioi_eq]; exact h.one_sub_cdf_le' hθ x

/-- `j(t) ν(t,∞)` is integrable on `(0,∞)` when `|j t| ≤ M e^{ηt}` with `η < θ`. -/
theorem RegLaw.integrable_mul_tail {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) {η M : ℝ} (hηθ : η < θ) {j : ℝ → ℝ}
    (hj : AEStronglyMeasurable j (volume.restrict (Ioi (0 : ℝ))))
    (hb : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |j t| ≤ M * Real.exp (η * t)) :
    Integrable (fun t => j t * (ν : Measure ℝ).real (Ioi t))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hD := h.D_nonneg
  refine Integrable.mono'
    ((integrableOn_exp_mul_Ioi (a := η - θ) (by linarith) 0).const_mul (|M| * (D / θ)))
    (hj.mul (measurable_measureReal_Ioi ν).aestronglyMeasurable) ?_
  filter_upwards [hb] with t ht
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg measureReal_nonneg]
  have hexp : Real.exp ((η - θ) * t) = Real.exp (η * t) * Real.exp (-θ * t) := by
    rw [← Real.exp_add]; ring_nf
  calc |j t| * (ν : Measure ℝ).real (Ioi t)
      ≤ (|M| * Real.exp (η * t)) * (D / θ * Real.exp (-θ * t)) :=
        mul_le_mul (ht.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le))
          (h.measureReal_Ioi_le hθ t) measureReal_nonneg
          (mul_nonneg (abs_nonneg M) (Real.exp_pos _).le)
    _ = |M| * (D / θ) * Real.exp ((η - θ) * t) := by rw [hexp]; ring

theorem testFn_one {x : ℝ} (hx : 0 < x) : testFn (fun _ => (1 : ℝ)) x = x := by
  rw [testFn, setIntegral_const, Real.volume_real_Ioo_of_le hx.le, smul_eq_mul, mul_one,
    sub_zero]

theorem testFn_two_mul {x : ℝ} (hx : 0 < x) : testFn (fun t => 2 * t) x = x ^ 2 := by
  rw [testFn, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le,
    intervalIntegral.integral_const_mul, integral_id]
  ring

theorem le_exp_div {η t : ℝ} (hη : 0 < η) : t ≤ Real.exp (η * t) / η := by
  rw [le_div_iff₀ hη]
  have := Real.add_one_le_exp (η * t)
  linarith

/-- On the class: `∫_0^∞ ν(t,∞) dt = 1`, and the identity is integrable. -/
theorem RegLaw.tail_mean {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) :
    Integrable (fun x => x) (ν : Measure ℝ) ∧
      ∫ t in Ioi 0, (ν : Measure ℝ).real (Ioi t) = 1 := by
  have hb : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |(fun _ => (1 : ℝ)) t| ≤
      1 * Real.exp (0 * t) := ae_of_all _ fun t => by simp
  obtain ⟨hI, hE⟩ := testFn_integral (ρ := (ν : Measure ℝ)) aestronglyMeasurable_const
    (h.integrable_mul_tail hθ hθ aestronglyMeasurable_const hb)
  have hae : testFn (fun _ => (1 : ℝ)) =ᵐ[(ν : Measure ℝ)] fun x => x := by
    filter_upwards [h.ae_pos] with x hx using testFn_one hx
  refine ⟨hI.congr hae, ?_⟩
  have hm := h.mean
  rw [lawMean, ← integral_congr_ae hae, hE] at hm
  simpa using hm

/-- On the class: `∫_0^∞ 2t ν(t,∞) dt = v(ν) + 1`, and `x²` is integrable. -/
theorem RegLaw.tail_sq {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) :
    Integrable (fun x => x ^ 2) (ν : Measure ℝ) ∧
      ∫ t in Ioi 0, 2 * t * (ν : Measure ℝ).real (Ioi t) = lawVar ν + 1 := by
  have hθ2 : 0 < θ / 2 := by linarith
  have hb : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |(fun t => 2 * t) t| ≤
      (4 / θ) * Real.exp (θ / 2 * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [abs_of_pos (by linarith)]
    have := le_exp_div (t := t) hθ2
    rw [div_div_eq_mul_div] at this
    calc 2 * t ≤ 2 * (Real.exp (θ / 2 * t) * 2 / θ) := by linarith
      _ = 4 / θ * Real.exp (θ / 2 * t) := by ring
  obtain ⟨hI, hE⟩ := testFn_integral (ρ := (ν : Measure ℝ)) (j := fun t => 2 * t)
    ((continuous_const.mul continuous_id).aestronglyMeasurable)
    (h.integrable_mul_tail hθ (by linarith) (continuous_const.mul continuous_id).aestronglyMeasurable hb)
  have hae : testFn (fun t => 2 * t) =ᵐ[(ν : Measure ℝ)] fun x => x ^ 2 := by
    filter_upwards [h.ae_pos] with x hx using testFn_two_mul hx
  have hsq : Integrable (fun x => x ^ 2) (ν : Measure ℝ) := hI.congr hae
  refine ⟨hsq, ?_⟩
  have hid := (h.tail_mean hθ).1
  have hv : lawVar ν = ∫ x, x ^ 2 ∂(ν : Measure ℝ) - 1 := by
    have hm := h.mean
    rw [lawMean] at hm
    rw [lawVar, h.mean]
    have e : (fun x : ℝ => (x - 1) ^ 2) = fun x => (x ^ 2 - 2 * x) + 1 := by ext x; ring
    rw [e, integral_add (f := fun x => x ^ 2 - 2 * x) (g := fun _ => (1 : ℝ))
        (hsq.sub (hid.const_mul 2)) (integrable_const _),
      integral_sub (f := fun x => x ^ 2) (g := fun x => 2 * x) hsq (hid.const_mul 2),
      integral_const_mul, hm, integral_const, probReal_univ, smul_eq_mul]
    ring
  have hE' : ∫ x, x ^ 2 ∂(ν : Measure ℝ) =
      ∫ t in Ioi 0, 2 * t * (ν : Measure ℝ).real (Ioi t) := (integral_congr_ae hae).symm.trans hE
  rw [hv, hE']
  ring

/-! ## 3. Integration by parts for a decomposed influence -/

theorem AEPrimitive.aestronglyMeasurable {J j : ℝ → ℝ} (h : AEPrimitive J j) :
    AEStronglyMeasurable j (volume.restrict (Ioi (0 : ℝ))) := by
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc 0 (n : ℝ) := by
    ext x
    simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, -⟩
      exact hx
  rw [hU, aestronglyMeasurable_iUnion_iff]
  intro n
  exact (h.1 n).1.aestronglyMeasurable

/-- `∫ J dν = c + ∫_0^∞ j(t) ν(t,∞) dt` for an a.e. primitive of exponential growth. -/
theorem RegLaw.integral_of_primitive {ν : ProbabilityMeasure ℝ} (h : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) {J j : ℝ → ℝ} {c η M : ℝ} (hηθ : η < θ)
    (hj : AEStronglyMeasurable j (volume.restrict (Ioi (0 : ℝ))))
    (hc : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), J x = c + ∫ t in (0 : ℝ)..x, j t)
    (hb : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |j t| ≤ M * Real.exp (η * t)) :
    ∫ x, J x ∂(ν : Measure ℝ) = c + ∫ t in Ioi 0, j t * (ν : Measure ℝ).real (Ioi t) := by
  have hc' : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), J x = c + testFn j x := by
    filter_upwards [hc, ae_restrict_mem measurableSet_Ioi] with x hx hx0
    rw [hx, intervalIntegral.integral_of_le (le_of_lt hx0), integral_Ioc_eq_integral_Ioo]
    rfl
  have hJ : J =ᵐ[(ν : Measure ℝ)] fun x => c + testFn j x := h.ae_of_ae_Ioi hc'
  obtain ⟨hI, hE⟩ := testFn_integral (ρ := (ν : Measure ℝ)) hj
    (h.integrable_mul_tail hθ hηθ hj hb)
  rw [integral_congr_ae hJ, integral_add (integrable_const _) hI, hE]
  simp

/-- **Integration by parts (JR §5).**  If `J' = a + 2qx + r` with `|q| ≤ K`, `|r| ≤ ε e^{ηx}`,
then `|∫ J dν₁ - ∫ J dν₀| ≤ K |v₁ - v₀| + ε d_η(ν₀, ν₁)`: the constant term meets
`∫ ΔF = 0` and the linear term meets `∫ x ΔF = -(v₁ - v₀)/2`. -/
theorem inflDecomp_integral_sub_le {ν₀ ν₁ : ProbabilityMeasure ℝ}
    (h₀ : RegLaw D θ vlo vhi ν₀) (h₁ : RegLaw D θ vlo vhi ν₁) (hθ : 0 < θ) {η ε K : ℝ}
    (hη : 0 < η) (hηθ : η < θ) {J : ℝ → ℝ} (hJ : InflDecomp η ε K J) :
    |(∫ x, J x ∂(ν₁ : Measure ℝ)) - ∫ x, J x ∂(ν₀ : Measure ℝ)| ≤
      K * |lawVar ν₁ - lawVar ν₀| + ε * dEta η ν₀ ν₁ := by
  obtain ⟨a, q, r, hq, hprim, hr⟩ := hJ
  obtain ⟨hII, c, hc⟩ := hprim
  set j : ℝ → ℝ := fun t => a + 2 * q * t + r t with hj_def
  have hjm : AEStronglyMeasurable j (volume.restrict (Ioi (0 : ℝ))) :=
    AEPrimitive.aestronglyMeasurable ⟨hII, c, hc⟩
  have hpm : AEStronglyMeasurable (fun t : ℝ => a + 2 * q * t) (volume.restrict (Ioi (0 : ℝ))) :=
    (continuous_const.add (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hrm : AEStronglyMeasurable r (volume.restrict (Ioi (0 : ℝ))) := by
    have e : r = fun t => j t - (a + 2 * q * t) := by ext t; simp [hj_def]
    rw [e]; exact hjm.sub hpm
  -- growth of `j`
  have hjb : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      |j t| ≤ (|a| + 2 * |q| / η + ε) * Real.exp (η * t) := by
    filter_upwards [hr, ae_restrict_mem measurableSet_Ioi] with t ht ht0
    have ht0' : (0 : ℝ) < t := ht0
    have e1 : 1 ≤ Real.exp (η * t) := Real.one_le_exp (by positivity)
    have e2 := le_exp_div (t := t) hη
    have h2 : |2 * q * t| ≤ 2 * |q| / η * Real.exp (η * t) := by
      rw [abs_mul, abs_mul, abs_of_pos ht0', abs_two]
      calc 2 * |q| * t ≤ 2 * |q| * (Real.exp (η * t) / η) :=
            mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = 2 * |q| / η * Real.exp (η * t) := by ring
    calc |j t| ≤ |a| + |2 * q * t| + |r t| := by
          simp only [hj_def]
          exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq
            (by ring)
      _ ≤ |a| * Real.exp (η * t) + 2 * |q| / η * Real.exp (η * t) + ε * Real.exp (η * t) :=
          add_le_add (add_le_add (le_mul_of_one_le_right (abs_nonneg _) e1) h2) ht
      _ = (|a| + 2 * |q| / η + ε) * Real.exp (η * t) := by ring
  have hrb : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |r t| ≤ |ε| * Real.exp (η * t) := by
    filter_upwards [hr] with t ht
    exact ht.trans (mul_le_mul_of_nonneg_right (le_abs_self ε) (Real.exp_pos _).le)
  -- the three tail integrals on each law
  have key : ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∫ x, J x ∂(ν : Measure ℝ) = c + a + q * (lawVar ν + 1) +
        ∫ t in Ioi 0, r t * (ν : Measure ℝ).real (Ioi t) := by
    intro ν hν
    rw [hν.integral_of_primitive hθ hηθ hjm hc hjb]
    have i1 := hν.integrable_mul_tail hθ hθ (j := fun _ => (1 : ℝ)) aestronglyMeasurable_const
      (M := 1) (ae_of_all _ fun t => by simp)
    have i2 : Integrable (fun t => 2 * t * (ν : Measure ℝ).real (Ioi t))
        (volume.restrict (Ioi (0 : ℝ))) := by
      have hθ2 : 0 < θ / 2 := by linarith
      refine hν.integrable_mul_tail hθ (η := θ / 2) (M := 4 / θ) (by linarith)
        ((continuous_const.mul continuous_id).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [abs_of_pos (by linarith)]
      have := le_exp_div (t := t) hθ2
      rw [div_div_eq_mul_div] at this
      calc 2 * t ≤ 2 * (Real.exp (θ / 2 * t) * 2 / θ) := by linarith
        _ = 4 / θ * Real.exp (θ / 2 * t) := by ring
    have i3 := hν.integrable_mul_tail hθ hηθ hrm hrb
    have e : (fun t => j t * (ν : Measure ℝ).real (Ioi t)) = fun t =>
        a * (1 * (ν : Measure ℝ).real (Ioi t)) + q * (2 * t * (ν : Measure ℝ).real (Ioi t)) +
          r t * (ν : Measure ℝ).real (Ioi t) := by
      ext t; simp only [hj_def]; ring
    rw [e, integral_add (f := fun t => a * (1 * (ν : Measure ℝ).real (Ioi t)) +
          q * (2 * t * (ν : Measure ℝ).real (Ioi t)))
        (g := fun t => r t * (ν : Measure ℝ).real (Ioi t)) ((i1.const_mul a).add (i2.const_mul q)) i3,
      integral_add (f := fun t => a * (1 * (ν : Measure ℝ).real (Ioi t)))
        (g := fun t => q * (2 * t * (ν : Measure ℝ).real (Ioi t))) (i1.const_mul a)
        (i2.const_mul q), integral_const_mul a, integral_const_mul q, (hν.tail_sq hθ).2]
    simp only [one_mul]
    rw [(hν.tail_mean hθ).2]
    ring
  rw [key ν₀ h₀, key ν₁ h₁]
  have i30 := h₀.integrable_mul_tail hθ hηθ hrm hrb
  have i31 := h₁.integrable_mul_tail hθ hηθ hrm hrb
  have hdiff : (∫ t in Ioi 0, r t * (ν₁ : Measure ℝ).real (Ioi t)) -
      ∫ t in Ioi 0, r t * (ν₀ : Measure ℝ).real (Ioi t) =
      ∫ t in Ioi 0, r t * (cdf (ν₀ : Measure ℝ) t - cdf (ν₁ : Measure ℝ) t) := by
    rw [← integral_sub i31 i30]
    congr 1; ext t
    rw [measureReal_Ioi_eq, measureReal_Ioi_eq]; ring
  have hbd : |∫ t in Ioi 0, r t * (cdf (ν₀ : Measure ℝ) t - cdf (ν₁ : Measure ℝ) t)| ≤
      ε * dEta η ν₀ ν₁ := by
    rw [dEta, ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le
      ((h₀.integrableOn_dEta h₁ hηθ hθ).const_mul ε) ?_
    filter_upwards [hr] with t ht
    rw [Real.norm_eq_abs, abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  have hq' : |q * (lawVar ν₁ + 1) - q * (lawVar ν₀ + 1)| ≤ K * |lawVar ν₁ - lawVar ν₀| := by
    rw [show q * (lawVar ν₁ + 1) - q * (lawVar ν₀ + 1) = q * (lawVar ν₁ - lawVar ν₀) by ring,
      abs_mul]
    exact mul_le_mul_of_nonneg_right hq (abs_nonneg _)
  calc |c + a + q * (lawVar ν₁ + 1) + (∫ t in Ioi 0, r t * (ν₁ : Measure ℝ).real (Ioi t)) -
        (c + a + q * (lawVar ν₀ + 1) + ∫ t in Ioi 0, r t * (ν₀ : Measure ℝ).real (Ioi t))|
      = |(q * (lawVar ν₁ + 1) - q * (lawVar ν₀ + 1)) +
          ((∫ t in Ioi 0, r t * (ν₁ : Measure ℝ).real (Ioi t)) -
            ∫ t in Ioi 0, r t * (ν₀ : Measure ℝ).real (Ioi t))| := by ring_nf
    _ ≤ K * |lawVar ν₁ - lawVar ν₀| + ε * dEta η ν₀ ν₁ := by
        rw [hdiff]
        exact (abs_add_le _ _).trans (add_le_add hq' hbd)

/-! ## 4. The mixture path stays in the class -/

theorem mixPM_zero (ν₀ ν₁ : ProbabilityMeasure ℝ) : mixPM ν₀ ν₁ 0 = ν₀ := by
  apply Subtype.ext
  show (mixPM ν₀ ν₁ 0 : Measure ℝ) = ν₀
  rw [coe_mixPM, mixParam_of_mem ⟨le_rfl, zero_le_one⟩]
  simp

theorem mixPM_one (ν₀ ν₁ : ProbabilityMeasure ℝ) : mixPM ν₀ ν₁ 1 = ν₁ := by
  apply Subtype.ext
  show (mixPM ν₀ ν₁ 1 : Measure ℝ) = ν₁
  rw [coe_mixPM, mixParam_of_mem ⟨zero_le_one, le_rfl⟩]
  simp

/-- **Convexity of the class** (JR §1): mixtures stay in `RegLaw D θ vlo vhi`. -/
theorem RegLaw.mix {ν₀ ν₁ : ProbabilityMeasure ℝ} (h₀ : RegLaw D θ vlo vhi ν₀)
    (h₁ : RegLaw D θ vlo vhi ν₁) (hθ : 0 < θ) (s : ℝ) :
    RegLaw D θ vlo vhi (mixPM ν₀ ν₁ s) := by
  set σ := mixParam s with hσ_def
  have hσ0 : 0 ≤ σ := mixParam_nonneg s
  have hσ1 : σ ≤ 1 := mixParam_le_one s
  have h1σ : 0 ≤ 1 - σ := by linarith
  obtain ⟨f₀, hf₀m, hf₀0, hf₀z, hf₀D, hν₀⟩ := h₀.density
  obtain ⟨f₁, hf₁m, hf₁0, hf₁z, hf₁D, hν₁⟩ := h₁.density
  obtain ⟨hid₀, -⟩ := h₀.tail_mean hθ
  obtain ⟨hid₁, -⟩ := h₁.tail_mean hθ
  obtain ⟨hsq₀, -⟩ := h₀.tail_sq hθ
  obtain ⟨hsq₁, -⟩ := h₁.tail_sq hθ
  have hne₀ : ENNReal.ofReal (1 - σ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hne₁ : ENNReal.ofReal σ ≠ ⊤ := ENNReal.ofReal_ne_top
  -- integrals against the mixture
  have hint : ∀ {g : ℝ → ℝ}, Integrable g (ν₀ : Measure ℝ) → Integrable g (ν₁ : Measure ℝ) →
      ∫ x, g x ∂(mixPM ν₀ ν₁ s : Measure ℝ) =
        (1 - σ) * ∫ x, g x ∂(ν₀ : Measure ℝ) + σ * ∫ x, g x ∂(ν₁ : Measure ℝ) := by
    intro g hg₀ hg₁
    rw [coe_mixPM, integral_add_measure (hg₀.smul_measure hne₀) (hg₁.smul_measure hne₁),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal h1σ,
      ENNReal.toReal_ofReal hσ0, smul_eq_mul, smul_eq_mul]
  have hsq1 : ∀ ν : ProbabilityMeasure ℝ, Integrable (fun x => x) (ν : Measure ℝ) →
      Integrable (fun x => x ^ 2) (ν : Measure ℝ) →
      Integrable (fun x : ℝ => (x - 1) ^ 2) (ν : Measure ℝ) := by
    intro ν hi hs
    have e : (fun x : ℝ => (x - 1) ^ 2) = fun x => x ^ 2 - 2 * x + 1 := by ext x; ring
    rw [e]; exact (hs.sub (hi.const_mul 2)).add (integrable_const _)
  have hmean : lawMean (mixPM ν₀ ν₁ s) = 1 := by
    rw [lawMean, hint hid₀ hid₁]
    have m₀ := h₀.mean; have m₁ := h₁.mean
    rw [lawMean] at m₀ m₁
    rw [m₀, m₁]; ring
  have hvar : lawVar (mixPM ν₀ ν₁ s) = (1 - σ) * lawVar ν₀ + σ * lawVar ν₁ := by
    rw [lawVar, hmean, hint (hsq1 ν₀ hid₀ hsq₀) (hsq1 ν₁ hid₁ hsq₁), lawVar, lawVar, h₀.mean,
      h₁.mean]
  have hv₀ := h₀.var_ge; have hv₀' := h₀.var_le
  have hv₁ := h₁.var_ge; have hv₁' := h₁.var_le
  have a1 := mul_le_mul_of_nonneg_left hv₀ h1σ
  have a2 := mul_le_mul_of_nonneg_left hv₁ hσ0
  have a3 := mul_le_mul_of_nonneg_left hv₀' h1σ
  have a4 := mul_le_mul_of_nonneg_left hv₁' hσ0
  refine ⟨⟨fun x => (1 - σ) * f₀ x + σ * f₁ x, (hf₀m.const_mul _).add (hf₁m.const_mul _),
    fun x => add_nonneg (mul_nonneg h1σ (hf₀0 x)) (mul_nonneg hσ0 (hf₁0 x)),
    fun x hx => by simp [hf₀z x hx, hf₁z x hx], fun x => ?_, ?_⟩, hmean, ?_, ?_⟩
  · have b1 := mul_le_mul_of_nonneg_left (hf₀D x) h1σ
    have b2 := mul_le_mul_of_nonneg_left (hf₁D x) hσ0
    calc (1 - σ) * f₀ x + σ * f₁ x ≤ (1 - σ) * (D * Real.exp (-θ * x)) +
          σ * (D * Real.exp (-θ * x)) := add_le_add b1 b2
      _ = D * Real.exp (-θ * x) := by ring
  · rw [coe_mixPM, ← hσ_def, hν₀, hν₁, ← withDensity_smul _ hf₀m.ennreal_ofReal,
      ← withDensity_smul _ hf₁m.ennreal_ofReal,
      ← withDensity_add_left (hf₀m.ennreal_ofReal.const_smul _)]
    congr 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_add (mul_nonneg h1σ (hf₀0 x)) (mul_nonneg hσ0 (hf₁0 x)),
      ENNReal.ofReal_mul h1σ, ENNReal.ofReal_mul hσ0]
  · rw [hvar]; nlinarith
  · rw [hvar]; nlinarith

/-! ## 5. The mean value theorem along the path -/

theorem abs_sub_le_of_deriv {f f' : ℝ → ℝ} {B : ℝ} (hc : ContinuousOn f (Icc 0 1))
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Ioo (0 : ℝ) 1, |f' s| ≤ B) : |f 1 - f 0| ≤ B := by
  obtain ⟨c, hc', he⟩ := exists_hasDerivAt_eq_slope f f' zero_lt_one hc hd
  rw [sub_zero, div_one] at he
  rw [← he]
  exact hb c hc'

/-- **The finite difference along the mixture path** (JR §5). -/
theorem mixDiff_bound {F : ProbabilityMeasure ℝ → ℝ} {J : ProbabilityMeasure ℝ → ℝ → ℝ}
    {ν₀ ν₁ : ProbabilityMeasure ℝ} (h₀ : RegLaw D θ vlo vhi ν₀) (h₁ : RegLaw D θ vlo vhi ν₁)
    (hθ : 0 < θ) {η ε K : ℝ} (hη : 0 < η) (hηθ : η < θ) (hF : MixDiff F J ν₀ ν₁)
    (hdec : ∀ s ∈ Ioo (0 : ℝ) 1, InflDecomp η ε K (J (mixPM ν₀ ν₁ s))) :
    |F ν₁ - F ν₀| ≤ K * |lawVar ν₁ - lawVar ν₀| + ε * dEta η ν₀ ν₁ := by
  have h := abs_sub_le_of_deriv hF.1 hF.2
    (fun s hs => inflDecomp_integral_sub_le h₀ h₁ hθ hη hηθ (hdec s hs))
  simpa only [mixPM_one, mixPM_zero] using h

/-! ## 6. The output distance through bounded sign tests -/

theorem OutTest.nonneg {η M : ℝ} {ψ : ℝ → ℝ} (h : OutTest η M ψ) : 0 ≤ M := by
  have := h.2 0 le_rfl
  simp only [mul_zero, Real.exp_zero, mul_one] at this
  exact (abs_nonneg _).trans this

theorem OutTest.mono {η η' M : ℝ} {ψ : ℝ → ℝ} (h : OutTest η M ψ) (hη : η ≤ η') :
    OutTest η' M ψ := by
  refine ⟨h.1, fun x hx => (h.2 x hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hη hx))
    h.nonneg

/-- The truncated sign test: `φ' = e^{ηt} sign(F₀ - F₁)` on `(0, R]`. -/
def signTest (η R : ℝ) (ρ₀ ρ₁ : ProbabilityMeasure ℝ) (t : ℝ) : ℝ :=
  (Ioc 0 R).indicator (fun t => Real.exp (η * t) *
    (if cdf (ρ₁ : Measure ℝ) t ≤ cdf (ρ₀ : Measure ℝ) t then 1 else -1)) t

theorem measurable_signTest (η R : ℝ) (ρ₀ ρ₁ : ProbabilityMeasure ℝ) :
    Measurable (signTest η R ρ₀ ρ₁) :=
  ((measurable_const.mul measurable_id).exp.mul
    (Measurable.ite (measurableSet_le (monotone_cdf _).measurable (monotone_cdf _).measurable)
      measurable_const measurable_const)).indicator measurableSet_Ioc

theorem abs_signTest_le (η R : ℝ) (ρ₀ ρ₁ : ProbabilityMeasure ℝ) (t : ℝ) :
    |signTest η R ρ₀ ρ₁ t| ≤ (Ioc 0 R).indicator (fun t => Real.exp (η * t)) t := by
  unfold signTest
  by_cases ht : t ∈ Ioc 0 R
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, abs_mul, abs_of_pos (Real.exp_pos _)]
    split_ifs <;> simp
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, abs_zero]

theorem outTest_signTest (η R : ℝ) (ρ₀ ρ₁ : ProbabilityMeasure ℝ) :
    OutTest η 1 (signTest η R ρ₀ ρ₁) := by
  refine ⟨measurable_signTest η R ρ₀ ρ₁, fun t _ => (abs_signTest_le η R ρ₀ ρ₁ t).trans ?_⟩
  rw [one_mul]
  by_cases ht : t ∈ Ioc 0 R
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]; exact (Real.exp_pos _).le

/-- The sign test integrates the CDF difference: `∫ φ dρ₁ - ∫ φ dρ₀ = ∫_0^R e^{ηt}|F₀ - F₁|`. -/
theorem integral_testFn_signTest_sub {η R : ℝ} (hη : 0 ≤ η) (ρ₀ ρ₁ : ProbabilityMeasure ℝ) :
    (∫ y, testFn (signTest η R ρ₀ ρ₁) y ∂(ρ₁ : Measure ℝ)) -
        ∫ y, testFn (signTest η R ρ₀ ρ₁) y ∂(ρ₀ : Measure ℝ) =
      ∫ t in Ioc 0 R, Real.exp (η * t) *
        |cdf (ρ₀ : Measure ℝ) t - cdf (ρ₁ : Measure ℝ) t| := by
  set ψ := signTest η R ρ₀ ρ₁ with hψ
  have hψm : AEStronglyMeasurable ψ (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_signTest η R ρ₀ ρ₁).aestronglyMeasurable
  have hint : ∀ ρ : ProbabilityMeasure ℝ, Integrable (fun t => ψ t * (ρ : Measure ℝ).real (Ioi t))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro ρ
    refine Integrable.mono'
      ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul
        (Real.exp ((η + 1) * R)))
      (hψm.mul (measurable_measureReal_Ioi ρ).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg measureReal_nonneg]
    have hρ1 : (ρ : Measure ℝ).real (Ioi t) ≤ 1 := measureReal_le_one
    refine (mul_le_of_le_one_right (abs_nonneg _) hρ1).trans ?_
    refine (abs_signTest_le η R ρ₀ ρ₁ t).trans ?_
    by_cases ht : t ∈ Ioc 0 R
    · rw [Set.indicator_of_mem ht, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [ht.1, ht.2])
    · rw [Set.indicator_of_notMem ht]; positivity
  rw [(testFn_integral hψm (hint ρ₁)).2, (testFn_integral hψm (hint ρ₀)).2,
    ← integral_sub (hint ρ₁) (hint ρ₀)]
  have e : (fun t => ψ t * (ρ₁ : Measure ℝ).real (Ioi t) - ψ t * (ρ₀ : Measure ℝ).real (Ioi t)) =
      (Ioc 0 R).indicator (fun t => Real.exp (η * t) *
        |cdf (ρ₀ : Measure ℝ) t - cdf (ρ₁ : Measure ℝ) t|) := by
    ext t
    rw [measureReal_Ioi_eq, measureReal_Ioi_eq, hψ]
    unfold signTest
    by_cases ht : t ∈ Ioc 0 R
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      split_ifs with hc
      · rw [abs_of_nonneg (by linarith)]; ring
      · rw [abs_of_neg (by linarith)]; ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; ring
  rw [e, setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr Ioc_subset_Ioi_self]

/-- If all truncations of a nonnegative integrand are bounded by `B ≥ 0`, so is its integral
over `(0,∞)`. -/
theorem integral_Ioi_le_of_Ioc {g : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ n : ℕ, ∫ t in Ioc 0 (n : ℝ), g t ≤ B) : ∫ t in Ioi 0, g t ≤ B := by
  by_cases hi : IntegrableOn g (Ioi 0)
  · have hT := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_natCast_atTop_atTop
    refine le_of_tendsto' hT fun n => ?_
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
    exact h n
  · rw [integral_undef hi]; exact hB

/-! ## 7. The reduction -/

/-- **JR §5: the joint response from the score calculus and the decompositions (R).** -/
theorem jointResponse_of_interfaces (hS : ScoreCalculus) (hR : InfluenceDecomp) :
    JointResponse := by
  intro D θ vlo vhi hD hθ hvlo hv
  obtain ⟨η₀, e₁, hη₀, hS'⟩ := hS D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηm, hηm, hR'⟩ := hR D θ vlo vhi hD hθ hvlo hv
  set η := min (min η₀ ηm) (θ / 8) with hη_def
  have hη : 0 < η := lt_min (lt_min hη₀ hηm) (by linarith)
  have hηη₀ : η ≤ η₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hηm' : η ≤ ηm := (min_le_left _ _).trans (min_le_right _ _)
  have hηθ8 : η ≤ θ / 8 := min_le_right _ _
  have hηθ : η < θ := by linarith
  obtain ⟨K, e₂, ε, hK, hε0, hεT, hdec⟩ := hR' η hη hηm'
  refine ⟨η, K, max e₁ e₂, ε, hη, by linarith, hK, hε0, hεT, ?_⟩
  intro eps heps ν₀ ν₁ h₀ h₁
  have he₁ : e₁ ≤ eps := (le_max_left _ _).trans heps
  have he₂ : e₂ ≤ eps := (le_max_right _ _).trans heps
  obtain ⟨hA, hV, hO⟩ := hS' eps he₁ ν₀ ν₁ h₀ h₁
  have hmix : ∀ s, RegLaw D θ vlo vhi (mixPM ν₀ ν₁ s) := fun s => h₀.mix h₁ hθ s
  have hd0 := dEta_nonneg η ν₀ ν₁
  refine ⟨?_, ?_, ?_⟩
  · have h := mixDiff_bound h₀ h₁ hθ hη hηθ hA (fun s _ => (hdec eps he₂ _ (hmix s)).1)
    simpa only [lawA, zero_mul, zero_add] using h
  · have h := mixDiff_bound h₀ h₁ hθ hη hηθ hV (fun s _ => (hdec eps he₂ _ (hmix s)).2.1)
    simpa only [lawV, zero_mul, zero_add] using h
  · refine integral_Ioi_le_of_Ioc
      (add_nonneg (mul_nonneg (hε0 eps) hd0) (mul_nonneg hK (abs_nonneg _))) fun n => ?_
    have ht := outTest_signTest η n (lawPhi eps ν₀) (lawPhi eps ν₁)
    have h := mixDiff_bound h₀ h₁ hθ hη hηθ (hO 1 _ (ht.mono hηη₀))
      (fun s _ => by simpa only [one_mul] using (hdec eps he₂ _ (hmix s)).2.2 1 _ ht)
    have e := integral_testFn_signTest_sub (R := (n : ℝ)) hη.le (lawPhi eps ν₀) (lawPhi eps ν₁)
    simp only [outFn] at h
    rw [e] at h
    have := le_abs_self (∫ t in Ioc 0 (n : ℝ), Real.exp (η * t) *
      |cdf (lawPhi eps ν₀ : Measure ℝ) t - cdf (lawPhi eps ν₁ : Measure ℝ) t|)
    linarith

end

end PGM
