import PLAStochastic.Swing.Gaussian.Survival.FiniteLikelihood

/-! The finite-to-infinite error for actual Gaussian survival probabilities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Subtracting the two actual stopping identities isolates the unobserved future exit. -/
theorem gaussianHalfLine_late_exit_exp_identity
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (n : ℕ) :
    (∫ ω in {ω | (n : WithTop ℕ) < gaussianHalfLineExit X x a ω ∧
        gaussianHalfLineExit X x a ω ≠ ⊤},
      Real.exp (2*a*gaussianHalfLineOvershoot X x a ω) ∂μ) =
    ∫ ω in gaussianHalfLineSurvives X x a n,
      Real.exp (-2*a*gaussianDriftWalk X x a n ω) ∂μ := by
  have := hi.isProbabilityMeasure
  let τ := gaussianHalfLineExit X x a
  let A := {ω | τ ω ≤ (n : WithTop ℕ)}
  let F := {ω | τ ω ≠ ⊤}
  let C := {ω | (n : WithTop ℕ) < τ ω ∧ τ ω ≠ ⊤}
  let E := fun ω => Real.exp (2*a*gaussianHalfLineOvershoot X x a ω)
  let Z := fun ω => Real.exp (-2*a*gaussianDriftWalk X x a (capDiscreteTime (τ ω) n) ω)
  have hτ : Measurable τ := (gaussianHalfLineExit_isStoppingTime hX x a).measurable'
  have hA : MeasurableSet A := measurableSet_le hτ measurable_const
  have hF : MeasurableSet F := (hτ (measurableSet_singleton ⊤)).compl
  have hC : MeasurableSet C := (measurableSet_lt measurable_const hτ).inter hF
  have hAF : A ⊆ F := by
    intro ω hω
    exact ne_top_of_le_ne_top WithTop.coe_ne_top hω
  have hu : A ∪ C = F := by
    ext ω
    constructor
    · rintro (h | h)
      · exact hAF h
      · exact h.2
    · intro h
      by_cases hn : τ ω ≤ (n : WithTop ℕ)
      · exact Or.inl hn
      · exact Or.inr ⟨lt_of_not_ge hn, h⟩
  have hd : Disjoint A C := disjoint_left.mpr (fun _ h h' => not_lt_of_ge h h'.1)
  have hE : Integrable E μ :=
    gaussianHalfLineOvershoot_integrable_exp hX hi hG hx ha.le (by positivity)
  have hZ : Integrable Z μ := capDiscreteTime_potential_integrable hτ
    (gaussianDriftWalk_integrable_exp hX hi hG x a (-2*a)) n
  have hZA : (∫ ω in A, Z ω ∂μ) = ∫ ω in A, E ω ∂μ := by
    apply setIntegral_congr_fun hA
    intro ω hω
    have ht : gaussianHalfLineExit X x a ω ≠ ⊤ := hAF hω
    dsimp only [Z, E]
    rw [capDiscreteTime_eq_of_le hω]
    simp only [gaussianHalfLineOvershoot, if_neg ht, gaussianHalfLineExitPosition, τ]
    congr 1
    ring
  have hAc : Aᶜ = gaussianHalfLineSurvives X x a n := by
    ext ω
    change (¬ τ ω ≤ (n : WithTop ℕ)) ↔ _
    rw [not_le]
    exact lt_gaussianHalfLineExit_iff X x a n ω
  have hZB : (∫ ω in Aᶜ, Z ω ∂μ) = ∫ ω in gaussianHalfLineSurvives X x a n,
      Real.exp (-2*a*gaussianDriftWalk X x a n ω) ∂μ := by
    rw [← hAc]
    apply setIntegral_congr_fun hA.compl
    intro ω hω
    have ht : (n : WithTop ℕ) < τ ω := lt_of_not_ge hω
    dsimp only [Z]
    rw [capDiscreteTime_eq_of_lt ht]
  have hb := integral_add_compl hA hZ
  rw [hZA, hZB] at hb
  have hz : (∫ ω, Z ω ∂μ) = Real.exp (-2*a*x) :=
    gaussianHalfLine_capped_exp_integral hX hi hG x a n
  rw [hz] at hb
  have he : Real.exp (-2*a*x) = ∫ ω in F, E ω ∂μ :=
    gaussianHalfLine_overshoot_identity hX hi hG hx ha
  rw [← hu, setIntegral_union hd hC hE.integrableOn hE.integrableOn] at he
  change (∫ ω in C, E ω ∂μ) = _
  linarith


/-- The probability difference counts paths whose true first exit lies after the horizon. -/
theorem gaussianHalfLineSurvives_sub_infinite [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) (x a : ℝ) (n : ℕ) :
    μ.real (gaussianHalfLineSurvives X x a n)-gaussianInfiniteSurvival X μ x a =
    μ.real {ω | (n : WithTop ℕ) < gaussianHalfLineExit X x a ω ∧
      gaussianHalfLineExit X x a ω ≠ ⊤} := by
  have ht : MeasurableSet {ω | gaussianHalfLineExit X x a ω = ⊤} :=
    (gaussianHalfLineExit_isStoppingTime hX x a).measurable' (measurableSet_singleton ⊤)
  have hs : {ω | gaussianHalfLineExit X x a ω = ⊤} ⊆ gaussianHalfLineSurvives X x a n := by
    intro ω hω
    apply (lt_gaussianHalfLineExit_iff X x a n ω).mp
    rw [hω]
    exact WithTop.coe_lt_top n
  have he : gaussianHalfLineSurvives X x a n \ {ω | gaussianHalfLineExit X x a ω = ⊤} =
      {ω | (n : WithTop ℕ) < gaussianHalfLineExit X x a ω ∧ gaussianHalfLineExit X x a ω ≠ ⊤} := by
    ext ω
    simp only [Set.mem_sdiff, mem_ofPred_eq, lt_gaussianHalfLineExit_iff]
  rw [← he, measureReal_sdiff hs ht]
  rfl

/-- No future-increment independence is assumed: the error is bounded by the stopped identity. -/
theorem gaussianHalfLineSurvives_sub_infinite_le_weighted
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (n : ℕ) :
    0 ≤ μ.real (gaussianHalfLineSurvives X x a n)-gaussianInfiniteSurvival X μ x a ∧
    μ.real (gaussianHalfLineSurvives X x a n)-gaussianInfiniteSurvival X μ x a ≤
      Real.exp (-2*a*x)*μ.real (gaussianHalfLineSurvives X x (-a) n) := by
  have := hi.isProbabilityMeasure
  rw [gaussianHalfLineSurvives_sub_infinite hX]
  constructor
  · exact measureReal_nonneg
  let C := {ω | (n : WithTop ℕ) < gaussianHalfLineExit X x a ω ∧
      gaussianHalfLineExit X x a ω ≠ ⊤}
  have hτ := (gaussianHalfLineExit_isStoppingTime hX x a).measurable'
  have hC : MeasurableSet C := (measurableSet_lt measurable_const hτ).inter
    (hτ (measurableSet_singleton ⊤)).compl
  have hb : μ.real C ≤ ∫ ω in C, Real.exp (2*a*gaussianHalfLineOvershoot X x a ω) ∂μ := by
    have h := setIntegral_mono_on (integrable_const (1 : ℝ))
      (gaussianHalfLineOvershoot_integrable_exp hX hi hG hx ha.le
        (θ := 2*a) (by positivity)).integrableOn
      hC (fun ω _ => Real.one_le_exp (mul_nonneg (by positivity)
        (gaussianHalfLineOvershoot_nonneg X x a ω)))
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using h
  calc
    _ ≤ ∫ ω in C, Real.exp (2*a*gaussianHalfLineOvershoot X x a ω) ∂μ := hb
    _ = ∫ ω in gaussianHalfLineSurvives X x a n,
        Real.exp (-2*a*gaussianDriftWalk X x a n ω) ∂μ :=
      gaussianHalfLine_late_exit_exp_identity hX hi hG hx ha n
    _ = _ := gaussianHalfLineSurvives_weighted_endpoint hX hi hG n x a

/-- The actual finite survival correction has the exponential Gaussian factor in C.3. -/
theorem gaussianSurvivalEvent_sub_infinite_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    0 ≤ μ.real (gaussianSurvivalEvent X x a n)-gaussianInfiniteSurvival X μ x a ∧
    μ.real (gaussianSurvivalEvent X x a n)-gaussianInfiniteSurvival X μ x a ≤
      gaussianBallotConstant*(x+1)*(Real.sqrt (n : ℝ))⁻¹*Real.exp (-a^2*(n : ℝ)/2) := by
  obtain ⟨h0, hb⟩ := gaussianHalfLineSurvives_sub_infinite_le_weighted hX hi hG hx ha n
  rw [gaussianHalfLineSurvives_eq_survivalEvent hx] at h0 hb
  refine ⟨h0, hb.trans ?_⟩
  have hneg := gaussianHalfLineSurvives_negative_drift_le hX hi hG n x ha.le
  have hballot := gaussian_ballot_bound hX hi hG hx (a := 0) (by norm_num) (by norm_num) hn
  simp only [zero_add] at hballot
  calc
    _ ≤ Real.exp (-2*a*x)*(Real.exp (a*x-(n : ℝ)*a^2/2)*
        μ.real (gaussianHalfLineSurvives X x 0 n)) := by
      exact mul_le_mul_of_nonneg_left hneg (Real.exp_pos _).le
    _ = Real.exp (-a*x-(n : ℝ)*a^2/2)*μ.real (gaussianSurvivalEvent X x 0 n) := by
      rw [gaussianHalfLineSurvives_eq_survivalEvent hx, ← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-a^2*(n : ℝ)/2)*(gaussianBallotConstant*(x+1)*(Real.sqrt (n : ℝ))⁻¹) := by
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg ha.le hx]
      · exact hballot
      · exact measureReal_nonneg
      · exact (Real.exp_pos _).le
    _ = _ := by ring

/- The C.3 correction estimate in the normalization used by the small-drift
   renewal limit.  Keeping this as a separate interface avoids repeatedly
   redoing the positivity/division argument at call sites. -/
theorem gaussianSurvivalEvent_normalized_sub_infinite_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    0 ≤ (μ.real (gaussianSurvivalEvent X x a n) -
      gaussianInfiniteSurvival X μ x a) / (2*a) ∧
    (μ.real (gaussianSurvivalEvent X x a n) -
      gaussianInfiniteSurvival X μ x a) / (2*a) ≤
      (gaussianBallotConstant*(x+1)*(Real.sqrt (n : ℝ))⁻¹*
        Real.exp (-a^2*(n : ℝ)/2)) / (2*a) := by
  obtain ⟨h0, hb⟩ := gaussianSurvivalEvent_sub_infinite_bound hX hi hG hx ha hn
  have h2a : 0 < (2*a : ℝ) := by positivity
  constructor
  · exact div_nonneg h0 h2a.le
  · exact div_le_div_of_nonneg_right hb h2a.le

/- A convenient sequential C.3 interface: once the explicit normalized
  finite-horizon error is known to vanish, the finite survival quotient has
  the same limit as the infinite quotient. -/
theorem gaussianSurvivalEvent_normalized_tendsto_of_error
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℕ → ℝ} {w : ℝ} {n : ℕ → ℕ}
    (hx : ∀ k, 0 ≤ x k) (ha : ∀ k, 0 < a k) (ha' : ∀ k, a k ≤ 1/2)
    (hn : ∀ k, 0 < n k) (hxlim : Tendsto x atTop (𝓝 w))
    (halim : Tendsto a atTop (𝓝 0)) (hw : 0 ≤ w)
    (herror : Tendsto (fun k =>
      (gaussianBallotConstant*(x k+1)*(Real.sqrt (n k : ℝ))⁻¹*
        Real.exp (-(a k)^2*(n k : ℝ)/2)) / (2*a k)) atTop (𝓝 0)) :
    Tendsto (fun k => μ.real (gaussianSurvivalEvent X (x k) (a k) (n k)) /
      (2*a k)) atTop (𝓝 (gaussianRenewalPotential X μ w)) := by
  have hinf := gaussianInfiniteSurvival_small_drift hX hi hG hx ha ha'
    hxlim halim hw
  let d : ℕ → ℝ := fun k =>
    (μ.real (gaussianSurvivalEvent X (x k) (a k) (n k)) -
      gaussianInfiniteSurvival X μ (x k) (a k)) / (2*a k)
  have hd0 : ∀ k, 0 ≤ d k := by
    intro k
    exact (gaussianSurvivalEvent_normalized_sub_infinite_bound hX hi hG
      (hx k) (ha k) (hn k)).1
  have hdle : ∀ k, d k ≤
      (gaussianBallotConstant*(x k+1)*(Real.sqrt (n k : ℝ))⁻¹*
        Real.exp (-(a k)^2*(n k : ℝ)/2)) / (2*a k) := by
    intro k
    exact (gaussianSurvivalEvent_normalized_sub_infinite_bound hX hi hG
      (hx k) (ha k) (hn k)).2
  have hdz : Tendsto d atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herror
    · exact Eventually.of_forall hd0
    · exact Eventually.of_forall hdle
  have hadd : Tendsto (fun k =>
      gaussianInfiniteSurvival X μ (x k) (a k) / (2*a k) + d k) atTop
      (𝓝 (gaussianRenewalPotential X μ w)) := by
    simpa only [add_zero] using hinf.add hdz
  apply hadd.congr'
  filter_upwards [] with k
  dsimp [d]
  ring

/- The explicit C.3 error tends to zero whenever the inverse diffusive
   scale tends to zero.  This isolates the only horizon-growth input needed
   by the finite-to-infinite passage: `(a k * sqrt (n k))⁻¹ → 0`. -/
theorem gaussianSurvivalEvent_normalized_error_tendsto_zero_of_diffusive_scale
    {x a : ℕ → ℝ} {n : ℕ → ℕ} {w : ℝ}
    (hxlim : Tendsto x atTop (𝓝 w))
    (hden : Tendsto (fun k => (a k * Real.sqrt (n k : ℝ))⁻¹) atTop (𝓝 0))
    (hx : ∀ k, 0 ≤ x k) (ha : ∀ k, 0 < a k) (hn : ∀ k, 0 < n k) :
    Tendsto (fun k =>
      (gaussianBallotConstant*(x k+1)*(Real.sqrt (n k : ℝ))⁻¹*
        Real.exp (-(a k)^2*(n k : ℝ)/2)) / (2*a k)) atTop (𝓝 0) := by
  have hconst : Tendsto (fun k => gaussianBallotConstant * (x k + 1) *
      (a k * Real.sqrt (n k : ℝ))⁻¹) atTop (𝓝 0) := by
    have hx1 : Tendsto (fun k => x k + 1) atTop (𝓝 (w + 1)) :=
      hxlim.add_const 1
    have hp1 : Tendsto (fun k => gaussianBallotConstant * (x k + 1)) atTop
        (𝓝 (gaussianBallotConstant * (w + 1))) :=
      tendsto_const_nhds.mul hx1
    have hp := hp1.mul hden
    simpa using hp
  have hupper : ∀ᶠ k in atTop, 0 ≤
      (gaussianBallotConstant * (x k + 1) *
        (a k * Real.sqrt (n k : ℝ))⁻¹) *
        Real.exp (-(a k)^2*(n k : ℝ)/2) := by
    filter_upwards [] with k
    have harg : 0 ≤ a k * Real.sqrt (n k : ℝ) :=
      mul_nonneg (ha k).le (Real.sqrt_nonneg _)
    have hd : 0 ≤ (a k * Real.sqrt (n k : ℝ))⁻¹ := inv_nonneg.mpr harg
    have hx1 : 0 ≤ x k + 1 := by linarith [hx k]
    exact mul_nonneg (mul_nonneg (mul_nonneg gaussianBallotConstant_pos.le hx1) hd)
      (Real.exp_pos _).le
  have hle : ∀ᶠ k in atTop,
      (gaussianBallotConstant * (x k + 1) *
        (a k * Real.sqrt (n k : ℝ))⁻¹) *
        Real.exp (-(a k)^2*(n k : ℝ)/2) ≤
      gaussianBallotConstant * (x k + 1) *
        (a k * Real.sqrt (n k : ℝ))⁻¹ := by
    filter_upwards [] with k
    have harg : -(a k)^2*(n k : ℝ)/2 ≤ 0 := by
      have ha2 : 0 ≤ (a k)^2 := sq_nonneg _
      have hn0 : 0 ≤ (n k : ℝ) := by exact_mod_cast (Nat.zero_le (n k))
      nlinarith
    have he : Real.exp (-(a k)^2*(n k : ℝ)/2) ≤ 1 :=
      (Real.exp_le_one_iff.mpr harg)
    exact mul_le_of_le_one_right
      (by
        have harg' : 0 ≤ a k * Real.sqrt (n k : ℝ) :=
          mul_nonneg (ha k).le (Real.sqrt_nonneg _)
        have hd : 0 ≤ (a k * Real.sqrt (n k : ℝ))⁻¹ := inv_nonneg.mpr harg'
        exact mul_nonneg (mul_nonneg gaussianBallotConstant_pos.le (by linarith [hx k])) hd) he
  have hprod : Tendsto (fun k =>
      (gaussianBallotConstant * (x k + 1) *
        (a k * Real.sqrt (n k : ℝ))⁻¹) *
        Real.exp (-(a k)^2*(n k : ℝ)/2)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconst
    · exact hupper
    · exact hle
  have hfun : (fun k =>
      (gaussianBallotConstant*(x k+1)*(Real.sqrt (n k : ℝ))⁻¹*
        Real.exp (-(a k)^2*(n k : ℝ)/2)) / (2*a k)) =
      (fun k =>
      (gaussianBallotConstant * (x k + 1) *
        (a k * Real.sqrt (n k : ℝ))⁻¹) *
        Real.exp (-(a k)^2*(n k : ℝ)/2) / 2) := by
    funext k
    have hsn : Real.sqrt (n k : ℝ) ≠ 0 := by
      exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast (hn k))
    field_simp [ha k |>.ne', hsn]
  rw [hfun]
  simpa using (hprod.div_const (2 : ℝ))

/- The denominator hypothesis is automatic under divergence of the
   diffusive scale itself. -/
theorem gaussianSurvivalEvent_normalized_error_tendsto_zero_of_diffusive_scale_atTop
    {x a : ℕ → ℝ} {n : ℕ → ℕ} {w : ℝ}
    (hxlim : Tendsto x atTop (𝓝 w))
    (hscale : Tendsto (fun k => a k * Real.sqrt (n k : ℝ)) atTop atTop)
    (hx : ∀ k, 0 ≤ x k) (ha : ∀ k, 0 < a k) (hn : ∀ k, 0 < n k) :
    Tendsto (fun k =>
      (gaussianBallotConstant*(x k+1)*(Real.sqrt (n k : ℝ))⁻¹*
        Real.exp (-(a k)^2*(n k : ℝ)/2)) / (2*a k)) atTop (𝓝 0) := by
  apply gaussianSurvivalEvent_normalized_error_tendsto_zero_of_diffusive_scale
    hxlim (tendsto_inv_atTop_zero.comp hscale) hx ha hn

/-! A one-shot finite-horizon C.3 passage.  This is the form used in the
renewal limit: the spatial offset converges, the drift vanishes, and the
finite horizon dominates the diffusive scale. -/
theorem gaussianSurvivalEvent_normalized_tendsto_of_diffusive_scale_atTop
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℕ → ℝ} {n : ℕ → ℕ} {w : ℝ}
    (hx : ∀ k, 0 ≤ x k) (ha : ∀ k, 0 < a k) (ha' : ∀ k, a k ≤ 1/2)
    (hn : ∀ k, 0 < n k) (hxlim : Tendsto x atTop (𝓝 w))
    (halim : Tendsto a atTop (𝓝 0)) (hw : 0 ≤ w)
    (hscale : Tendsto (fun k => a k * Real.sqrt (n k : ℝ)) atTop atTop) :
    Tendsto (fun k => μ.real (gaussianSurvivalEvent X (x k) (a k) (n k)) /
      (2*a k)) atTop (𝓝 (gaussianRenewalPotential X μ w)) := by
  apply gaussianSurvivalEvent_normalized_tendsto_of_error hX hi hG
    hx ha ha' hn hxlim halim hw
  exact gaussianSurvivalEvent_normalized_error_tendsto_zero_of_diffusive_scale_atTop
    hxlim hscale hx ha hn

end SwingRepair

namespace SwingRepair
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
noncomputable section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- For fixed offset and drift, finite-horizon survival converges to the
    infinite survival probability.  This is the direct subtraction form of
    the decreasing-event continuity theorem and is useful when passing a
    bridge horizon to infinity before taking a small-drift limit. -/
theorem gaussianSurvivalEvent_sub_infinite_tendsto_zero [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) {x a : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => μ.real (gaussianSurvivalEvent X x a n) -
      gaussianInfiniteSurvival X μ x a) atTop (𝓝 0) := by
  have hfin := gaussianSurvivalEvent_tendsto_infinite (μ := μ) (x := x) (a := a) hX hx
  have hsub := hfin.sub_const (gaussianInfiniteSurvival X μ x a)
  simpa using hsub

/-- The same convergence after division by any fixed positive normalizer. -/
theorem gaussianSurvivalEvent_sub_infinite_div_tendsto_zero [IsFiniteMeasure μ]
    (hX : ∀ n, Measurable (X n)) {x a c : ℝ} (hx : 0 ≤ x) (_hc : c ≠ 0) :
    Tendsto (fun n : ℕ =>
      (μ.real (gaussianSurvivalEvent X x a n) -
        gaussianInfiniteSurvival X μ x a) / c) atTop (𝓝 0) := by
  have h0 := gaussianSurvivalEvent_sub_infinite_tendsto_zero (μ := μ) (x := x) (a := a) hX hx
  simpa using h0.div_const c

end
end SwingRepair
