import PLAStochastic.Swing.Ladder.Renewal.EquilibriumOvershoot

/-! # The uniform ladder renewal expansion: interface and verified hypotheses

`eq:uniformladderrenewal` is quoted in `app:limit` from Blanchet and Glynn.
This file states that expansion as an explicit predicate on a parameterised
family of inter-arrival laws, proves the consequences that follow from it by
elementary means, and separately proves — with no renewal theorem — the three
hypotheses that the cited theorem requires of the actual Gaussian ladder
family on a compact positive drift interval.

The expansion itself is **not** proved here.  It is an input, recorded as a
hypothesis wherever it is used; see the module documentation of the project
status for the precise remaining gap.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The renewal function `U(u) = U([0,u])`. -/
noncomputable def ladderRenewalFunction (ν : Measure ℝ) (u : ℝ) : ℝ :=
  (ladderRenewalMeasure ν (Icc 0 u)).toReal

/-- The ladder mean `μ = E H`. -/
noncomputable def ladderMean (ν : Measure ℝ) : ℝ := (ladderMeanENN ν).toReal

/-- The ladder second moment `E H²`. -/
noncomputable def ladderSecondMoment (ν : Measure ℝ) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (x^2) ∂ν).toReal

/-- The constant term of the renewal expansion, `E H² / (2 μ²)`. -/
noncomputable def ladderRenewalConstant (ν : Measure ℝ) : ℝ :=
  ladderSecondMoment ν / (2*(ladderMean ν)^2)

/-- `eq:uniformladderrenewal`: the uniform renewal expansion with an
exponentially small remainder, for a family of inter-arrival laws indexed by a
parameter set `S`.  This is the statement quoted from Blanchet–Glynn; it is
carried as a hypothesis, never proved here. -/
def UniformLadderRenewalExpansion (L : ℝ → Measure ℝ) (S : Set ℝ) (C c : ℝ) : Prop :=
  0 < c ∧ 0 ≤ C ∧
    ∀ a ∈ S, ∀ u : ℝ, 0 ≤ u →
      |ladderRenewalFunction (L a) u -
          (u / ladderMean (L a) + ladderRenewalConstant (L a))| ≤ C * Real.exp (-c*u)

/-! ### Elementary consequences of the expansion -/

/-- Blackwell form with an exponential rate: the renewal mass of a window of
length `h` at height `u` is `h/μ` up to `2Ce^{-cu}`, uniformly in the
parameter. -/
theorem uniformLadderRenewal_window {L : ℝ → Measure ℝ} {S : Set ℝ} {C c : ℝ}
    (h : UniformLadderRenewalExpansion L S C c) {a : ℝ} (ha : a ∈ S)
    {u hh : ℝ} (hu : 0 ≤ u) (hhh : 0 ≤ hh) :
    |ladderRenewalFunction (L a) (u+hh) - ladderRenewalFunction (L a) u -
        hh / ladderMean (L a)| ≤ 2*C*Real.exp (-c*u) := by
  obtain ⟨hc, hC, hexp⟩ := h
  have h1 := hexp a ha u hu
  have h2 := hexp a ha (u+hh) (by linarith)
  have hmono : Real.exp (-c*(u+hh)) ≤ Real.exp (-c*u) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hid : ladderRenewalFunction (L a) (u+hh) - ladderRenewalFunction (L a) u -
      hh / ladderMean (L a) =
      (ladderRenewalFunction (L a) (u+hh) -
        ((u+hh) / ladderMean (L a) + ladderRenewalConstant (L a))) -
      (ladderRenewalFunction (L a) u -
        (u / ladderMean (L a) + ladderRenewalConstant (L a))) := by
    ring
  rw [hid]
  calc |_| ≤ |ladderRenewalFunction (L a) (u+hh) -
          ((u+hh) / ladderMean (L a) + ladderRenewalConstant (L a))| +
        |ladderRenewalFunction (L a) u -
          (u / ladderMean (L a) + ladderRenewalConstant (L a))| := abs_sub _ _
    _ ≤ C*Real.exp (-c*(u+hh)) + C*Real.exp (-c*u) := add_le_add h2 h1
    _ ≤ C*Real.exp (-c*u) + C*Real.exp (-c*u) :=
        add_le_add (mul_le_mul_of_nonneg_left hmono hC) le_rfl
    _ = 2*C*Real.exp (-c*u) := by ring

/-- The normalised renewal function converges to `1/μ` with a uniform rate. -/
theorem uniformLadderRenewal_normalized {L : ℝ → Measure ℝ} {S : Set ℝ} {C c : ℝ}
    (h : UniformLadderRenewalExpansion L S C c) {a : ℝ} (ha : a ∈ S)
    {u : ℝ} (hu : 0 < u) :
    |ladderRenewalFunction (L a) u / u - 1 / ladderMean (L a)| ≤
      (C*Real.exp (-c*u) + |ladderRenewalConstant (L a)|)/u := by
  obtain ⟨hc, hC, hexp⟩ := h
  have hb := hexp a ha u hu.le
  have hid : ladderRenewalFunction (L a) u / u - 1 / ladderMean (L a) =
      ((ladderRenewalFunction (L a) u -
          (u / ladderMean (L a) + ladderRenewalConstant (L a))) +
        ladderRenewalConstant (L a))/u := by
    have hune : u ≠ 0 := ne_of_gt hu
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hu]
  refine div_le_div_of_nonneg_right ?_ hu.le
  calc |(ladderRenewalFunction (L a) u -
          (u / ladderMean (L a) + ladderRenewalConstant (L a))) +
        ladderRenewalConstant (L a)|
      ≤ |ladderRenewalFunction (L a) u -
          (u / ladderMean (L a) + ladderRenewalConstant (L a))| +
        |ladderRenewalConstant (L a)| := abs_add_le _ _
    _ ≤ C*Real.exp (-c*u) + |ladderRenewalConstant (L a)| := add_le_add hb le_rfl

/-- Linear growth follows from the expansion, with a uniform constant. -/
theorem uniformLadderRenewal_le_linear {L : ℝ → Measure ℝ} {S : Set ℝ} {C c : ℝ}
    (h : UniformLadderRenewalExpansion L S C c) {a : ℝ} (ha : a ∈ S)
    {u : ℝ} (hu : 0 ≤ u) :
    ladderRenewalFunction (L a) u ≤
      u / ladderMean (L a) + ladderRenewalConstant (L a) + C := by
  obtain ⟨hc, hC, hexp⟩ := h
  have hb := hexp a ha u hu
  have hexp1 : Real.exp (-c*u) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith
  have habs := (abs_le.mp hb).2
  nlinarith

/-! ### The hypotheses of the cited expansion, verified for the actual family -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Blanchet--Glynn's condition (4), uniform strong nonlatticeness, in its
original form: the characteristic functions stay a fixed distance from `1` at
every frequency of size at least `4`, uniformly over the drift interval. -/
theorem gaussianAscendingLadderLaw_uniform_nonlattice
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : μ.map (X 0) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) {θ : ℝ} (hθ : 4 ≤ |θ|) :
    gaussianAscendingLadderCommonDensity M/2 ≤
      ‖1 - charFun (gaussianAscendingLadderLaw X μ a) θ‖ := by
  have hb := gaussianAscendingLadderLaw_uniform_cramer hX hi hG ha haM hθ
  have hrev : ‖(1 : ℂ)‖ - ‖charFun (gaussianAscendingLadderLaw X μ a) θ‖ ≤
      ‖1 - charFun (gaussianAscendingLadderLaw X μ a) θ‖ := norm_sub_norm_le _ _
  rw [norm_one] at hrev
  linarith

/-- The three hypotheses required by the uniform renewal expansion quoted in
`app:limit` hold for the actual strict ascending ladder heights of the
positive-drift Gaussian walk, uniformly over `δ ≤ a ≤ M`:

* `E H_a > 0` with a uniform positive lower bound;
* a uniform exponential moment `sup_a E e^{η H_a} < ∞` for every order `η`
  below the tail rate;
* uniform strong nonlatticeness in Blanchet--Glynn's form (4).

Nothing in this statement is assumed; each part is proved in the preceding
modules from the Gaussian increments.  The family is
`a ↦ gaussianAscendingLadderLaw X μ a` on `Icc δ M`. -/
theorem gaussianAscendingLadder_uniform_renewal_hypotheses
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M η : ℝ} (hδ : 0 < δ)
    (hη : 0 ≤ η) (hηr : η < gaussianAscendingLadderTailRate δ) :
    (∀ a ∈ Icc δ M, gaussianAscendingLadderCommonDensity M ≤
        ∫ ω, gaussianAscendingLadderHeight X a ω ∂μ) ∧
      (∀ a ∈ Icc δ M,
        (∫ ω, Real.exp (η*gaussianAscendingLadderHeight X a ω) ∂μ) ≤
          gaussianAscendingLadderExpMomentBound δ M η) ∧
      (∀ a ∈ Icc δ M, ∀ θ : ℝ, 4 ≤ |θ| →
        gaussianAscendingLadderCommonDensity M/2 ≤
          ‖1 - charFun (gaussianAscendingLadderLaw X μ a) θ‖) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact gaussianAscendingLadderHeight_mean_ge hX hi hG hδ ha.1 ha.2
  · intro a ha
    exact gaussianAscendingLadderHeight_exp_integral_le hX hi hG hδ ha.1 ha.2 hη hηr
  · intro a ha θ hθ
    exact gaussianAscendingLadderLaw_uniform_nonlattice hX hi (hG 0)
      (hδ.le.trans ha.1) ha.2 hθ

/-- Every fixed polynomial moment is also uniformly bounded; this is the
stronger moment hypothesis of the cited theorem's part (ii). -/
theorem gaussianAscendingLadder_uniform_polynomial_moments
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M : ℝ} (hδ : 0 < δ) :
    ∀ a ∈ Icc δ M, ∀ k : ℕ,
      (∫ ω, gaussianAscendingLadderHeight X a ω ^ k ∂μ) ≤
        gaussianAscendingLadderMomentBound δ M k := by
  intro a ha k
  exact gaussianAscendingLadderHeight_pow_integral_le hX hi hG hδ ha.1 ha.2 k

/-! ### The near part of the residual-life integral, unconditionally -/

/-- The part of `eq:overshootrenewalidentity` coming from renewals below `b/2`
vanishes uniformly over the compact drift interval: the renewal mass grows only
linearly and the ladder tail is exponentially small.  No renewal expansion is
used. -/
theorem gaussianAscendingLadderRenewal_near_part_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a b t : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) (hb : 0 ≤ b)
    {N : ℕ} (hN : 0 < N) (hNb : M + (N : ℝ) ≤ b/2 + t) :
    (∫⁻ s in Icc (0 : ℝ) (b/2),
        gaussianAscendingLadderLaw X μ a (Ioi (b+t-s))
          ∂(ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a))) ≤
      ENNReal.ofReal (3*Real.exp (-gaussianAscendingLadderTailRate δ*(N : ℝ))) *
        ENNReal.ofReal (2*Real.exp 1*(1+b/2)/gaussianAscendingLadderCommonDensity M) := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have htail : gaussianAscendingLadderLaw X μ a (Ioi (b/2+t)) ≤
      ENNReal.ofReal (3*Real.exp (-gaussianAscendingLadderTailRate δ*(N : ℝ))) := by
    have hsub : gaussianAscendingLadderLaw X μ a (Ioi (b/2+t)) ≤
        gaussianAscendingLadderLaw X μ a (Ioi (M + (N : ℝ))) :=
      measure_mono (Ioi_subset_Ioi hNb)
    refine hsub.trans ?_
    have hreal := gaussianAscendingLadderLaw_compact_tail hX hi hG hδ hδa haM hN
    calc gaussianAscendingLadderLaw X μ a (Ioi (M + (N : ℝ)))
        = ENNReal.ofReal ((gaussianAscendingLadderLaw X μ a).real (Ioi (M + (N : ℝ)))) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  have hren := gaussianAscendingLadderRenewal_Icc_le hX hi hG ha haM (b := b/2) (by linarith)
  exact (renewalOvershootTail_near_le (gaussianAscendingLadderLaw X μ a)).trans
    (mul_le_mul' htail hren)

end SwingRepair
