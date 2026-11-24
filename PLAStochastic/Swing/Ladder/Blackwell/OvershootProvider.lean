import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.SubstituteIntegral

/-!
# The exact renewal input consumed by Theorem 4.3

The Blanchet--Glynn expansion enters Theorem 4.3 through a single door: the
uniform bounded-Lipschitz comparison between the overshoot law of the actual
positive-drift Gaussian walk above a distant level and the equilibrium
overshoot law, uniformly over drifts in a positive compact strip.  Neither the
expansion's constant term nor its exponential rate is used downstream.

This file isolates that statement as a named predicate, and proves that the
renewal expansion implies it.  Two things are gained.  First, the standing
hypothesis of the paper-level theorem becomes a statement about the actual
Gaussian ladder walk rather than a citation of a literature theorem whose
proof needs Fourier/contour analysis.  Second, the predicate is exactly the
target of a Doeblin/coupling proof on the residual-life chain, for which the
project already owns the Lebesgue minorization of the ladder law and the
abstract two-step Doeblin machinery.

The predicate is a hypothesis, not a theorem.  It is still unproved; see the
dated research record for the precise remaining obligations.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]

/--
`UniformOvershootEquilibriumLimit X μ`: for every positive compact drift strip
`[δ, M]`, every Lipschitz constant `L`, every sup-norm bound `B` and every
accuracy `η`, there is a passage level `b₀ > 0` beyond which the reflected
reward of the actual walk's overshoot agrees with the equilibrium reward to
within `η`, simultaneously for all drifts in the strip and all admissible test
functions.
-/
def UniformOvershootEquilibriumLimit (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ δ M L B η : ℝ, 0 < δ → 0 ≤ M → 0 ≤ L → 0 ≤ B → 0 < η →
    ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b → ∀ f : ℝ → ℝ,
        (∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) →
        (∀ x, |f x| ≤ B) →
          |gaussianWalkReflectedReward X μ f a b -
            swingOvershootReward X μ f a| ≤ η

/--
The scalar form of the same input: the tail of the actual overshoot law above
a distant level agrees with the equilibrium tail, uniformly in the tail level
`t ≥ 0` and in the drift.  No test functions and no transform appear here; it
is a statement about two explicit measures on the line.
-/
def UniformOvershootTailLimit (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ δ M ε : ℝ, 0 < δ → 0 ≤ M → 0 < ε →
    ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ a ∈ Icc δ M, ∀ b : ℝ, b₀ ≤ b → ∀ t : ℝ, 0 ≤ t →
        |(gaussianWalkOvershootLaw X μ a b).real (Ioi t) -
          (equilibriumOvershootLaw
            (gaussianAscendingLadderLaw X μ a)).real (Ioi t)| ≤ ε

/-- The reflection `o ↦ a - o` transports a bounded-Lipschitz comparison of
the overshoot laws to one of the reflected rewards.  This is the purely
algebraic half of the interface, separated so that the analytic half can be
supplied in either the tail or the bounded-Lipschitz form. -/
theorem gaussianWalkReflectedReward_sub_le_of_overshoot_close
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n))
    {a b : ℝ} {f : ℝ → ℝ} {K B η : ℝ} (hK : 0 ≤ K)
    (hclose : ∀ g : ℝ → ℝ, (∀ x y : ℝ, |g x - g y| ≤ K * |x - y|) →
      (∀ x, |g x| ≤ B) →
        |(∫ x, g x ∂(gaussianWalkOvershootLaw X μ a b)) -
          ∫ x, g x ∂(equilibriumOvershootLaw
            (gaussianAscendingLadderLaw X μ a))| ≤ η)
    (hfl : ∀ x y : ℝ, |f x - f y| ≤ K * |x - y|) (hfB : ∀ x, |f x| ≤ B) :
    |gaussianWalkReflectedReward X μ f a b -
      swingOvershootReward X μ f a| ≤ η := by
  let g : ℝ → ℝ := fun o => f (a - o)
  have hfLip : LipschitzWith ⟨K, hK⟩ f := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    change |f x - f y| ≤ K * |x - y|
    exact hfl x y
  have hfmeas : Measurable f := hfLip.continuous.measurable
  have hg : Measurable g :=
    Measurable.comp hfmeas (measurable_const.sub measurable_id)
  have hglip : ∀ x y : ℝ, |g x - g y| ≤ K * |x - y| := by
    intro x y
    dsimp [g]
    calc
      |f (a - x) - f (a - y)| ≤ K * |(a - x) - (a - y)| := hfl _ _
      _ = K * |x - y| := by
        congr 1
        rw [show (a - x) - (a - y) = -(x - y) by ring, abs_neg]
  have hgbdd : ∀ x, |g x| ≤ B := fun x => hfB _
  have hmain := hclose g hglip hgbdd
  have hfinite : gaussianWalkReflectedReward X μ f a b =
      ∫ o, g o ∂(gaussianWalkOvershootLaw X μ a b) := by
    unfold gaussianWalkReflectedReward gaussianWalkOvershootLaw
    exact (integral_map
      (gaussianWalkOvershoot_measurable hX a b).aemeasurable
      (show Measurable (fun o : ℝ => f (a - o)) from hg).aestronglyMeasurable).symm
  have hequil : swingOvershootReward X μ f a =
      ∫ o, g o ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)) := by
    unfold swingOvershootReward swingOvershootMeasure
    simpa [g] using (integral_map
      (φ := fun o : ℝ => a - o)
      (measurable_const.sub measurable_id).aemeasurable
      hfmeas.aestronglyMeasurable)
  rw [hfinite, hequil]
  exact hmain

/-- **The tail form suffices.**  A uniform tail limit for the overshoot law
gives the bounded-Lipschitz statement that Theorem 4.3 consumes.  The
truncation level is chosen from the already proved uniform second moment of
the ladder height, so the only analytic input left is
`UniformOvershootTailLimit`. -/
theorem uniformOvershootEquilibriumLimit_of_tail_limit
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (htail : UniformOvershootTailLimit X μ) :
    UniformOvershootEquilibriumLimit X μ := by
  have _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  intro δ M L B η hδ hM hL hB hη
  set B2 := gaussianAscendingLadderMomentBound δ M 2 with hB2def
  set cM := gaussianAscendingLadderCommonDensity M with hcMdef
  have hcM : 0 < cM := gaussianAscendingLadderCommonDensity_pos M
  set T : ℝ := max 1 (8 * B * |B2| / (cM * η)) with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  have hT : 0 < T := lt_of_lt_of_le one_pos hT1
  have hTtail : 4 * B * B2 / (cM * T) ≤ η / 2 := by
    have hTge : 8 * B * |B2| / (cM * η) ≤ T := le_max_right _ _
    have hkey : 8 * B * |B2| ≤ cM * η * T := by
      rw [div_le_iff₀ (by positivity)] at hTge
      linarith
    have habs : B2 ≤ |B2| := le_abs_self _
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg B2,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hB) (abs_nonneg B2)]
  set A : ℝ := 2 * B + 2 * L * T with hAdef
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA2B : 2 * B ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg hL hT.le]
  have hden : (0 : ℝ) < 4 * A + 4 := by linarith
  set ε : ℝ := η / (4 * A + 4) with hεdef
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεkey : A * ε + 2 * B * ε ≤ η / 2 := by
    have h1 : A * ε + 2 * B * ε ≤ 2 * A * ε := by nlinarith
    have h2 : 2 * A * ε ≤ η / 2 := by
      have heq : 2 * A * ε = 2 * A * η / (4 * A + 4) := by
        rw [hεdef]; ring
      rw [heq, div_le_iff₀ hden]
      nlinarith
    linarith
  obtain ⟨b₀, hb₀pos, hb₀⟩ := htail δ M ε hδ hM hε
  refine ⟨max b₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro a ha b hb f hfl hfB
  have hb1 : (1 : ℝ) ≤ b := le_trans (le_max_right _ _) hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  have hbb : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hδa : δ ≤ a := ha.1
  have haM : a ≤ M := ha.2
  have hapos : 0 < a := lt_of_lt_of_le hδ hδa
  have hPprob := gaussianWalkOvershootLaw_isProbabilityMeasure (μ := μ) hX a b
  have hQprob :=
    gaussianAscendingLadderEquilibrium_isProbabilityMeasure hX hi hG hδ hδa haM
  set P := gaussianWalkOvershootLaw X μ a b with hPdef
  set Q := equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a) with hQdef
  have hPIio : P (Iio 0) = 0 :=
    gaussianWalkOvershootLaw_Iio_zero hX hi hG hapos haM hbpos.le
  have hQIio : Q (Iio 0) = 0 := equilibriumOvershootLaw_Iio_zero _
  have htailclose : ∀ t : ℝ, 0 ≤ t →
      |P.real (Ioi t) - Q.real (Ioi t)| ≤ ε := fun t ht => hb₀ a ha b hbb t ht
  have hQtail : Q.real (Ioi T) ≤ B2 / (cM * T) :=
    equilibriumOvershoot_tail_le hX hi hG hδ hδa haM hT
  have hPtail : P.real (Ioi T) ≤ Q.real (Ioi T) + ε := by
    have hdiff := htailclose T hT.le
    have h1 : P.real (Ioi T) - Q.real (Ioi T) ≤ ε := (le_abs_self _).trans hdiff
    linarith
  have hQ0 : 0 ≤ Q.real (Ioi T) := measureReal_nonneg
  have hQsmall : 4 * B * Q.real (Ioi T) ≤ η / 2 := by
    have hstep : 4 * B * Q.real (Ioi T) ≤ 4 * B * (B2 / (cM * T)) :=
      mul_le_mul_of_nonneg_left hQtail (by linarith)
    calc
      4 * B * Q.real (Ioi T) ≤ 4 * B * (B2 / (cM * T)) := hstep
      _ = 4 * B * B2 / (cM * T) := by ring
      _ ≤ η / 2 := hTtail
  have hclose : ∀ g : ℝ → ℝ, (∀ x y : ℝ, |g x - g y| ≤ L * |x - y|) →
      (∀ x, |g x| ≤ B) → |(∫ x, g x ∂P) - ∫ x, g x ∂Q| ≤ η := by
    intro g hglip hgB
    have hmain := integral_lipschitz_sub_le_of_tail_close hPIio hQIio
      htailclose hL hglip hgB hT.le
    refine hmain.trans ?_
    have hfar : 2 * B * (P.real (Ioi T) + Q.real (Ioi T)) ≤
        4 * B * Q.real (Ioi T) + 2 * B * ε := by
      have hsum : P.real (Ioi T) + Q.real (Ioi T) ≤
          2 * Q.real (Ioi T) + ε := by linarith
      nlinarith
    dsimp [A] at hεkey
    linarith
  exact gaussianWalkReflectedReward_sub_le_of_overshoot_close hX hL hclose hfl hfB

/-- The Blanchet--Glynn provider implies the consumed statement.  Hence
weakening the standing hypothesis to
`UniformOvershootEquilibriumLimit` loses nothing. -/
theorem uniformOvershootEquilibriumLimit_of_uniform_renewal
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hrenew : ∀ {δ M : ℝ}, 0 < δ → 0 ≤ M →
      ∃ Cexp c : ℝ,
        UniformLadderRenewalExpansion
          (gaussianAscendingLadderLaw X μ) (Icc δ M) Cexp c) :
    UniformOvershootEquilibriumLimit X μ := by
  intro δ M L B η hδ hM hL hB hη
  obtain ⟨Cexp, cexp, hexp⟩ := hrenew hδ hM
  exact gaussianWalkReflectedReward_lipschitz_uniform_pos
    (X := X) (μ := μ) hX hi hG hδ hexp.1 hexp hL hB hη

/-- The Blanchet--Glynn provider also gives the scalar tail form, so the two
providers sit in a chain `renewal expansion ⟹ tail limit ⟹ bounded-Lipschitz
limit` and no route is lost by targeting the weakest one. -/
theorem uniformOvershootTailLimit_of_uniform_renewal
    {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hrenew : ∀ {δ M : ℝ}, 0 < δ → 0 ≤ M →
      ∃ Cexp c : ℝ,
        UniformLadderRenewalExpansion
          (gaussianAscendingLadderLaw X μ) (Icc δ M) Cexp c) :
    UniformOvershootTailLimit X μ := by
  have _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  intro δ M ε hδ hM hε
  obtain ⟨C, c, hexp⟩ := hrenew hδ hM
  have hc : 0 < c := hexp.1
  have hlim := gaussianResidualLifeBound_tendsto (δ := δ) (M := M) (C := C) (c := c) hc
  have hsmall : ∀ᶠ b : ℝ in atTop,
      gaussianResidualLifeBound δ M C c b < ε := hlim.eventually_lt_const hε
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp hsmall
  refine ⟨max b₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro a ha b hb t ht
  have hb1 : (1 : ℝ) ≤ b := le_trans (le_max_right _ _) hb
  have hbpos : 0 < b := lt_of_lt_of_le one_pos hb1
  have hbb : b₀ ≤ b := le_trans (le_max_left _ _) hb
  have hδa : δ ≤ a := ha.1
  have haM : a ≤ M := ha.2
  have hapos : 0 < a := lt_of_lt_of_le hδ hδa
  have hP : (gaussianWalkOvershootLaw X μ a b).real (Ioi t) =
      (renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b t).toReal := by
    rw [Measure.real, gaussianWalkOvershootLaw_Ioi hX hi hG hapos haM hbpos.le ht]
  have hQ : (equilibriumOvershootLaw
      (gaussianAscendingLadderLaw X μ a)).real (Ioi t) =
      (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ a) t).toReal := by
    rw [Measure.real, equilibriumOvershootLaw_Ioi _
      (gaussianAscendingLadderLaw_mean_ne_zero hX hG hapos haM) ht]
  rw [hP, hQ]
  exact le_of_le_of_eq
    ((gaussianAscendingLadder_residual_life_uniform_le hX hi hG hδ hexp hδa haM
      ht hbpos).trans (hb₀ b hbb).le) rfl

end SwingRepair
