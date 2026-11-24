import PLAStochastic.Swing.Restart.Chain.PathwiseBounds
import PLAStochastic.Swing.Restart.Chain.FreshWalkEnvelope
import PLAStochastic.Swing.FirstSegment.MarginMoments
import PLAStochastic.ForMathlib.Probability.Moments.IntegerGridExpTail

/-! # Arithmetic interfaces for the stationary-margin absorption step

These lemmas isolate the deterministic geometry and the final absorption
inequality used in Appendix `app:margins`.  They are deliberately stated
without probability hypotheses so that the probabilistic estimates can be
plugged in independently.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The numerical comparison used on a favorable branch: once the accepted
prefix is long enough, the unconstrained least-squares slope lies below the
old lower-cone endpoint. -/
theorem stationary_favorable_ls_lt_lower
    {E N a : ℝ} (_hE : 0 ≤ E) (hN : 39 ≤ N)
    (ha : (2-(1/20 : ℝ))*E/(N+1) < a) :
    3*(1+(1/20 : ℝ))*E/(2*N+1) < a := by
  have hNp : 0 < N + 1 := by linarith
  have hN2p : 0 < 2*N + 1 := by linarith
  have hcoef : 3*(1+(1/20 : ℝ))*E/(2*N+1) ≤
      (2-(1/20 : ℝ))*E/(N+1) := by
    apply (div_le_div_iff₀ hN2p hNp).2
    nlinarith
  exact hcoef.trans_lt ha

/-- The favorable branch records the small nonnegative old slope. -/
theorem stationary_favorable_old_slope_bounds
    {E a : ℝ} (_hE : 0 ≤ E) (ha0 : 0 < a) (haδ : a ≤ (1/20 : ℝ)*E) :
    0 < a ∧ a ≤ (1/20 : ℝ)*E := ⟨ha0, haδ⟩

/-- A positive margin is absorbed by the selected old slope and a negative
margin by the selected increment; this is the abstract form of the two
pathwise controls in the stationary proof. -/
theorem stationary_margin_absorption_controls
    {E x m z : ℝ} (hrej : E < |z-m|) (_hres : |x| ≤ E) :
    max (E-|z|) 0 ≤ |m| := by
  apply max_le _ (abs_nonneg _)
  have htri : |z-m| ≤ |z| + |m| := abs_sub z m
  linarith

/-- Geometry of a favorable lower rejection.  Writing the last accepted
residual as `-E+g`, with `g≥0`, the threshold `ζ<m-g` forces the new state to
the negative half-line and identifies its negative margin exactly. -/
theorem stationary_favorable_lower_geometry
    {E m g ζ : ℝ} (_hE : 0 ≤ E) (_hm0 : 0 ≤ m) (hmE : m ≤ E)
    (_hg : 0 ≤ g) (hζ : ζ < m-g) :
    -E+g+ζ ≤ 0 ∧
      |(-E+g+ζ)| = E-g-ζ ∧
      max (|(-E+g+ζ)|-E) 0 = max (-g-ζ) 0 := by
  have hx : -E+g+ζ ≤ 0 := by linarith
  have habs : |(-E+g+ζ)| = E-g-ζ := by
    rw [abs_of_nonpos hx]
    ring
  refine ⟨hx, habs, ?_⟩
  rw [habs]
  congr 1
  ring

/-- Solve the one-line stationary absorption inequality. -/
theorem stationary_absorb
    {C A b : ℝ} (_hC : 0 ≤ C) (_hA : 0 ≤ A)
    (_hb : 0 ≤ b) (hblt : b < 1) (hineq : C ≤ A + b*C) :
    C ≤ A/(1-b) := by
  have hden : 0 < 1-b := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Convenient quantitative version: a coefficient at most one half costs a
factor two. -/
theorem stationary_absorb_half
    {C A b : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb : 0 ≤ b) (hbhalf : b ≤ (1/2 : ℝ))
    (hineq : C ≤ A + b*C) : C ≤ 2*A := by
  have h := stationary_absorb hC hA hb (lt_of_le_of_lt hbhalf (by norm_num)) hineq
  have hden : (1/2 : ℝ) ≤ 1-b := by linarith
  have hnonneg : 0 ≤ 1-b := by linarith
  calc
    C ≤ A/(1-b) := h
    _ ≤ A/(1/2 : ℝ) := by
      exact (div_le_div_of_nonneg_left hA (by norm_num) hden)
    _ = 2*A := by ring

/-- The coefficient in the stationary proof tends to zero whenever the
numerator grows polylogarithmically slower than the scale. -/
theorem stationary_absorption_coefficient_eventually_half
    {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ᶠ n in atTop, f n ≤ (1/2 : ℝ) := by
  have hnh : {x : ℝ | x < (1/2 : ℝ)} ∈ 𝓝 (0 : ℝ) :=
    Iio_mem_nhds (by norm_num)
  have hev := hf.eventually hnh
  filter_upwards [hev] with n hn
  exact hn.le

/-- The explicit absorption estimate appearing in (G.4): once the residual
coefficient is at most one half, the stationary mean is bounded by twice the
main `E log E` term. -/
theorem stationary_absorb_E_log
    {C K E : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hE : 1 ≤ E)
    (hcoef : K*(Real.log E)^(3/2)/E ≤ (1/2 : ℝ))
    (hineq : C ≤ K*E*Real.log E + (K*(Real.log E)^(3/2)/E)*C) :
    C ≤ 2*(K*E*Real.log E) := by
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
  have hA : 0 ≤ K*E*Real.log E := by positivity
  have hcoef0 : 0 ≤ K*(Real.log E)^(3/2)/E := by positivity
  exact stationary_absorb_half hC hA hcoef0 hcoef hineq

/-!  The following two lemmas are the measure-theoretic closing step used when
the stationary law `π_E` is inserted.  They keep the tail integration and the
absorption arithmetic separate, so that the estimates for the favourable and
unfavourable branches can be supplied independently. -/

/-- A nonnegative stationary observable with an exponential integer tail has
all polynomial moments bounded by the explicit tail series.  This is the
`π_E` version of the layer-cake estimate used in the proof of Theorem 4.2. -/
theorem stationary_pi_moment_of_exp_tail
    {S : Type*} [MeasurableSpace S] {π : Measure S} [IsProbabilityMeasure π]
    {M : S → ℝ} (hM : Measurable M) (hnonneg : 0 ≤ᵐ[π] M)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (htail : ∀ n : ℕ, π {s | (n : ℝ) ≤ M s} ≤
      ENNReal.ofReal (A * Real.exp (-c * (n : ℝ)))) (k : ℕ) :
    (∫ s, M s ^ k ∂π) ≤ A * expTailMomentSum c k := by
  exact integral_pow_le_of_expTail hM hnonneg hA hc htail k

/-- The same tail hypothesis gives Bochner integrability of every polynomial
power, which justifies exchanging the stationary `π_E` integral with the
branch decomposition. -/
theorem stationary_pi_integrable_pow_of_exp_tail
    {S : Type*} [MeasurableSpace S] {π : Measure S} [IsProbabilityMeasure π]
    {M : S → ℝ} (hM : Measurable M) (hnonneg : 0 ≤ᵐ[π] M)
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (htail : ∀ n : ℕ, π {s | (n : ℝ) ≤ M s} ≤
      ENNReal.ofReal (A * Real.exp (-c * (n : ℝ)))) (k : ℕ) :
    Integrable (fun s => M s ^ k) π := by
  exact integrable_pow_of_expTail hM hnonneg hA hc htail k

/-- Uniform form of the stationary absorption estimate.  Once the residual
coefficient is eventually at most one half, every stationary solution of the
one-step inequality is eventually bounded by twice its main `E log E` term. -/
theorem stationary_absorb_E_log_eventually
    {C K : ℝ → ℝ}
    (hC : ∀ᶠ E : ℝ in atTop, 0 ≤ C E)
    (hK : ∀ᶠ E : ℝ in atTop, 0 ≤ K E)
    (hE : ∀ᶠ E : ℝ in atTop, 1 ≤ E)
    (hcoef : ∀ᶠ E : ℝ in atTop,
      K E * (Real.log (E))^(3/2) / E ≤ (1/2 : ℝ))
    (hineq : ∀ᶠ E : ℝ in atTop,
      C E ≤ K E * E * Real.log E +
        (K E * (Real.log E)^(3/2) / E) * C E) :
    ∀ᶠ E : ℝ in atTop, C E ≤ 2 * (K E * E * Real.log E) := by
  filter_upwards [hC, hK, hE, hcoef, hineq] with E hCE hKE hE1 hbe hineqE
  exact stationary_absorb_E_log hCE hKE hE1 hbe hineqE

/-! ### Pathwise restart margin control

The following is the exact deterministic decomposition used in the
stationary proof.  It combines the positive and negative margin controls for
one finite restart, and is useful when the transition kernel is integrated
against an invariant law.
-/

theorem nativeRestart_margin_abs_le_slope_add_increment
    {Ω : Type*} (X : ℕ → Ω → ℝ) {E : ℝ} (hE : 0 ≤ E)
    (x : ℝ) (ω : Ω)
    (hf : nativeRestartLength X E x ω ≠ ⊤) :
    |(E - |nativeRestartNext X E x ω|)| ≤
      |nativeRestartSlope X E x ω| +
        |X (nativeRestartLengthNat X E x ω - 1) ω| := by
  have hpos := nativeRestart_margin_pos_le_slope X hE x ω hf
  have hneg := nativeRestart_margin_neg_le_increment X hE x ω hf
  rcases le_or_gt E |nativeRestartNext X E x ω| with hle | hgt
  · have hnon : 0 ≤ |nativeRestartNext X E x ω| - E := sub_nonneg.mpr hle
    have hneg' : |nativeRestartNext X E x ω| - E ≤
        |X (nativeRestartLengthNat X E x ω - 1) ω| := by
      simpa [max_eq_left hnon] using hneg
    rw [abs_of_nonpos (by linarith)]
    have hsum : |nativeRestartNext X E x ω| - E ≤
        |nativeRestartSlope X E x ω| +
          |X (nativeRestartLengthNat X E x ω - 1) ω| :=
      hneg'.trans (le_add_of_nonneg_left (abs_nonneg _))
    simpa [neg_sub] using hsum
  · have hnon : 0 ≤ E - |nativeRestartNext X E x ω| := sub_nonneg.mpr hgt.le
    have hpos' : E - |nativeRestartNext X E x ω| ≤
        |nativeRestartSlope X E x ω| := by
      simpa [max_eq_left hnon] using hpos
    rw [abs_of_nonneg (by linarith)]
    exact hpos'.trans (le_add_of_nonneg_right (abs_nonneg _))

/-! Replace the abstract slope term by the genuine Gaussian partial-sum
envelope.  This is the pathwise estimate used in the stationary margin
argument. -/
theorem nativeRestart_margin_abs_le_envelope_add_increment
    {X : ℕ → Ω → ℝ} {E : ℝ} (hE : 0 ≤ E) (x : ℝ) (ω : Ω)
    (hW : ∀ n, |cumulativeSamples X n ω| ≤
      nativeGaussianEnvelope X ω * ((n : ℝ) + 1))
    (hB : 0 < nativeRestartExcess E x + 2 * nativeGaussianEnvelope X ω)
    (hf : nativeRestartLength X E x ω ≠ ⊤) :
    |(E - |nativeRestartNext X E x ω|)| ≤
      5 * nativeRestartExcess E x + 10 * nativeGaussianEnvelope X ω +
        |X (nativeRestartLengthNat X E x ω - 1) ω| := by
  have hG : 0 ≤ nativeGaussianEnvelope X ω := nativeGaussianEnvelope_nonneg X ω
  have hs := nativeRestart_slope_bound X hE hG ω hW hB hf
  have hm := nativeRestart_margin_abs_le_slope_add_increment X hE x ω hf
  exact hm.trans (by
    have hh := add_le_add_right hs (|X (nativeRestartLengthNat X E x ω - 1) ω|)
    simpa [add_assoc, add_comm, add_left_comm] using hh)

end SwingRepair
