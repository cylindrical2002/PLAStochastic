import PLAStochastic.Swing.Algorithm.Cone
import PLAStochastic.Swing.FirstSegment.Recording
import PLAStochastic.Swing.FirstSegment.MarginMoments
import PLAStochastic.Swing.SecondSegment.SlopeDecay
import PLAStochastic.Swing.Ladder.Renewal.EquilibriumOvershoot
import PLAStochastic.Swing.Ladder.Law.AscendingLaw
import PLAStochastic.Affine.Pinch.SlopeCone
import PLAStochastic.Affine.Error.Measurable
import PLAStochastic.Brownian.Construction.ContinuousVersion

/-!
# Objects of the first-restart entrance law

Definitions shared by the proof that the first-restart margin of the native Swing filter
converges in law. The notation follows the entrance-law derivation:

* the running cone endpoints `a_n = max_{1≤i≤n} (y_i - E)/i` and
  `b_n = min_{1≤i≤n} (y_i + E)/i` of the anchored sample path, kept after the cone empties;
* the rescaled width `n (b_n - a_n)`, the adaptive cut `τ = inf {n ≥ 1 : n(b_n - a_n) ≤ E^{1/4}}`,
  the refreshed side, the frozen endpoint and the reflected local residual process after the
  cut, with its crossing time, overshoot and undershoot;
* the native quantities at the first rejection used in the final statement;
* the Brownian first pinch `σ`, its slope `m_*`, terminal sign `s`, signed area `I` and the
  selection probability `θ = P(I > 0)` under the canonical Brownian motion;
* the zero-drift equilibrium age/residual pair and the entrance law
  `ρ = θ Law(-O) + (1 - θ) Law(-(U + O))`.
-/

open MeasureTheory ProbabilityTheory Set BrownianAffine
open scoped ENNReal NNReal

namespace SwingRepair

noncomputable section

/-! ## The running cone of the anchored path -/

/-- `a_n = max_{1 ≤ i ≤ n} (y_i - y_0 - E)/i`, defined for every `n ≥ 1`; `0` at `n = 0`. -/
def entranceLower (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℝ :=
  if h : (Finset.Icc 1 n).Nonempty then
    nativeConeLower (Finset.Icc 1 n) h (fun j => (j : ℝ)) y 0 (y 0) E
  else 0

/-- `b_n = min_{1 ≤ i ≤ n} (y_i - y_0 + E)/i`, defined for every `n ≥ 1`; `0` at `n = 0`. -/
def entranceUpper (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℝ :=
  if h : (Finset.Icc 1 n).Nonempty then
    nativeConeUpper (Finset.Icc 1 n) h (fun j => (j : ℝ)) y 0 (y 0) E
  else 0

/-- The rescaled cone width `n (b_n - a_n)`. -/
def entranceWidth (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (entranceUpper y E n - entranceLower y E n)

/-- The cut level `d_E = E^{1/4}`. -/
def entranceCutLevel (E : ℝ) : ℝ := E ^ (1 / 4 : ℝ)

/-- The window length `q_E = ⌊E^{3/4}⌋`. -/
def entranceWindow (E : ℝ) : ℕ := ⌊E ^ (3 / 4 : ℝ)⌋₊

/-- The adaptive cut `τ = inf {n ≥ 1 : n (b_n - a_n) ≤ d_E}`, `⊤` if it never happens. -/
def entranceCut (y : ℕ → ℝ) (E : ℝ) : ℕ∞ := by
  classical
  exact if h : ∃ n : ℕ, 1 ≤ n ∧ entranceWidth y E n ≤ entranceCutLevel E then (Nat.find h : ℕ∞)
    else ⊤

/-- At index `n` the lower endpoint is attained by the current sample. -/
def entranceRefreshesLower (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : Prop :=
  entranceLower y E n = slopeLower (n : ℝ) (y n) 0 (y 0) E

/-- The side `s_E = 1` when the lower endpoint is refreshed (upper endpoint frozen), else `-1`. -/
def entranceSide (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if entranceRefreshesLower y E n then 1 else -1

/-- The frozen endpoint `β` at index `n`, in the original coordinates. -/
def entranceFrozenSlope (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if entranceRefreshesLower y E n then entranceUpper y E n else entranceLower y E n

theorem entranceSide_eq_one_or {y : ℕ → ℝ} {E : ℝ} (n : ℕ) :
    entranceSide y E n = 1 ∨ entranceSide y E n = -1 := by
  classical
  unfold entranceSide
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The reflected local residual `Q_j = s (y_{n+j} - y_n) - s β j` after index `n`. -/
def entranceLocal (y : ℕ → ℝ) (E : ℝ) (n j : ℕ) : ℝ :=
  entranceSide y E n * (y (n + j) - y n) - entranceSide y E n * entranceFrozenSlope y E n * j

/-- The crossing time `T_D = inf {j ≥ 1 : Q_j > D}` of the cut width `D = n (b_n - a_n)`. -/
def entranceCrossing (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℕ∞ := by
  classical
  exact if h : ∃ j : ℕ, 1 ≤ j ∧ entranceWidth y E n < entranceLocal y E n j then
    (Nat.find h : ℕ∞) else ⊤

/-- The local overshoot `O = Q_T - D` (`0` if there is no crossing). -/
def entranceOvershoot (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℝ :=
  match entranceCrossing y E n with
  | ⊤ => 0
  | (T : ℕ) => entranceLocal y E n T - entranceWidth y E n

/-- The local undershoot `U = D - max_{0 ≤ j < T} Q_j` (`0` if there is no crossing). -/
def entranceUndershoot (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℝ :=
  match entranceCrossing y E n with
  | ⊤ => 0
  | (T : ℕ) =>
    if hT : 0 < T then
      entranceWidth y E n - (Finset.range T).sup' (Finset.nonempty_range_iff.mpr hT.ne')
        (entranceLocal y E n)
    else 0

/-- The reflected rescaled area `E^{-5} ∑_{i=1}^{n} i (s y_i - s β i)` at the cut. -/
def entranceGridArea (y : ℕ → ℝ) (E : ℝ) (n : ℕ) : ℝ :=
  E⁻¹ ^ 5 * ∑ i ∈ Finset.Icc 1 n,
    (i : ℝ) * (entranceSide y E n * y i - entranceSide y E n * entranceFrozenSlope y E n * i)

/-- The truncation event of the cut, measurable at the cut: `δ E² ≤ τ ≤ M E²`,
`|E β| ≤ M` and `d_E / 2 ≤ D ≤ d_E` with `D = τ (b_τ - a_τ)`. -/
def entranceGood (y : ℕ → ℝ) (E δ M : ℝ) : Prop :=
  ∃ n : ℕ, entranceCut y E = n ∧ δ * E ^ 2 ≤ n ∧ (n : ℝ) ≤ M * E ^ 2 ∧
    |E * entranceFrozenSlope y E n| ≤ M ∧
    entranceCutLevel E / 2 ≤ entranceWidth y E n ∧ entranceWidth y E n ≤ entranceCutLevel E

/-! ## Native quantities at the first rejection -/

variable {Ω : Type*}

/-- The anchored sample path `y_n = X_0 + ⋯ + X_{n-1}`. -/
def entrancePath (X : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ := fun n => cumulativeSamples X n ω

@[simp] theorem entrancePath_zero (X : ℕ → Ω → ℝ) (ω : Ω) : entrancePath X ω 0 = 0 :=
  cumulativeSamples_zero X ω

/-- The rejection direction: `1` if the first rejected sample lies above the cone, else `-1`. -/
def entranceRejectSide (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ := by
  classical
  exact
    let y := entrancePath X ω
    let N := nativeFirstDuration X E ω
    if entranceUpper y E N * (N + 1 : ℕ) + E < y (N + 1) then 1 else -1

/-- The frozen endpoint at the first rejection: `b_N` for an upper rejection, else `a_N`. -/
def entranceRejectFrozen (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  let y := entrancePath X ω
  let N := nativeFirstDuration X E ω
  if entranceRejectSide X E ω = 1 then entranceUpper y E N else entranceLower y E N

/-- `O♮ = s (y_J - β♮ J) - E` with `J = N + 1`. -/
def entranceRejectOvershoot (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  let N := nativeFirstDuration X E ω
  entranceRejectSide X E ω *
      (entrancePath X ω (N + 1) - entranceRejectFrozen X E ω * (N + 1 : ℕ)) - E

/-- `U♮ = N (b_N - a_N)`. -/
def entranceRejectWidth (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : ℝ :=
  entranceWidth (entrancePath X ω) E (nativeFirstDuration X E ω)

/-- `χ♮`: the native SSE selects the frozen endpoint. -/
def entranceSelectsFrozen (X : ℕ → Ω → ℝ) (E : ℝ) (ω : Ω) : Prop :=
  nativeFirstSelectedSlope X E ω = entranceRejectFrozen X E ω

/-! ## The Brownian macroscopic selection -/

/-- The first continuous cone pinch `σ` of the anchored path with tolerance `1`. -/
def entrancePinch (f : C(ℝ, ℝ)) : ℝ := (firstContinuousConePinch f 0 1).toReal

/-- The unique feasible slope `m_*` at the pinch. -/
def entranceSlope (f : C(ℝ, ℝ)) : ℝ := continuousLowerSlope f 0 1 (entrancePinch f)

/-- The terminal data-residual sign `s = f(σ) - m_* σ`, which is `±1` almost surely. -/
def entranceSign (f : C(ℝ, ℝ)) : ℝ := f (entrancePinch f) - entranceSlope f * entrancePinch f

/-- The signed area `I = s ∫_0^σ t (f t - m_* t) dt`. -/
def entranceArea (f : C(ℝ, ℝ)) : ℝ :=
  entranceSign f * ∫ t in (0 : ℝ)..entrancePinch f, t * (f t - entranceSlope f * t)

/-- The selection probability `θ = P(I > 0)` under the canonical Brownian motion. -/
def entranceSelectionProb : ℝ :=
  canonicalPreBrownianMeasure.real
    {ω | 0 < entranceArea (processPath canonicalBrownian ω)}

/-! ## The equilibrium pair and the entrance law -/

/-- The size-biased law `h ν(dh) / E h` of a nonnegative law `ν`. -/
def sizeBiasedLaw (ν : Measure ℝ) : Measure ℝ :=
  ν.withDensity (fun h => ENNReal.ofReal h / ladderMeanENN ν)

/-- The equilibrium age/residual pair: `((1 - V) H, V H)` with `H` size-biased and `V`
uniform on `[0,1]` independent. -/
def equilibriumPairLaw (ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  ((sizeBiasedLaw ν).prod (volume.restrict (Icc (0 : ℝ) 1))).map
    (fun p => ((1 - p.2) * p.1, p.2 * p.1))

variable [MeasurableSpace Ω]

/-- The entrance law `ρ = θ Law(-O) + (1 - θ) Law(-(U + O))` of the zero-drift ascending
ladder height law. -/
def entranceLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Measure ℝ :=
  ENNReal.ofReal entranceSelectionProb •
      (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0)).map (fun o => -o) +
    ENNReal.ofReal (1 - entranceSelectionProb) •
      (sizeBiasedLaw (gaussianAscendingLadderLaw X μ 0)).map (fun h => -h)

end

end SwingRepair
