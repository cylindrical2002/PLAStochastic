import PLAStochastic.Swing.StationaryLimit.LowerBridge.DeterministicInterface

/-!
# A probability certificate for the random lower bridge

The native kernel theorem needs a small amount of probability input in
addition to the pathwise bridge.  This file separates that input into three
events: early-slope localization, a finite prefix Gaussian envelope, and the
remaining passage/least-squares conditions.  The resulting estimate is a
literal three-term bad-mass bound; no asymptotic statement is hidden here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The part of the lower-bridge event left after the early localization and
the fixed prefix envelope have been supplied.  The index `k` is still
random, while all remaining checks are stated explicitly. -/
def randomBridgeWindowCore
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (η Q : ℝ) : Set Ω :=
  {ω | ∃ k : ℕ,
      1 ≤ J - 1 + k ∧
      (∀ i ∈ Finset.Icc 1 (J - 1 + k),
        |cumulativeSamples X (i-1) ω| ≤ Q + η * (i : ℝ)) ∧
      3 * (E-r+Q) / (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + η ≤
        prefixCrossingSlope X r J ω ∧
      0 < prefixCrossingSlope X r J ω ∧
      0 < prefixCrossingLevel X E r J ω ∧
      prefixCrossingSlope X r J ω ≤ E ∧
      (∃ m : ℕ,
        prefixCrossingLevel X E r J ω <
          gaussianDriftWalk
            (negIncrements (fun q => X (J - 1 + q))) 0
            (prefixCrossingSlope X r J ω) m ω) ∧
      gaussianWalkPassage
        (negIncrements (fun q => X (J - 1 + q)))
        (prefixCrossingSlope X r J ω)
        (prefixCrossingLevel X E r J ω) ω = k}

/-- Explicit data needed to turn a localization event into a lower-bridge
probability estimate.  The two real numbers `α` and `γ` are supplied by the
eventual localization and passage arguments respectively. -/
structure RandomBridgeLocalizationCertificate
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    (K δ Q M η α γ : ℝ) : Prop where
  hJ : 1 ≤ J
  hδ : 0 < δ
  hE : 0 ≤ E
  hr : |r| ≤ K
  hK : 0 ≤ K
  hQ : 0 ≤ Q
  hM : 0 ≤ M
  hη : 0 ≤ η
  hbudget : M * (J : ℝ) ≤ 2*E - K - Q
  hα : 0 ≤ α
  hγ : 0 ≤ γ
  hlocal : μ.real (swingEarlySlopeGood X K δ M (J-1))ᶜ ≤ α
  hcore : μ.real (randomBridgeWindowCore (X := X) E r J η Q)ᶜ ≤ γ

omit [MeasurableSpace Ω] in
theorem randomBridgeLocalizationCertificate_intersection_subset_envelope
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ Q M η : ℝ}
    :
    swingEarlySlopeGood X K δ M (J-1) ∩
        finiteCumulativeEnvelope X J Q ∩
        randomBridgeWindowCore (X := X) E r J η Q ⊆
      prefixCrossingLowerBridgeEnvelopeEvent (X := X) E r J K δ Q M η := by
  intro ω hω
  rcases hω with ⟨⟨hgood, hprefix⟩, hcore⟩
  change ω ∈ swingEarlySlopeGood X K δ M (J - 1) ∧
      (∀ i ∈ Finset.Icc 1 (J - 1),
        |cumulativeSamples X (i - 1) ω| ≤ Q) ∧
      ω ∈ randomBridgeWindowCore (X := X) E r J η Q
  refine ⟨hgood, finiteCumulativeEnvelope_controls_prefix hprefix, hcore⟩

theorem randomBridgeLocalizationCertificate_bad_mass_le
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ Q M η α γ : ℝ}
    (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (hcert : RandomBridgeLocalizationCertificate (X := X) (μ := μ) E r J K δ Q M η α γ) :
    μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤
      α + 2 * (J : ℝ) * Real.exp (-Q^2/(2*(J : ℝ))) + γ := by
  have hbridge_env := prefixCrossingLowerBridgeEventRandom_compl_measure_le_envelope_compl
    (X := X) (μ := μ) E r J hcert.hJ hcert.hδ hcert.hE hcert.hr hcert.hK hcert.hQ
      hcert.hM hcert.hη hcert.hbudget
  have hinter :
      μ.real (prefixCrossingLowerBridgeEnvelopeEvent (X := X) E r J K δ Q M η)ᶜ ≤
        μ.real (swingEarlySlopeGood X K δ M (J-1))ᶜ +
          μ.real (finiteCumulativeEnvelope X J Q)ᶜ +
          μ.real (randomBridgeWindowCore (X := X) E r J η Q)ᶜ := by
    let A := swingEarlySlopeGood X K δ M (J-1)
    let B := finiteCumulativeEnvelope X J Q
    let C := randomBridgeWindowCore (X := X) E r J η Q
    let D := prefixCrossingLowerBridgeEnvelopeEvent (X := X) E r J K δ Q M η
    have hsub : A ∩ B ∩ C ⊆ D := by
      simpa [A, B, C, D] using
        (randomBridgeLocalizationCertificate_intersection_subset_envelope E r J)
    have hc : Dᶜ ⊆ (A ∩ B ∩ C)ᶜ := Set.compl_subset_compl.mpr hsub
    calc
      μ.real Dᶜ ≤ μ.real (A ∩ B ∩ C)ᶜ :=
        measureReal_mono hc (measure_ne_top μ _)
      _ ≤ μ.real (Aᶜ ∪ Bᶜ ∪ Cᶜ) := by
        exact measureReal_mono (by
          intro ω hω
          simp only [mem_compl_iff, mem_inter_iff, mem_union, not_and_or] at hω ⊢
          tauto) (measure_ne_top μ _)
      _ ≤ μ.real Aᶜ + μ.real Bᶜ + μ.real Cᶜ := by
        calc
          μ.real (Aᶜ ∪ Bᶜ ∪ Cᶜ) ≤ μ.real (Aᶜ ∪ Bᶜ) + μ.real Cᶜ :=
            measureReal_union_le _ _
          _ ≤ (μ.real Aᶜ + μ.real Bᶜ) + μ.real Cᶜ := by
            gcongr
            exact measureReal_union_le _ _
          _ = μ.real Aᶜ + μ.real Bᶜ + μ.real Cᶜ := by ring
  calc
    μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤
        μ.real (prefixCrossingLowerBridgeEnvelopeEvent (X := X) E r J K δ Q M η)ᶜ :=
      hbridge_env
    _ ≤ μ.real (swingEarlySlopeGood X K δ M (J-1))ᶜ +
          μ.real (finiteCumulativeEnvelope X J Q)ᶜ +
          μ.real (randomBridgeWindowCore (X := X) E r J η Q)ᶜ := hinter
    _ ≤ α + 2 * (J : ℝ) * Real.exp (-Q^2/(2*(J : ℝ))) + γ := by
      have hJpos : 0 < J := lt_of_lt_of_le Nat.zero_lt_one hcert.hJ
      have hprefix := finiteCumulativeEnvelope_compl_bound
        (μ := μ) (X := X) hX hi hG hJpos hcert.hQ
      linarith [hcert.hlocal, hcert.hcore, hprefix]

/-! A filter-level packaging of the certificate.  This is the exact shape
needed for a compact-uniform input: the indices and error split are fixed
after `(C, ε)` is chosen, while the certificate itself may depend on the
budget index and the incoming margin. -/

def randomBridgeLocalizationFamily
    {X : ℕ → Ω → ℝ} {ι : Type*} (l : Filter ι)
    (budget : ι → ℝ) (C ε : ℝ) : Prop :=
  ∃ (J : ℕ) (δ Q M η α γ : ℝ),
    0 < ε ∧ 1 ≤ J ∧ 0 < δ ∧ 0 ≤ Q ∧ 0 ≤ M ∧ 0 ≤ η ∧
      0 ≤ α ∧ 0 ≤ γ ∧
      α + 2 * (J : ℝ) * Real.exp (-Q^2/(2*(J : ℝ))) + γ ≤ ε ∧
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        ∃ E : ℝ,
          E = budget i ∧
          RandomBridgeLocalizationCertificate (X := X) (μ := μ)
            E r J C δ Q M η α γ

theorem randomBridgeLocalizationFamily_bad_mass_le
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {budget : ι → ℝ} {C ε : ℝ}
    (hfamily : randomBridgeLocalizationFamily (X := X) (μ := μ) l budget C ε) :
    ∃ J : ℕ, ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
      μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ ε := by
  rcases hfamily with ⟨J, δ, Q, M, η, α, γ, hε, hJ, hδ, hQ, hM, hη,
    hα, hγ, hsplit, hevent⟩
  refine ⟨J, ?_⟩
  filter_upwards [hevent] with i hi_event
  intro r hr
  obtain ⟨E, hEeq, hcert⟩ := hi_event r hr
  subst E
  have hbad := randomBridgeLocalizationCertificate_bad_mass_le
    (μ := μ) (X := X) (budget i) r J hX hi hG hcert
  exact hbad.trans hsplit

end SwingRepair
