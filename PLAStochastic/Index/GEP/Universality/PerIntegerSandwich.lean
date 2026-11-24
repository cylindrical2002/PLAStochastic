import PLAStochastic.Index.GEP.Universality.StrongApproxInterface
import PLAStochastic.Index.GEP.Universality.DeterministicEnvelope
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers

/-!
# WP5, D3: the per-integer sandwich

Blueprint `kmt-blueprint/main.tex` Proposition 8.5 (`prop:perk`), in an abstract form: given an
(SA) coupling `π` at horizon `n` with error `a` and failure `pSA`, the two maximal bounds on the
centred input walk (`B₁`: deviation `k/9`, `B₂`: deviation `xB`) with failures `p₁, p₂`, and
the Brownian side `LifetimeSide 𝒯`, the probability `P(T > k)` is sandwiched between the scaled
lifetime tails at `(ε ± …)²/v`, up to the failure probabilities.  With
`x_D = 8 xB²/k`, `x_Γ = 2√v ρ` and `χ = a + x_D + x_Γ`:

* `perInteger_upper`: `P(T > k) ≤ s̄(v k/(ε + χ)²) + pSA + p₁ + p₂ + 2 n e^{-ρ²/2}`;
* `perInteger_lower`: `s̄(v k/(ε - 2χ)²) - 2 n e^{-ρ²/2} - pSA - p₁ - p₂ ≤ P(T > k)` if `2χ < ε`.

The deterministic step is `GEPSAEnvelope`; `T > k` is `lt_segLen_iff`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-! ## Events on the coupling space -/

/-- The centred input walk `s_t = S_t - t` deviates by more than `x` before `k`. -/
def walkBad (x : ℝ) (k : ℕ) : Set (ℕ → ℝ) := {g | ∃ t ≤ k, x < |gapKeys g t - t|}

theorem measurableSet_walkBad (x : ℝ) (k : ℕ) : MeasurableSet (walkBad x k) := by
  have : walkBad x k = ⋃ t, ⋃ (_ : t ≤ k), {g : ℕ → ℝ | x < |gapKeys g t - t|} := by
    ext g; simp [walkBad]
  rw [this]
  exact MeasurableSet.iUnion fun t => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const ((measurable_gapKeys_apply t).sub_const _).abs

theorem measurableSet_lt_gapSegLen (eps : ℝ) (k : ℕ) :
    MeasurableSet {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} := by
  have h := (gapFiltration gapCoord (fun t => measurable_pi_apply t)).le k _
    (gapSegLen_lt_measurable (X := gapCoord) (fun t => measurable_pi_apply t) eps k)
  exact h

/-- `T > k` iff some `(a, b)` fits the keys `0, …, k` within `ε`. -/
theorem lt_gapSegLen_iff_fit (eps : ℝ) (g : ℕ → ℝ) (k : ℕ) :
    (k : ℕ∞) < gapSegLen eps g ↔
      ∃ a b : ℝ, ∀ t ≤ k, |(t : ℝ) - (a * (t + (gapKeys g t - t)) + b)| ≤ eps := by
  rw [gapSegLen, lt_segLen_iff]
  unfold prefixAffineFeasible
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, fun t ht => by simpa using h t (Nat.lt_succ_of_le ht)⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, fun t ht => by simpa using h t (Nat.lt_succ_iff.1 ht)⟩

/-- The oscillation bound of a walk with `|s_t| ≤ M` on `{0, …, k}`. -/
theorem osc_le_of_abs_le {s : ℕ → ℝ} {k : ℕ} {M : ℝ} (h : ∀ t ≤ k, |s t| ≤ M) :
    ∀ t₁ ≤ k, ∀ t₂ ≤ k, |s t₁ - s t₂| ≤ 2 * M := fun t₁ h₁ t₂ h₂ =>
  (abs_sub _ _).trans (by linarith [h t₁ h₁, h t₂ h₂])

variable {ν : ProbabilityMeasure ℝ} {π : Measure ((ℕ → ℝ) × (ℕ → ℝ))}

/-- Transfer of a first-marginal event. -/
theorem real_fst_event (h1 : π.map Prod.fst = iidLaw ν) {A : Set (ℕ → ℝ)} (hA : MeasurableSet A) :
    (iidLaw ν).real A = π.real {q | q.1 ∈ A} := by
  rw [← h1, measureReal_def, Measure.map_apply measurable_fst hA]; rfl

/-- Transfer of a second-marginal event. -/
theorem real_snd_event (h2 : π.map Prod.snd = iidLaw gaussPM) {A : Set (ℕ → ℝ)}
    (hA : MeasurableSet A) : (iidLaw gaussPM).real A = π.real {q | q.2 ∈ A} := by
  rw [← h2, measureReal_def, Measure.map_apply measurable_snd hA]; rfl

variable [IsProbabilityMeasure π]

/-! ## The deterministic inclusions -/

/-- Off the bad events, `T > k` forces a small affine-fit error of the Gaussian walk. -/
theorem affErr_le_of_lt_gapSegLen {eps v a xB : ℝ} (hxB : 0 ≤ xB)
    {k : ℕ} (hk : 1 ≤ k) {q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hT : (k : ℕ∞) < gapSegLen eps q.1)
    (hSA : ∀ t ≤ k, |gapKeys q.1 t - t - Real.sqrt v * gapKeys q.2 t| ≤ a)
    (hB₁ : ∀ t ≤ k, |gapKeys q.1 t - t| ≤ k / 9)
    (hB₂ : ∀ t ≤ k, |gapKeys q.1 t - t| ≤ xB) :
    affErr v k q.2 ≤ eps + a + 8 * xB ^ 2 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨a', b', hfit⟩ := (lt_gapSegLen_iff_fit eps q.1 k).1 hT
  set s : ℕ → ℝ := fun t => gapKeys q.1 t - t with hs
  set D : ℝ := 2 * min xB ((k : ℝ) / 9) with hD
  have hD0 : 0 ≤ D := by positivity
  have hDk : D < k / 4 := by
    have : min xB ((k : ℝ) / 9) ≤ k / 9 := min_le_right _ _
    rw [hD]; linarith
  have hDosc : ∀ t₁ ≤ k, ∀ t₂ ≤ k, |s t₁ - s t₂| ≤ D :=
    osc_le_of_abs_le fun t ht => le_min (hB₂ t ht) (hB₁ t ht)
  have hclose : ∀ t ≤ k, |s t - Real.sqrt v * gapKeys q.2 t| ≤ a := fun t ht => hSA t ht
  obtain ⟨lam, c, h⟩ := affine_of_keys_close (g := fun t => Real.sqrt v * gapKeys q.2 t) hk hD0
    hDk hDosc hclose hfit
  have hDD : 2 * D ^ 2 / k ≤ 8 * xB ^ 2 / k := by
    have hmin : min xB ((k : ℝ) / 9) ≤ xB := min_le_left _ _
    have hmin0 : 0 ≤ min xB ((k : ℝ) / 9) := le_min hxB (by positivity)
    rw [div_le_div_iff_of_pos_right hk0, hD]
    nlinarith [mul_le_mul hmin hmin hmin0 hxB]
  refine affErr_le_of_fit (lam := lam) (c := c) fun t ht => ?_
  have := h t ht
  calc |Real.sqrt v * gapKeys q.2 t - lam * t - c| ≤ eps + 2 * D ^ 2 / k + a := this
    _ ≤ eps + a + 8 * xB ^ 2 / k := by linarith

/-- Off the bad events, a small affine-fit error of the Gaussian walk forces `T > k`. -/
theorem lt_gapSegLen_of_affErr_le {eps v a xB y : ℝ} (hxB : 0 ≤ xB)
    {k : ℕ} (hk : 1 ≤ k) (hy : y < eps - a - 8 * xB ^ 2 / k) {q : (ℕ → ℝ) × (ℕ → ℝ)}
    (hΨ : affErr v k q.2 ≤ y)
    (hSA : ∀ t ≤ k, |gapKeys q.1 t - t - Real.sqrt v * gapKeys q.2 t| ≤ a)
    (hB₁ : ∀ t ≤ k, |gapKeys q.1 t - t| ≤ k / 9)
    (hB₂ : ∀ t ≤ k, |gapKeys q.1 t - t| ≤ xB) :
    (k : ℕ∞) < gapSegLen eps q.1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set e' := eps - a - 8 * xB ^ 2 / k with he'
  obtain ⟨lam, c, hfit⟩ := exists_fit_of_affErr_lt (lt_of_le_of_lt hΨ hy)
  set s : ℕ → ℝ := fun t => gapKeys q.1 t - t with hs
  set D : ℝ := 2 * min xB ((k : ℝ) / 9) with hD
  have hD0 : 0 ≤ D := by positivity
  have hDk : D < k / 4 := by
    have : min xB ((k : ℝ) / 9) ≤ k / 9 := min_le_right _ _
    rw [hD]; linarith
  have hDosc : ∀ t₁ ≤ k, ∀ t₂ ≤ k, |s t₁ - s t₂| ≤ D :=
    osc_le_of_abs_le fun t ht => le_min (hB₂ t ht) (hB₁ t ht)
  have hclose : ∀ t ≤ k, |s t - Real.sqrt v * gapKeys q.2 t| ≤ a := fun t ht => hSA t ht
  obtain ⟨a', b', h⟩ := keys_of_affine_close (g := fun t => Real.sqrt v * gapKeys q.2 t) hk hD0
    hDk hDosc hclose (fun t ht => (hfit t ht).le)
  have hDD : 2 * D ^ 2 / k ≤ 8 * xB ^ 2 / k := by
    have hmin : min xB ((k : ℝ) / 9) ≤ xB := min_le_left _ _
    have hmin0 : 0 ≤ min xB ((k : ℝ) / 9) := le_min hxB (by positivity)
    rw [div_le_div_iff_of_pos_right hk0, hD]
    nlinarith [mul_le_mul hmin hmin hmin0 hxB]
  rw [lt_gapSegLen_iff_fit]
  refine ⟨a', b', fun t ht => ?_⟩
  have := h t ht
  calc |(t : ℝ) - (a' * (t + (gapKeys q.1 t - t)) + b')| ≤ e' + a + 2 * D ^ 2 / k := this
    _ ≤ eps := by rw [he']; linarith

/-! ## The sandwich -/

/-- **Per-integer sandwich, upper bound.** -/
theorem perInteger_upper {eps v a xB pSA p₁ p₂ : ℝ} {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hv : 0 < v) (ha : 0 ≤ a) (hxB : 0 ≤ xB) (heps : 0 < eps)
    (h1 : π.map Prod.fst = iidLaw ν) (h2 : π.map Prod.snd = iidLaw gaussPM)
    (hSA : π.real (SAEvent v a n) ≤ pSA)
    (hB₁ : (iidLaw ν).real (walkBad ((k : ℝ) / 9) k) ≤ p₁)
    (hB₂ : (iidLaw ν).real (walkBad xB k) ≤ p₂)
    {𝒯 : Measure ℝ} {θτ Eτ : ℝ} (hL : LifetimeSide 𝒯 θτ Eτ) {ρ : ℝ} (hρ : 0 < ρ) :
    (iidLaw ν).real {g | (k : ℕ∞) < gapSegLen eps g} ≤
      𝒯.real (Ici (v * k / (eps + (a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ)) ^ 2)) +
        pSA + p₁ + p₂ + 2 * n * Real.exp (-ρ ^ 2 / 2) := by
  set xD := 8 * xB ^ 2 / k with hxD
  have hxD0 : 0 ≤ xD := by positivity
  set y := eps + a + xD with hy
  have hy0 : 0 < y := by positivity
  -- transfer everything to the coupling space
  rw [real_fst_event h1 (measurableSet_lt_gapSegLen eps k)]
  rw [real_fst_event h1 (measurableSet_walkBad _ _)] at hB₁ hB₂
  have hΨ := hL.walk_le v hv n k hk hkn y ρ hy0 hρ
  rw [real_snd_event h2 (measurableSet_le (measurable_affErr v k) measurable_const)] at hΨ
  -- the inclusion
  have hsub : {q : (ℕ → ℝ) × (ℕ → ℝ) | (k : ℕ∞) < gapSegLen eps q.1} ⊆
      {q | q.2 ∈ {ζ | affErr v k ζ ≤ y}} ∪ (SAEvent v a n ∪
        ({q | q.1 ∈ walkBad ((k : ℝ) / 9) k} ∪ {q | q.1 ∈ walkBad xB k})) := by
    intro q hq
    by_cases hbad : q ∈ SAEvent v a n ∪
        ({q | q.1 ∈ walkBad ((k : ℝ) / 9) k} ∪ {q | q.1 ∈ walkBad xB k})
    · exact Or.inr hbad
    · left
      simp only [Set.mem_union, not_or, SAEvent, walkBad, Set.mem_ofPred_eq, not_exists,
        not_and, not_lt] at hbad
      obtain ⟨hSAq, hB₁q, hB₂q⟩ := hbad
      show affErr v k q.2 ≤ y
      exact affErr_le_of_lt_gapSegLen hxB hk hq
        (fun t ht => hSAq t (ht.trans hkn)) hB₁q hB₂q
  calc π.real {q | (k : ℕ∞) < gapSegLen eps q.1}
      ≤ π.real ({q | q.2 ∈ {ζ | affErr v k ζ ≤ y}} ∪ (SAEvent v a n ∪
          ({q | q.1 ∈ walkBad ((k : ℝ) / 9) k} ∪ {q | q.1 ∈ walkBad xB k}))) :=
        measureReal_mono hsub
    _ ≤ π.real {q | q.2 ∈ {ζ | affErr v k ζ ≤ y}} + (π.real (SAEvent v a n) +
          (π.real {q | q.1 ∈ walkBad ((k : ℝ) / 9) k} + π.real {q | q.1 ∈ walkBad xB k})) := by
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        exact measureReal_union_le _ _
    _ ≤ (𝒯.real (Ici (v * k / (y + 2 * Real.sqrt v * ρ) ^ 2)) + 2 * n * Real.exp (-ρ ^ 2 / 2)) +
          (pSA + (p₁ + p₂)) := by gcongr
    _ = _ := by rw [hy]; ring_nf

/-- **Per-integer sandwich, lower bound.** -/
theorem perInteger_lower {eps v a xB pSA p₁ p₂ : ℝ} {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hv : 0 < v) (ha : 0 ≤ a) (hxB : 0 ≤ xB)
    (h1 : π.map Prod.fst = iidLaw ν) (h2 : π.map Prod.snd = iidLaw gaussPM)
    (hSA : π.real (SAEvent v a n) ≤ pSA)
    (hB₁ : (iidLaw ν).real (walkBad ((k : ℝ) / 9) k) ≤ p₁)
    (hB₂ : (iidLaw ν).real (walkBad xB k) ≤ p₂)
    {𝒯 : Measure ℝ} {θτ Eτ : ℝ} (hL : LifetimeSide 𝒯 θτ Eτ) {ρ : ℝ} (hρ : 0 < ρ)
    (hχ : 2 * (a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ) < eps) :
    𝒯.real (Ici (v * k / (eps - 2 * (a + 8 * xB ^ 2 / k + 2 * Real.sqrt v * ρ)) ^ 2)) -
        2 * n * Real.exp (-ρ ^ 2 / 2) - pSA - p₁ - p₂ ≤
      (iidLaw ν).real {g | (k : ℕ∞) < gapSegLen eps g} := by
  set xD := 8 * xB ^ 2 / k with hxD
  have hxD0 : 0 ≤ xD := by positivity
  set xΓ := 2 * Real.sqrt v * ρ with hxΓ
  have hxΓ0 : 0 < xΓ := by positivity
  set χ := a + xD + xΓ with hχdef
  -- `y = ε - 2χ + x_Γ`: then `y - x_Γ = ε - 2χ` and `y < ε - a - x_D`
  set y := eps - 2 * χ + xΓ with hy
  have hyΓ : xΓ < y := by rw [hy]; linarith
  have hy' : y < eps - a - xD := by rw [hy, hχdef]; linarith
  have hyΓ' : y - xΓ = eps - 2 * χ := by rw [hy]; ring
  rw [real_fst_event h1 (measurableSet_lt_gapSegLen eps k)]
  rw [real_fst_event h1 (measurableSet_walkBad _ _)] at hB₁ hB₂
  have hΨ := hL.walk_ge v hv n k hk hkn y ρ hρ hyΓ
  rw [real_snd_event h2 (measurableSet_le (measurable_affErr v k) measurable_const), hyΓ'] at hΨ
  have hsub : {q : (ℕ → ℝ) × (ℕ → ℝ) | q.2 ∈ {ζ | affErr v k ζ ≤ y}} ⊆
      {q | (k : ℕ∞) < gapSegLen eps q.1} ∪ (SAEvent v a n ∪
        ({q | q.1 ∈ walkBad ((k : ℝ) / 9) k} ∪ {q | q.1 ∈ walkBad xB k})) := by
    intro q hq
    by_cases hbad : q ∈ SAEvent v a n ∪
        ({q | q.1 ∈ walkBad ((k : ℝ) / 9) k} ∪ {q | q.1 ∈ walkBad xB k})
    · exact Or.inr hbad
    · left
      simp only [Set.mem_union, not_or, SAEvent, walkBad, Set.mem_ofPred_eq, not_exists,
        not_and, not_lt] at hbad
      obtain ⟨hSAq, hB₁q, hB₂q⟩ := hbad
      exact lt_gapSegLen_of_affErr_le hxB hk hy' hq
        (fun t ht => hSAq t (ht.trans hkn)) hB₁q hB₂q
  have hun : π.real {q | q.2 ∈ {ζ | affErr v k ζ ≤ y}} ≤
      π.real {q | (k : ℕ∞) < gapSegLen eps q.1} + (pSA + (p₁ + p₂)) := by
    calc π.real {q | q.2 ∈ {ζ | affErr v k ζ ≤ y}}
        ≤ π.real ({q | (k : ℕ∞) < gapSegLen eps q.1} ∪ (SAEvent v a n ∪
            ({q | q.1 ∈ walkBad ((k : ℝ) / 9) k} ∪ {q | q.1 ∈ walkBad xB k}))) :=
          measureReal_mono hsub
      _ ≤ π.real {q | (k : ℕ∞) < gapSegLen eps q.1} + (π.real (SAEvent v a n) +
            (π.real {q | q.1 ∈ walkBad ((k : ℝ) / 9) k} + π.real {q | q.1 ∈ walkBad xB k})) := by
          refine (measureReal_union_le _ _).trans ?_
          gcongr
          refine (measureReal_union_le _ _).trans ?_
          gcongr
          exact measureReal_union_le _ _
      _ ≤ _ := by gcongr
  show _ ≤ π.real {q : (ℕ → ℝ) × (ℕ → ℝ) | (k : ℕ∞) < gapSegLen eps q.1}
  linarith

end

end PGM
