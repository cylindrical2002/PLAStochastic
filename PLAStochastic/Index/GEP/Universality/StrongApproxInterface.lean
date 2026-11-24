import PLAStochastic.Index.GEP.Universality.Defs
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# WP5: the two interfaces of the reduction `(SA) + Brownian side ⟹ (U)`

Blueprint `kmt-blueprint/main.tex` §2.3 (Theorem `thm:SA`) and §8.1 (imported Brownian facts).
This file only defines objects and the two interface propositions; nothing here is assumed.

* `affErr v k ζ` is the affine-fit error `inf_{λ,c} max_{t ≤ k} |√v · G_t - λ t - c|` of the
  scaled Gaussian walk `G_t = ∑_{i<t} ζ_i` (blueprint `Ψ_k(ζ)`), with the infimum over rational
  pairs so that measurability is immediate.
* `HasSACoupling ν n a p`: a law on pairs of sequences with marginals `iidLaw ν` and
  `iidLaw gaussPM` under which `max_{k ≤ n} |S_k - k - √v G_k| > a` has probability `≤ p`.
* `StrongApproxClass`: (SA) with constants uniform over `UnivClass ∩ SmoothPart`.
* `LifetimeSide 𝒯 θτ Eτ`: what the Brownian package must supply — the lifetime law `𝒯`
  (`Law τ` of `optimalUnitLifetime`), its exponential moment, and the comparison of the
  Gaussian-walk affine error with the scaled lifetime tail (blueprint Lemmas 7.4(b)(c), 7.5 and
  the grid-oscillation bound `B₃`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-- The standard Gaussian law as a probability measure. -/
def gaussPM : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

/-! ## The affine-fit error of the scaled Gaussian walk -/

theorem range_succ_nonempty (k : ℕ) : (Finset.range (k + 1)).Nonempty := ⟨0, by simp⟩

/-- `max_{t ≤ k} |√v · gapKeys ζ t - λ t - c|`. -/
def maxDev (v : ℝ) (k : ℕ) (lam c : ℝ) (ζ : ℕ → ℝ) : ℝ :=
  (Finset.range (k + 1)).sup' (range_succ_nonempty k)
    (fun t : ℕ => |Real.sqrt v * gapKeys ζ t - lam * t - c|)

theorem maxDev_le_iff {v : ℝ} {k : ℕ} {lam c : ℝ} {ζ : ℕ → ℝ} {e : ℝ} :
    maxDev v k lam c ζ ≤ e ↔ ∀ t ≤ k, |Real.sqrt v * gapKeys ζ t - lam * t - c| ≤ e := by
  unfold maxDev
  rw [Finset.sup'_le_iff]
  constructor
  · intro h t ht
    exact h t (by simpa [Finset.mem_range, Nat.lt_succ_iff] using ht)
  · intro h t ht
    exact h t (by simpa [Finset.mem_range, Nat.lt_succ_iff] using ht)

theorem maxDev_lt_iff {v : ℝ} {k : ℕ} {lam c : ℝ} {ζ : ℕ → ℝ} {e : ℝ} :
    maxDev v k lam c ζ < e ↔ ∀ t ≤ k, |Real.sqrt v * gapKeys ζ t - lam * t - c| < e := by
  unfold maxDev
  rw [Finset.sup'_lt_iff]
  constructor
  · intro h t ht
    exact h t (by simpa [Finset.mem_range, Nat.lt_succ_iff] using ht)
  · intro h t ht
    exact h t (by simpa [Finset.mem_range, Nat.lt_succ_iff] using ht)

theorem maxDev_nonneg (v : ℝ) (k : ℕ) (lam c : ℝ) (ζ : ℕ → ℝ) : 0 ≤ maxDev v k lam c ζ :=
  le_trans (abs_nonneg _) (Finset.le_sup' (fun t : ℕ =>
    |Real.sqrt v * gapKeys ζ t - lam * t - c|) (show 0 ∈ Finset.range (k + 1) by simp))

theorem measurable_gapKeys_apply (t : ℕ) : Measurable fun ζ : ℕ → ℝ => gapKeys ζ t :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

theorem measurable_maxDev (v : ℝ) (k : ℕ) (lam c : ℝ) : Measurable (maxDev v k lam c) := by
  have e : maxDev v k lam c = (Finset.range (k + 1)).sup' (range_succ_nonempty k)
      (fun t : ℕ => fun ζ : ℕ → ℝ => |Real.sqrt v * gapKeys ζ t - lam * t - c|) := by
    funext ζ
    rw [Finset.sup'_apply]
    rfl
  rw [e]
  exact Finset.measurable_sup' _ fun t _ =>
    (((measurable_const.mul (measurable_gapKeys_apply t)).sub_const _).sub_const _).abs

/-- The affine-fit error `Ψ_k(ζ)` of the scaled Gaussian walk, as an infimum over rational
`(λ, c)`. -/
def affErr (v : ℝ) (k : ℕ) (ζ : ℕ → ℝ) : ℝ :=
  ⨅ p : ℚ × ℚ, maxDev v k (p.1 : ℝ) (p.2 : ℝ) ζ

theorem measurable_affErr (v : ℝ) (k : ℕ) : Measurable (affErr v k) :=
  Measurable.iInf fun _ => measurable_maxDev v k _ _

theorem bddBelow_maxDev_range (v : ℝ) (k : ℕ) (ζ : ℕ → ℝ) :
    BddBelow (Set.range fun p : ℚ × ℚ => maxDev v k (p.1 : ℝ) (p.2 : ℝ) ζ) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact maxDev_nonneg _ _ _ _ _⟩

theorem affErr_nonneg (v : ℝ) (k : ℕ) (ζ : ℕ → ℝ) : 0 ≤ affErr v k ζ :=
  le_ciInf fun _ => maxDev_nonneg _ _ _ _ _

/-- A real affine fit with error `e` gives `affErr ≤ e` (rational approximation). -/
theorem affErr_le_of_fit {v : ℝ} {k : ℕ} {ζ : ℕ → ℝ} {lam c e : ℝ}
    (h : ∀ t ≤ k, |Real.sqrt v * gapKeys ζ t - lam * t - c| ≤ e) : affErr v k ζ ≤ e := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hk : (0 : ℝ) < k + 1 := by positivity
  obtain ⟨q₁, hq₁⟩ := exists_rat_near lam (show 0 < η / (2 * (k + 1)) by positivity)
  obtain ⟨q₂, hq₂⟩ := exists_rat_near c (show 0 < η / 2 by positivity)
  have hle : maxDev v k (q₁ : ℝ) (q₂ : ℝ) ζ ≤ e + η / 2 + η / 2 * (k / (k + 1)) := by
    rw [maxDev_le_iff]
    intro t ht
    have ht' : (t : ℝ) ≤ k := by exact_mod_cast ht
    have h1 := h t ht
    calc |Real.sqrt v * gapKeys ζ t - (q₁ : ℝ) * t - (q₂ : ℝ)|
        = |(Real.sqrt v * gapKeys ζ t - lam * t - c) + (lam - q₁) * t + (c - q₂)| := by
          ring_nf
      _ ≤ |Real.sqrt v * gapKeys ζ t - lam * t - c| + |(lam - q₁) * t| + |c - q₂| :=
          abs_add_three _ _ _
      _ ≤ e + η / (2 * (k + 1)) * k + η / 2 := by
          rw [abs_mul, Nat.abs_cast]
          have h2 : |lam - q₁| * (t : ℝ) ≤ η / (2 * (k + 1)) * k :=
            mul_le_mul hq₁.le ht' (by positivity) (by positivity)
          linarith
      _ = e + η / 2 + η / 2 * (k / (k + 1)) := by field_simp; ring
  have hlt : e + η / 2 + η / 2 * (k / (k + 1)) < e + η := by
    have : (k : ℝ) / (k + 1) < 1 := by rw [div_lt_one hk]; linarith
    nlinarith
  exact lt_of_le_of_lt (ciInf_le (bddBelow_maxDev_range v k ζ) (q₁, q₂)) (hle.trans_lt hlt)

/-- `affErr < e` gives a real affine fit with error `< e`. -/
theorem exists_fit_of_affErr_lt {v : ℝ} {k : ℕ} {ζ : ℕ → ℝ} {e : ℝ} (h : affErr v k ζ < e) :
    ∃ lam c : ℝ, ∀ t ≤ k, |Real.sqrt v * gapKeys ζ t - lam * t - c| < e := by
  obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt h
  exact ⟨p.1, p.2, maxDev_lt_iff.1 hp⟩

/-! ## The (SA) coupling -/

/-- The bad event of (SA) at horizon `n`: `max_{k ≤ n} |S_k - k - √v G_k| > a`. -/
def SAEvent (v a : ℝ) (n : ℕ) : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {q | ∃ k ≤ n, a < |gapKeys q.1 k - k - Real.sqrt v * gapKeys q.2 k|}

theorem measurableSet_SAEvent (v a : ℝ) (n : ℕ) : MeasurableSet (SAEvent v a n) := by
  have : SAEvent v a n = ⋃ k, ⋃ (_ : k ≤ n),
      {q : (ℕ → ℝ) × (ℕ → ℝ) | a < |gapKeys q.1 k - k - Real.sqrt v * gapKeys q.2 k|} := by
    ext q; simp [SAEvent]
  rw [this]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_lt measurable_const
    ((((measurable_gapKeys_apply k).comp measurable_fst).sub_const _).sub
      (measurable_const.mul ((measurable_gapKeys_apply k).comp measurable_snd))).abs

/-- A coupling of iid `ν`-gaps and iid standard Gaussians with (SA) error `a` at horizon `n`,
failing with probability at most `p`. -/
def HasSACoupling (ν : ProbabilityMeasure ℝ) (n : ℕ) (a p : ℝ) : Prop :=
  ∃ π : Measure ((ℕ → ℝ) × (ℕ → ℝ)), IsProbabilityMeasure π ∧
    π.map Prod.fst = iidLaw ν ∧ π.map Prod.snd = iidLaw gaussPM ∧
    π.real (SAEvent (lawVar ν) a n) ≤ p

/-- **(SA) over a class** (blueprint Theorem 2.3 with `A = 2`): constants `K`, `n₀` depending
only on the class parameters, such that every `ν` in `UnivClass ∩ SmoothPart` has an (SA)
coupling at every horizon `n ≥ n₀` with error `K n^{1/8} √(log n)` and failure `n⁻²`. -/
def StrongApproxClass (vlo vhi κ₃ B θ D c₀ : ℝ) : Prop :=
  ∃ K : ℝ, ∃ n₀ : ℕ, 0 ≤ K ∧ 16 ≤ n₀ ∧
    ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c₀ ν →
      ∀ n : ℕ, n₀ ≤ n →
        HasSACoupling ν n (K * (n : ℝ) ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n))
          ((n : ℝ) ^ (-(2 : ℝ)))

/-! ## The Brownian side -/

/-- **What the Brownian package supplies.**  `𝒯` is the law of the optimal unit lifetime
`τ` of Brownian motion; `s̄(t) = 𝒯 [t, ∞)`.  `walk_le`/`walk_ge` compare the affine-fit error
of the scaled Gaussian walk on `{0, …, k}` with the scaled lifetime tail, up to the grid
oscillation `2√v ρ` and its failure probability `2 n e^{-ρ²/2}` (blueprint Lemma 7.4(b)(c),
Lemma 7.5 and `B₃`). -/
structure LifetimeSide (𝒯 : Measure ℝ) (θτ Eτ : ℝ) : Prop where
  prob : IsProbabilityMeasure 𝒯
  nonneg : 𝒯 (Iio 0) = 0
  θpos : 0 < θτ
  expMom : ∫⁻ t, ENNReal.ofReal (Real.exp (θτ * t)) ∂𝒯 ≤ ENNReal.ofReal Eτ
  walk_le : ∀ v : ℝ, 0 < v → ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ y ρ : ℝ, 0 < y → 0 < ρ →
    (iidLaw gaussPM).real {ζ | affErr v k ζ ≤ y} ≤
      𝒯.real (Ici (v * k / (y + 2 * Real.sqrt v * ρ) ^ 2)) + 2 * n * Real.exp (-ρ ^ 2 / 2)
  walk_ge : ∀ v : ℝ, 0 < v → ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ y ρ : ℝ, 0 < ρ →
    2 * Real.sqrt v * ρ < y →
    𝒯.real (Ici (v * k / (y - 2 * Real.sqrt v * ρ) ^ 2)) - 2 * n * Real.exp (-ρ ^ 2 / 2) ≤
      (iidLaw gaussPM).real {ζ | affErr v k ζ ≤ y}

end

end PGM
