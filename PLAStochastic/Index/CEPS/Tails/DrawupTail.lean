import PLAStochastic.Index.CEPS.Tails.Cramer

/-!
# Long-time tails of the actual positive-drift drawup

Drawup survival forces the terminal walk position below the level. Subtracting
half the drift reduces this event to the W-7 endpoint deviation. This controls
the drawup occupation beyond the `w³` cutoff independently of the segment tail.
-/

namespace PGM

noncomputable section

open MeasureTheory Set WienerHopf

/-- A surviving drawup has terminal position at most its level. -/
theorem cepsDrawupOK_endpoint {β a l : ℝ} {g : ℕ → ℝ} {n : ℕ}
    (h : cepsDrawupOK β a l g n) : kWalk 0 β a g n ≤ l := by
  have hn := h 0 n (Nat.zero_le n) le_rfl
  simpa only [kWalk_zero, sub_zero] using hn

/-- Endpoint Cramér bound for drawup survival, uniformly over regular gap laws. -/
theorem measureReal_cepsDrawupOK_le_of_regLaw {ν : ProbabilityMeasure ℝ}
    {D θ vlo vhi δ l : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D)
    (hvlo : 0 < vlo) (hδ : 0 < δ) (n : ℕ) (hn : l ≤ δ * n / 2) :
    (iidLaw ν).real {g | cepsDrawupOK (1 + δ) 1 l g n} ≤
      Real.exp (-(driftRate (D * Real.exp θ) θ (δ / 2) * (δ * n - l))) := by
  obtain ⟨f, hf⟩ := hν.exists_isGapLaw hθ hvlo
  have hsub : {g | cepsDrawupOK (1 + δ) 1 l g n} ⊆
      {g | kWalk 0 (1 + δ / 2) 1 g n ≤ -(δ * n / 2 - l)} := by
    intro g hg
    have hend := cepsDrawupOK_endpoint hg
    change kWalk 0 (1 + δ / 2) 1 g n ≤ -(δ * n / 2 - l)
    unfold kWalk at hend ⊢
    nlinarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  have h := measureReal_cepsWalk_le_neg_of_gapLaw hf hθ hD (show 0 < δ / 2 by positivity)
    le_rfl n (show 0 ≤ δ * n / 2 - l by linarith)
  convert h using 2
  congr 2
  ring

/-- A convenient geometric form of the long-time drawup tail. -/
theorem measureReal_cepsDrawupOK_geometric_of_regLaw {ν : ProbabilityMeasure ℝ}
    {D θ vlo vhi δ l : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D)
    (hvlo : 0 < vlo) (hδ : 0 < δ) (n : ℕ) (hn : 2 * l ≤ δ * n / 2) :
    (iidLaw ν).real {g | cepsDrawupOK (1 + δ) 1 l g n} ≤
      Real.exp (-(driftRate (D * Real.exp θ) θ (δ / 2) * δ / 2) * n) := by
  have hn' : l ≤ δ * n / 2 := by
    have hnn : 0 ≤ δ * (n : ℝ) := by positivity
    linarith
  refine (measureReal_cepsDrawupOK_le_of_regLaw hν hθ hD hvlo hδ n hn').trans ?_
  have hc := driftRate_pos hθ (show 0 < D * Real.exp θ by positivity) (show 0 < δ / 2 by positivity)
  rw [Real.exp_le_exp]
  nlinarith

/-- The actual drawup occupation has a summable long-time survival tail. -/
theorem summable_cepsDrawupOK_tail_of_regLaw {ν : ProbabilityMeasure ℝ}
    {D θ vlo vhi δ l : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D)
    (hvlo : 0 < vlo) (hδ : 0 < δ) (N : ℕ) (hN : 2 * l ≤ δ * N / 2) :
    Summable (fun n : ℕ => (iidLaw ν).real
      {g | cepsDrawupOK (1 + δ) 1 l g (N + n)}) ∧
    (∑' n : ℕ, (iidLaw ν).real {g | cepsDrawupOK (1 + δ) 1 l g (N + n)}) ≤
      Real.exp (-(driftRate (D * Real.exp θ) θ (δ / 2) * δ / 2) * N) /
        (1 - Real.exp (-(driftRate (D * Real.exp θ) θ (δ / 2) * δ / 2))) := by
  set a := driftRate (D * Real.exp θ) θ (δ / 2) * δ / 2
  have hc := driftRate_pos hθ (show 0 < D * Real.exp θ by positivity) (show 0 < δ / 2 by positivity)
  have ha : 0 < a := by positivity
  have hr0 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => Real.exp (-a * N) * Real.exp (-a) ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∀ n : ℕ, (iidLaw ν).real {g | cepsDrawupOK (1 + δ) 1 l g (N + n)} ≤
      Real.exp (-a * N) * Real.exp (-a) ^ n := by
    intro n
    have hn : 2 * l ≤ δ * ((N + n : ℕ) : ℝ) / 2 := by
      push_cast
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine (measureReal_cepsDrawupOK_geometric_of_regLaw hν hθ hD hvlo hδ (N + n) hn).trans
      (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hs := hgeom.of_nonneg_of_le (fun _ => measureReal_nonneg) hle
  refine ⟨hs, (hs.tsum_le_tsum hle hgeom).trans (le_of_eq ?_)⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

end

end PGM
