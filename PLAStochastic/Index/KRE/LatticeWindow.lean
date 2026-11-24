import PLAStochastic.Index.GRE.FixedParameter
import PLAStochastic.Index.Model.ExpGaps
import PLAStochastic.Index.Algorithm.GreedyMinimality

/-!
# No long feasible lattice windows (window tail for the lattice walks)

For iid gaps `g` and a lattice spacing `d ≥ 1`, the lattice walk
`latWalk g d ω j = g 0 + ⋯ + g (j d - 1)` reads the gap walk at the multiples of `d`.
Its window starting at lattice index `a` is, up to translation, the walk of the block
gaps `blockGap (fun t => g (a d + t)) d` (`windowFeasible_latWalk_iff`), whose law is a
`GapLaw` with parameters `(d μ, √d σ, 2 d √d σ³ + d κ)`.  The one-layer geometric
tail (`measureReal_layerSegLen_gt_le`) then bounds the probability that a window of
`τ ≥ j L + 1` lattice keys is `eps`-feasible by `(71/72)^j`, once the half block
length `h` (`L = 2 h`) satisfies four explicit size conditions
(`measureReal_windowBad_le_of`).

For standard exponential gaps (`GapLaw P g 1 1 16`) the choice
`kreHalf eps d = ⌊2592 d eps²⌋₊ + 162`, `kreL eps d = 2 kreHalf eps d` meets them for
every `d ≥ 1` and `eps ≥ 0` (`measureReal_windowBad_le`).  A union bound over all
spacings and starting indices `d, a ≤ 2n` gives the global event `vBad`
(`measureReal_vBad_le`), off which no lattice window of `j L + 1` keys is feasible
(`not_windowFeasible_of_not_vBad` and its offset versions).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## The lattice walk and its window events -/

/-- The gap walk read at the multiples of `d`: `latWalk g d ω j = ∑_{i < j d} g i ω`. -/
def latWalk (g : ℕ → Ω → ℝ) (d : ℕ) (ω : Ω) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j * d), g i ω

/-- The window of `τ` lattice keys starting at lattice index `a` is `eps`-feasible. -/
def windowBad (eps : ℝ) (g : ℕ → Ω → ℝ) (d a τ : ℕ) : Set Ω :=
  {ω | windowFeasible eps (latWalk g d ω) a (a + τ)}

omit mΩ in
/-- The lattice walk seen from lattice index `a` is a translate of the block walk of the
gaps shifted by `a d`. -/
theorem shiftSeq_latWalk (g : ℕ → Ω → ℝ) (d a : ℕ) (ω : Ω) (i : ℕ) :
    shiftSeq (latWalk g d ω) a i =
      gapKeys (seq (blockGap (fun t => g (a * d + t)) d) ω) i + latWalk g d ω a := by
  rw [gapKeys_blockGap]
  simp only [shiftSeq_apply, latWalk, gapKeys, seq, add_mul, sum_range_add]
  ring

omit mΩ in
/-- **Stationarity.** A lattice window is feasible iff the corresponding prefix of the
block walk of the shifted gaps is. -/
theorem windowFeasible_latWalk_iff (eps : ℝ) (g : ℕ → Ω → ℝ) (d a τ : ℕ) (ω : Ω) :
    windowFeasible eps (latWalk g d ω) a (a + τ) ↔
      prefixAffineFeasible eps (gapKeys (seq (blockGap (fun t => g (a * d + t)) d) ω)) τ := by
  unfold windowFeasible
  rw [Nat.add_sub_cancel_left]
  rw [← prefixAffineFeasible_affine_iff
    (p := gapKeys (seq (blockGap (fun t => g (a * d + t)) d) ω)) (s := 1)
    (c := latWalk g d ω a) one_ne_zero]
  exact prefixAffineFeasible_congr fun i _ => by rw [shiftSeq_latWalk]; ring

/-- Window feasibility is invariant under translating the keys. -/
theorem windowFeasible_const_add_iff (eps : ℝ) (p : ℕ → ℝ) (x0 : ℝ) (a b : ℕ) :
    windowFeasible eps (fun k => x0 + p k) a b ↔ windowFeasible eps p a b := by
  unfold windowFeasible
  rw [← prefixAffineFeasible_affine_iff (p := shiftSeq p a) (s := 1) (c := x0) one_ne_zero]
  exact prefixAffineFeasible_congr fun i _ => by simp only [shiftSeq_apply]; ring

theorem measurable_latWalk {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s)) (d : ℕ) :
    Measurable fun ω => latWalk g d ω :=
  measurable_pi_lambda _ fun _ => Finset.measurable_sum _ fun i _ => hg i

theorem measurableSet_windowBad {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s)) (eps : ℝ)
    (d a τ : ℕ) : MeasurableSet (windowBad eps g d a τ) :=
  (measurable_shiftSeq a).comp (measurable_latWalk hg d)
    (measurableSet_prefixAffineFeasible eps (a + τ - a))

/-! ## The window tail -/

/-- **Window tail, general law.** If the half block length `h` satisfies the four size
conditions, a window of `τ ≥ j (2 h) + 1` lattice keys is feasible with probability at
most `(71/72)^j`. -/
theorem measureReal_windowBad_le_of [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ σ κ : ℝ}
    (hg : GapLaw P g μ σ κ) {eps : ℝ} (heps : 0 ≤ eps) {d : ℕ} (hd : 1 ≤ d) {h : ℕ}
    (H1 : 2592 * μ ^ 2 * d * eps ^ 2 < σ ^ 2 * h)
    (H2 : (2 * σ ^ 3 + κ) ^ 2 ≤ 2 * σ ^ 6 * h)
    (H3 : 2 * eps ≤ h) (H4 : 144 * σ ^ 2 ≤ μ ^ 2 * h)
    (j a τ : ℕ) (hτ : j * (2 * h) + 1 ≤ τ) :
    P.real (windowBad eps g d a τ) ≤ (71 / 72 : ℝ) ^ j := by
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have hκ := hg.kappa_nonneg
  have hlaw := (hg.shift (a * d)).block hd
  set D : ℝ := (d : ℝ) with hD
  have hD1 : (1 : ℝ) ≤ D := by rw [hD]; exact_mod_cast hd
  have hD0 : (0 : ℝ) < D := by linarith
  set sd : ℝ := Real.sqrt D with hsd
  have hsd2 : sd ^ 2 = D := Real.sq_sqrt hD0.le
  have hsd1 : 1 ≤ sd := by
    rw [hsd, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hD1
  have hsd0 : 0 < sd := by linarith
  set H : ℝ := (h : ℝ) with hH
  have hH0 : 0 ≤ H := Nat.cast_nonneg h
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · exfalso
      rw [hH, h0, Nat.cast_zero, mul_zero] at H4
      have : 0 < 144 * σ ^ 2 := by positivity
      linarith
    · exact h0
  have hL : ((2 * h : ℕ) : ℝ) = 2 * H := by rw [hH]; push_cast; ring
  have B1 : 5184 * (D * μ) ^ 2 * eps ^ 2 < (sd * σ) ^ 2 * ((2 * h : ℕ) : ℝ) := by
    rw [hL, mul_pow sd σ, hsd2]
    have := mul_lt_mul_of_pos_left H1 (by positivity : (0 : ℝ) < 2 * D)
    calc 5184 * (D * μ) ^ 2 * eps ^ 2 = 2 * D * (2592 * μ ^ 2 * D * eps ^ 2) := by ring
      _ < 2 * D * (σ ^ 2 * H) := this
      _ = D * σ ^ 2 * (2 * H) := by ring
  have B2 : (2 * D * sd * σ ^ 3 + D * κ) ^ 2 ≤ (sd * σ) ^ 6 * ((2 * h : ℕ) : ℝ) := by
    rw [hL]
    have hk1 : D * κ ≤ D * sd * κ := by
      have : D * κ * 1 ≤ D * κ * sd := mul_le_mul_of_nonneg_left hsd1 (by positivity)
      linarith
    have hk0 : 0 ≤ 2 * D * sd * σ ^ 3 + D * κ := by positivity
    have hk2 : 2 * D * sd * σ ^ 3 + D * κ ≤ D * sd * (2 * σ ^ 3 + κ) := by linarith
    have hsq : (2 * D * sd * σ ^ 3 + D * κ) ^ 2 ≤ (D * sd * (2 * σ ^ 3 + κ)) ^ 2 :=
      pow_le_pow_left₀ hk0 hk2 2
    have hD3 : (0 : ℝ) ≤ D ^ 3 := by positivity
    calc (2 * D * sd * σ ^ 3 + D * κ) ^ 2 ≤ (D * sd * (2 * σ ^ 3 + κ)) ^ 2 := hsq
      _ = D ^ 2 * sd ^ 2 * (2 * σ ^ 3 + κ) ^ 2 := by ring
      _ = D ^ 3 * (2 * σ ^ 3 + κ) ^ 2 := by rw [hsd2]; ring
      _ ≤ D ^ 3 * (2 * σ ^ 6 * H) := mul_le_mul_of_nonneg_left H2 hD3
      _ = (sd ^ 2) ^ 3 * σ ^ 6 * (2 * H) := by rw [hsd2]; ring
      _ = (sd * σ) ^ 6 * (2 * H) := by ring
  have B3 : 4 * eps ≤ ((2 * h : ℕ) : ℝ) := by rw [hL]; linarith
  have B4 : 288 * (sd * σ) ^ 2 ≤ (D * μ) ^ 2 * ((2 * h : ℕ) : ℝ) := by
    rw [hL, mul_pow sd σ, hsd2]
    have h1 : 0 ≤ μ ^ 2 * H := by positivity
    have h2 : μ ^ 2 * H ≤ D * (μ ^ 2 * H) := le_mul_of_one_le_left h1 hD1
    have h3 : 2 * D * (144 * σ ^ 2) ≤ 2 * D * (D * (μ ^ 2 * H)) :=
      mul_le_mul_of_nonneg_left (H4.trans h2) (by positivity)
    calc 288 * (D * σ ^ 2) = 2 * D * (144 * σ ^ 2) := by ring
      _ ≤ 2 * D * (D * (μ ^ 2 * H)) := h3
      _ = (D * μ) ^ 2 * (2 * H) := by ring
  have htail := measureReal_layerSegLen_gt_le hlaw hh rfl B1 B2 B3 B4 heps j
  rw [setOf_lt_layerSegLen] at htail
  refine le_trans (measureReal_mono fun ω hω => ?_) htail
  simp only [windowBad, Set.mem_ofPred_eq] at hω ⊢
  rw [windowFeasible_latWalk_iff] at hω
  exact prefixAffineFeasible_mono hω hτ

/-! ## Exponential gaps: explicit block length -/

/-- Half block length for standard exponential gaps: `⌊2592 d eps²⌋₊ + 162`. -/
def kreHalf (eps : ℝ) (d : ℕ) : ℕ := ⌊(2592 : ℝ) * d * eps ^ 2⌋₊ + 162

/-- Block length for standard exponential gaps: `L = 2 (⌊2592 d eps²⌋₊ + 162)`. -/
def kreL (eps : ℝ) (d : ℕ) : ℕ := 2 * kreHalf eps d

theorem kreL_eq (eps : ℝ) (d : ℕ) : kreL eps d = 2 * (⌊(2592 : ℝ) * d * eps ^ 2⌋₊ + 162) :=
  rfl

/-- Explicit upper bound on the block length. -/
theorem kreL_le (eps : ℝ) (d : ℕ) :
    (kreL eps d : ℝ) ≤ 2 * (2592 * d * eps ^ 2 + 162) := by
  have hx : (0 : ℝ) ≤ 2592 * d * eps ^ 2 := by positivity
  have hfl := Nat.floor_le hx
  simp only [kreL, kreHalf]
  push_cast
  linarith

/-- Explicit lower bound on the block length. -/
theorem lt_kreL (eps : ℝ) (d : ℕ) :
    2 * (2592 * d * eps ^ 2 + 161) < (kreL eps d : ℝ) := by
  have hfl := Nat.lt_floor_add_one ((2592 : ℝ) * d * eps ^ 2)
  simp only [kreL, kreHalf]
  push_cast
  linarith

/-- **Window tail, exponential gaps.** For `d ≥ 1`, `eps ≥ 0` and `τ ≥ j kreL eps d + 1`,
a window of `τ` lattice keys is `eps`-feasible with probability at most `(71/72)^j`. -/
theorem measureReal_windowBad_le [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    (hg : GapLaw P g 1 1 16) {eps : ℝ} (heps : 0 ≤ eps) {d : ℕ} (hd : 1 ≤ d)
    (j a τ : ℕ) (hτ : j * kreL eps d + 1 ≤ τ) :
    P.real (windowBad eps g d a τ) ≤ (71 / 72 : ℝ) ^ j := by
  have hD1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hfl := Nat.lt_floor_add_one ((2592 : ℝ) * d * eps ^ 2)
  have hH : ((kreHalf eps d : ℕ) : ℝ) = (⌊(2592 : ℝ) * d * eps ^ 2⌋₊ : ℝ) + 162 := by
    simp only [kreHalf]; push_cast; ring
  have hfl0 : (0 : ℝ) ≤ (⌊(2592 : ℝ) * d * eps ^ 2⌋₊ : ℝ) := Nat.cast_nonneg _
  have he2 : eps ^ 2 ≤ d * eps ^ 2 := le_mul_of_one_le_left (sq_nonneg eps) hD1
  have he1 : 2 * eps ≤ eps ^ 2 + 1 := by
    have h := sq_nonneg (eps - 1)
    have : (eps - 1) ^ 2 = eps ^ 2 + 1 - 2 * eps := by ring
    linarith
  have hde : 0 ≤ (d : ℝ) * eps ^ 2 := by positivity
  refine measureReal_windowBad_le_of hg heps hd (h := kreHalf eps d) ?_ ?_ ?_ ?_ j a τ hτ
  · rw [hH]; linarith
  · rw [hH]; linarith
  · rw [hH]; linarith
  · rw [hH]; linarith

/-! ## The global bad event -/

/-- Some lattice window with spacing `1 ≤ d ≤ 2n` and start `a ≤ 2n` of `j kreL eps d + 1`
keys is `eps`-feasible. -/
def vBad (eps : ℝ) (g : ℕ → Ω → ℝ) (j n : ℕ) : Set Ω :=
  ⋃ d ∈ range (2 * n + 1), ⋃ a ∈ range (2 * n + 1),
    if 1 ≤ d then windowBad eps g d a (j * kreL eps d + 1) else ∅

theorem measurableSet_vBad {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s)) (eps : ℝ)
    (j n : ℕ) : MeasurableSet (vBad eps g j n) :=
  MeasurableSet.biUnion (range (2 * n + 1)).countable_toSet fun d _ =>
    MeasurableSet.biUnion (range (2 * n + 1)).countable_toSet fun a _ => by
      split_ifs
      · exact measurableSet_windowBad hg eps d a _
      · exact MeasurableSet.empty

/-- Probability of the global bad event. -/
theorem measureReal_vBad_le [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    (hg : GapLaw P g 1 1 16) {eps : ℝ} (heps : 0 ≤ eps) (j n : ℕ) :
    P.real (vBad eps g j n) ≤ ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ j := by
  refine measureReal_biUnion_pairs_le n _ fun d a _ _ => ?_
  split_ifs with hd
  · exact measureReal_windowBad_le hg heps hd j a _ le_rfl
  · simp only [measureReal_empty]; positivity

/-! ## Pathwise consequences off the bad event -/

omit mΩ in
/-- Off `vBad`, no lattice window of `j kreL eps d + 1` keys is feasible. -/
theorem not_windowFeasible_of_not_vBad {eps : ℝ} {g : ℕ → Ω → ℝ} {j n : ℕ} {ω : Ω}
    (hω : ω ∉ vBad eps g j n) {d a : ℕ} (hd : 1 ≤ d) (hd2 : d ≤ 2 * n) (ha : a ≤ 2 * n) :
    ¬ windowFeasible eps (latWalk g d ω) a (a + (j * kreL eps d + 1)) := by
  intro hf
  have hmem : ω ∈ (if 1 ≤ d then windowBad eps g d a (j * kreL eps d + 1) else ∅) := by
    rw [if_pos hd]; exact hf
  exact hω (Set.mem_biUnion (mem_range.2 (show d < 2 * n + 1 by omega))
    (Set.mem_biUnion (mem_range.2 (show a < 2 * n + 1 by omega)) hmem))

omit mΩ in
/-- Offset version: translating the lattice walk does not change feasibility. -/
theorem not_windowFeasible_const_add_of_not_vBad {eps : ℝ} {g : ℕ → Ω → ℝ} {j n : ℕ}
    {ω : Ω} (hω : ω ∉ vBad eps g j n) (x0 : ℝ) {d a : ℕ} (hd : 1 ≤ d) (hd2 : d ≤ 2 * n)
    (ha : a ≤ 2 * n) :
    ¬ windowFeasible eps (fun k => x0 + latWalk g d ω k) a (a + (j * kreL eps d + 1)) := by
  rw [windowFeasible_const_add_iff]
  exact not_windowFeasible_of_not_vBad hω hd hd2 ha

omit mΩ in
/-- Key version: for the keys `z t = x0 + ∑_{i < t} g i ω`, no window of the lattice keys
`z (k d)` of `j kreL eps d + 1` keys is feasible. -/
theorem not_windowFeasible_lattice_of_not_vBad {eps : ℝ} {g : ℕ → Ω → ℝ} {j n : ℕ}
    {ω : Ω} (hω : ω ∉ vBad eps g j n) {x0 : ℝ} {z : ℕ → ℝ}
    (hz : ∀ t, z t = x0 + ∑ i ∈ range t, g i ω) {d a : ℕ} (hd : 1 ≤ d) (hd2 : d ≤ 2 * n)
    (ha : a ≤ 2 * n) :
    ¬ windowFeasible eps (fun k => z (k * d)) a (a + (j * kreL eps d + 1)) := by
  have hfun : (fun k => z (k * d)) = fun k => x0 + latWalk g d ω k := by
    funext k; rw [hz]; rfl
  rw [hfun]
  exact not_windowFeasible_const_add_of_not_vBad hω x0 hd hd2 ha

end

end PGM
