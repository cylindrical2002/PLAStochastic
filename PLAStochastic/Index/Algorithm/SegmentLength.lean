import PLAStochastic.Index.Algorithm.AffineFeasible
import Mathlib.Data.ENat.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Optimal PLA feasibility and the ALG-OPT segment length

`prefixAffineFeasible eps p len` (from `PLAStochastic.Index.Algorithm.AffineFeasible`) says that the first `len`
keys `p 0, …, p (len-1)` admit one affine map whose rank error is at most `eps`.
This file proves the structural facts about that predicate used by the height
proofs, and defines the greedy segment length of ALG-OPT on an infinite key
sequence:

* feasibility is monotone in the prefix, depends only on the prefix, is
  invariant under nonzero affine maps of the keys, and passes to sub-windows;
* `segLen eps p : ℕ∞` is the number of keys in the first ALG-OPT segment; it is
  `⊤` exactly when every prefix is feasible, and `t < segLen eps p` holds exactly
  when the first `t + 1` keys are feasible (`lt_segLen_iff`);
* with `q = floor (2*eps) + 1`, every segment has at least `q` keys;
* the tube criterion (a fixed line) and the second-difference criterion give
  the lower and upper bounds for the segment length used later;
* feasibility of a fixed prefix is a measurable property of the keys, which
  makes `segLen` a stopping index for the natural filtration of the gaps.
-/

namespace PGM

open Set Filter Topology

/-! ## Basic structure of prefix feasibility -/

theorem prefixAffineFeasible_mono {eps : ℝ} {p : ℕ → ℝ} {len len' : ℕ}
    (h : prefixAffineFeasible eps p len) (hle : len' ≤ len) :
    prefixAffineFeasible eps p len' := by
  rcases h with ⟨a, b, hab⟩
  exact ⟨a, b, fun i hi => hab i (lt_of_lt_of_le hi hle)⟩

theorem prefixAffineFeasible_zero (eps : ℝ) (p : ℕ → ℝ) :
    prefixAffineFeasible eps p 0 :=
  ⟨0, 0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem prefixAffineFeasible_congr {eps : ℝ} {p p' : ℕ → ℝ} {len : ℕ}
    (hpp : ∀ i < len, p i = p' i) :
    prefixAffineFeasible eps p len ↔ prefixAffineFeasible eps p' len := by
  constructor
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, fun i hi => by rw [← hpp i hi]; exact hab i hi⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, fun i hi => by rw [hpp i hi]; exact hab i hi⟩

/-- Feasibility is invariant under every nonzero affine change of the keys. -/
theorem prefixAffineFeasible_affine_iff {eps : ℝ} {p : ℕ → ℝ} {len : ℕ}
    {s c : ℝ} (hs : s ≠ 0) :
    prefixAffineFeasible eps (fun i => s * p i + c) len ↔
      prefixAffineFeasible eps p len := by
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a * s, a * c + b, fun i hi => ?_⟩
    have h := hab i hi
    have : a * (s * p i + c) + b = a * s * p i + (a * c + b) := by ring
    rwa [this] at h
  · rintro ⟨a, b, hab⟩
    refine ⟨a / s, b - a / s * c, fun i hi => ?_⟩
    have h := hab i hi
    have : a / s * (s * p i + c) + (b - a / s * c) = a * p i + b := by
      field_simp
      ring
    rwa [this]

/-- A window of a feasible prefix is feasible, with local ranks. -/
theorem prefixAffineFeasible_window {eps : ℝ} {p : ℕ → ℝ} {len r w : ℕ}
    (h : prefixAffineFeasible eps p len) (hw : r + w ≤ len) :
    prefixAffineFeasible eps (fun i => p (r + i)) w := by
  rcases h with ⟨a, b, hab⟩
  refine ⟨a, b - r, fun i hi => ?_⟩
  have h := hab (r + i) (by omega)
  have : ((r + i : ℕ) : ℝ) - (a * p (r + i) + b) =
      (i : ℝ) - (a * p (r + i) + (b - r)) := by
    push_cast
    ring
  rw [← this]
  exact h

/-- A fixed line with small rank error certifies feasibility (tube criterion). -/
theorem prefixAffineFeasible_of_line {eps : ℝ} {p : ℕ → ℝ} {len : ℕ} (a b : ℝ)
    (h : ∀ i < len, |(i : ℝ) - (a * p i + b)| ≤ eps) :
    prefixAffineFeasible eps p len :=
  ⟨a, b, h⟩

/-! ## The second-difference necessary condition -/

/--
If `2h + 1` keys with `p 0 = 0` are `eps`-feasible and the walk
`ŷ t = p t / μ - t` is not too far from zero at the right end, then the
second difference `ŷ (2h) - 2 ŷ h` is at most `12 eps`.  This is the
deterministic step of the geometric-tail argument (`lem:condtail`).
-/
theorem second_difference_of_feasible {eps μ : ℝ} {p : ℕ → ℝ} {h : ℕ}
    (hμ : 0 < μ) (hh : 0 < h) (hp0 : p 0 = 0)
    (hfeas : prefixAffineFeasible eps p (2 * h + 1))
    (hend : |p (2 * h) / μ - (2 * h : ℕ)| ≤ ((2 * h : ℕ) : ℝ) / 2)
    (hlong : 4 * eps ≤ ((2 * h : ℕ) : ℝ)) :
    |(p (2 * h) / μ - (2 * h : ℕ)) - 2 * (p h / μ - h)| ≤ 12 * eps := by
  rcases hfeas with ⟨a, b, hab⟩
  set L : ℝ := ((2 * h : ℕ) : ℝ) with hL
  have e0 := hab 0 (by omega)
  have eL := hab (2 * h) (by omega)
  have eh := hab h (by omega)
  simp only [Nat.cast_zero, hp0, mul_zero, zero_add] at e0
  -- slope in normalized coordinates
  set a' : ℝ := a * μ with ha'
  set yL : ℝ := p (2 * h) / μ - L with hyL
  set yh : ℝ := p h / μ - h with hyh
  have hpL : p (2 * h) = μ * (L + yL) := by
    rw [hyL]; field_simp; ring
  have hph : p h = μ * (h + yh) := by
    rw [hyh]; field_simp; ring
  have hLh : L = 2 * (h : ℝ) := by rw [hL]; push_cast; ring
  rw [hpL] at eL
  rw [hph] at eh
  have eL' : |L - (a' * (L + yL) + b)| ≤ eps := by
    have : a * (μ * (L + yL)) = a' * (L + yL) := by rw [ha']; ring
    rw [← this]; exact eL
  have eh' : |(h : ℝ) - (a' * (h + yh) + b)| ≤ eps := by
    have : a * (μ * ((h : ℝ) + yh)) = a' * ((h : ℝ) + yh) := by rw [ha']; ring
    rw [← this]; exact eh
  have hyLabs : |yL| ≤ L / 2 := hend
  rcases abs_le.mp e0 with ⟨e0l, e0u⟩
  rcases abs_le.mp eL' with ⟨eLl, eLu⟩
  rcases abs_le.mp eh' with ⟨ehl, ehu⟩
  rcases abs_le.mp hyLabs with ⟨yLl, yLu⟩
  -- the fitted normalized slope is at least one third
  have hslope : L - 2 * eps ≤ a' * (L + yL) := by linarith
  have hLpos' : 0 < L := by
    rw [hLh]; have : (0 : ℝ) < h := by exact_mod_cast hh
    linarith
  have ha'pos : 1 / 3 ≤ a' := by
    by_contra hneg
    have hneg : a' < 1 / 3 := not_le.mp hneg
    have hLy : 0 < L + yL := by linarith
    have : a' * (L + yL) < (1 / 3) * (L + yL) := by
      exact mul_lt_mul_of_pos_right hneg hLy
    nlinarith
  -- second difference of the error function
  have hsd : |a' * (yL - 2 * yh)| ≤ 4 * eps := by
    rw [abs_le]
    constructor <;> nlinarith
  have hfac : |a'| * |yL - 2 * yh| ≤ 4 * eps := by rwa [← abs_mul]
  have ha'abs : |a'| = a' := abs_of_pos (by linarith)
  rw [ha'abs] at hfac
  have hmain : |yL - 2 * yh| ≤ 12 * eps := by
    by_contra hneg
    have hneg : 12 * eps < |yL - 2 * yh| := not_le.mp hneg
    have : 4 * eps < a' * |yL - 2 * yh| := by nlinarith [abs_nonneg (yL - 2 * yh)]
    linarith
  simpa [hyL, hyh] using hmain

/-! ## The ALG-OPT segment length on an infinite key sequence -/

open Classical in
/-- Number of keys in the first ALG-OPT segment of `p`: the longest feasible
    prefix.  It is `⊤` when every prefix is feasible. -/
noncomputable def segLen (eps : ℝ) (p : ℕ → ℝ) : ℕ∞ :=
  if h : ∃ len, ¬ prefixAffineFeasible eps p len then ((Nat.find h - 1 : ℕ) : ℕ∞) else ⊤

/-- The defining property: the segment has more than `t` keys exactly when the
    first `t + 1` keys are feasible. -/
theorem lt_segLen_iff {eps : ℝ} {p : ℕ → ℝ} (t : ℕ) :
    (t : ℕ∞) < segLen eps p ↔ prefixAffineFeasible eps p (t + 1) := by
  classical
  unfold segLen
  split_ifs with h
  · have hf0 : Nat.find h ≠ 0 := by
      intro h0
      have := Nat.find_spec h
      rw [h0] at this
      exact this (prefixAffineFeasible_zero eps p)
    rw [Nat.cast_lt]
    constructor
    · intro ht
      have hlt : t + 1 < Nat.find h := by omega
      exact not_not.mp (Nat.find_min h hlt)
    · intro hfeas
      by_contra hle
      have hle' : Nat.find h ≤ t + 1 := by omega
      exact Nat.find_spec h (prefixAffineFeasible_mono hfeas hle')
  · push Not at h
    simp only [ENat.natCast_lt_top, true_iff]
    exact h (t + 1)

theorem segLen_le_iff {eps : ℝ} {p : ℕ → ℝ} (t : ℕ) :
    segLen eps p ≤ (t : ℕ∞) ↔ ¬ prefixAffineFeasible eps p (t + 1) := by
  rw [← not_lt, lt_segLen_iff]

theorem segLen_eq_top_iff {eps : ℝ} {p : ℕ → ℝ} :
    segLen eps p = ⊤ ↔ ∀ len, prefixAffineFeasible eps p len := by
  constructor
  · intro h len
    cases len with
    | zero => exact prefixAffineFeasible_zero eps p
    | succ t => exact (lt_segLen_iff t).1 (by rw [h]; exact ENat.natCast_lt_top t)
  · intro h
    rw [ENat.eq_top_iff_forall_gt]
    intro t
    exact (lt_segLen_iff t).2 (h (t + 1))

/-- The segment length only depends on the keys it inspects. -/
theorem lt_segLen_congr {eps : ℝ} {p p' : ℕ → ℝ} {t : ℕ}
    (hpp : ∀ i ≤ t, p i = p' i) :
    (t : ℕ∞) < segLen eps p ↔ (t : ℕ∞) < segLen eps p' := by
  rw [lt_segLen_iff, lt_segLen_iff]
  exact prefixAffineFeasible_congr (fun i hi => hpp i (by omega))

/-- Two extended naturals agree when the same naturals lie below them. -/
theorem ENat.eq_of_forall_natCast_lt_iff {a b : ℕ∞}
    (h : ∀ t : ℕ, (t : ℕ∞) < a ↔ (t : ℕ∞) < b) : a = b := by
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe m => exact absurd ((h m).1 (ENat.natCast_lt_top m)) (lt_irrefl _)
  | coe k =>
    induction b using ENat.recTopCoe with
    | top => exact absurd ((h k).2 (ENat.natCast_lt_top k)) (lt_irrefl _)
    | coe m =>
      congr 1
      apply le_antisymm
      · by_contra hlt
        have hmk : m < k := not_le.mp hlt
        have := (h m).1 (by exact_mod_cast hmk)
        exact lt_irrefl _ (by exact_mod_cast this)
      · by_contra hlt
        have hkm : k < m := not_le.mp hlt
        have := (h k).2 (by exact_mod_cast hkm)
        exact lt_irrefl _ (by exact_mod_cast this)

/-- Affine invariance of the segment length. -/
theorem segLen_affine {eps : ℝ} {p : ℕ → ℝ} {s c : ℝ} (hs : s ≠ 0) :
    segLen eps (fun i => s * p i + c) = segLen eps p := by
  apply ENat.eq_of_forall_natCast_lt_iff
  intro t
  rw [lt_segLen_iff, lt_segLen_iff]
  exact prefixAffineFeasible_affine_iff hs

/-- Every ALG-OPT segment contains at least `q = floor(2 eps) + 1` keys. -/
theorem constantLine_le_segLen {eps : ℝ} (C : ConstantLineLengthCertificate eps)
    (p : ℕ → ℝ) : (C.q : ℕ∞) ≤ segLen eps p := by
  rcases Nat.eq_zero_or_pos C.q with h0 | hpos
  · simp [h0]
  · have : ((C.q - 1 : ℕ) : ℕ∞) < segLen eps p := by
      rw [lt_segLen_iff]
      exact prefixAffineFeasible_constantLine C (by omega)
    have h' := (ENat.add_one_le_iff (ENat.natCast_ne_top _)).2 this
    have hq : ((C.q - 1 : ℕ) : ℕ∞) + 1 = (C.q : ℕ∞) := by
      have : C.q - 1 + 1 = C.q := Nat.sub_add_cancel hpos
      exact_mod_cast this
    rwa [hq] at h'

/-! ## Measurability of prefix feasibility -/

/-- A bounded sequence of lines whose errors approach `eps` yields an exact
    `eps`-line (compactness). -/
theorem prefixAffineFeasible_of_approx {eps : ℝ} {p : ℕ → ℝ} {len : ℕ}
    (z : ℕ → ℝ × ℝ) (R : ℝ) (hR : ∀ m, ‖z m‖ ≤ R)
    (happrox : ∀ m, ∀ i < len,
      |(i : ℝ) - ((z m).1 * p i + (z m).2)| < eps + 1 / ((m : ℝ) + 1)) :
    prefixAffineFeasible eps p len := by
  obtain ⟨w, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := R))
      (x := z) (fun m => by simpa using hR m)
  refine ⟨w.1, w.2, fun i hi => ?_⟩
  have hcont : Continuous fun v : ℝ × ℝ => |(i : ℝ) - (v.1 * p i + v.2)| := by
    fun_prop
  have h1 : Tendsto (fun m => |(i : ℝ) - ((z (φ m)).1 * p i + (z (φ m)).2)|) atTop
      (𝓝 |(i : ℝ) - (w.1 * p i + w.2)|) :=
    (hcont.tendsto w).comp hlim
  have hinv : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun m => eps + 1 / ((φ m : ℝ) + 1)) atTop (𝓝 (eps + 0)) :=
    tendsto_const_nhds.add (hinv.comp hφ.tendsto_atTop)
  rw [add_zero] at h2
  exact le_of_tendsto_of_tendsto' h1 h2 (fun m => (happrox (φ m) i hi).le)

/-- Rational characterization of feasibility; it makes the predicate measurable. -/
theorem prefixAffineFeasible_iff_rat {eps : ℝ} {p : ℕ → ℝ} {len : ℕ} :
    prefixAffineFeasible eps p len ↔
      ∀ m : ℕ, ∃ a b : ℚ, ∀ i < len,
        |(i : ℝ) - ((a : ℝ) * p i + b)| < eps + 1 / ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨a, b, hab⟩ m
    set δ : ℝ := 1 / ((m : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set K : ℝ := ∑ i ∈ Finset.range len, |p i| + 1 with hK
    have hKpos : 0 < K := by
      have : 0 ≤ ∑ i ∈ Finset.range len, |p i| :=
        Finset.sum_nonneg (fun i _ => abs_nonneg _)
      linarith
    have hpK : ∀ i < len, |p i| ≤ K := by
      intro i hi
      have : |p i| ≤ ∑ j ∈ Finset.range len, |p j| :=
        Finset.single_le_sum (f := fun j => |p j|) (fun j _ => abs_nonneg _)
          (Finset.mem_range.2 hi)
      linarith
    obtain ⟨a', ha'l, ha'u⟩ := exists_rat_btwn (show a - δ / (2 * K) < a + δ / (2 * K) by
      have : 0 < δ / (2 * K) := by positivity
      linarith)
    obtain ⟨b', hb'l, hb'u⟩ := exists_rat_btwn (show b - δ / 2 < b + δ / 2 by linarith)
    refine ⟨a', b', fun i hi => ?_⟩
    have hai : |((a' : ℝ) - a) * p i| ≤ δ / 2 := by
      rw [abs_mul]
      have h1 : |(a' : ℝ) - a| ≤ δ / (2 * K) := by
        rw [abs_le]; constructor <;> linarith
      calc |(a' : ℝ) - a| * |p i| ≤ δ / (2 * K) * K :=
            mul_le_mul h1 (hpK i hi) (abs_nonneg _) (by positivity)
        _ = δ / 2 := by field_simp
    have hbi : |(b' : ℝ) - b| < δ / 2 := by
      rw [abs_lt]; constructor <;> linarith
    have hsplit : (i : ℝ) - ((a' : ℝ) * p i + b') =
        ((i : ℝ) - (a * p i + b)) - ((a' : ℝ) - a) * p i - ((b' : ℝ) - b) := by ring
    rw [hsplit]
    calc |((i : ℝ) - (a * p i + b)) - ((a' : ℝ) - a) * p i - ((b' : ℝ) - b)|
        ≤ |(i : ℝ) - (a * p i + b)| + |((a' : ℝ) - a) * p i| + |(b' : ℝ) - b| := by
          have := abs_sub (((i : ℝ) - (a * p i + b)) - ((a' : ℝ) - a) * p i) ((b' : ℝ) - b)
          have := abs_sub ((i : ℝ) - (a * p i + b)) (((a' : ℝ) - a) * p i)
          linarith
      _ < eps + δ := by linarith [hab i hi]
  · intro h
    rcases Nat.eq_zero_or_pos len with h0 | hlen
    · subst h0; exact prefixAffineFeasible_zero eps p
    choose a b hab using h
    have h0 : ∀ m, |(a m : ℝ) * p 0 + b m| < eps + 1 := by
      intro m
      have := hab m 0 hlen
      have hle : 1 / ((m : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      rw [Nat.cast_zero, zero_sub, abs_neg] at this
      linarith
    by_cases hdist : ∃ j < len, p j ≠ p 0
    · obtain ⟨j, hj, hpj⟩ := hdist
      have hd : 0 < |p j - p 0| := abs_pos.2 (sub_ne_zero.2 hpj)
      set A : ℝ := ((j : ℝ) + 2 * (eps + 1)) / |p j - p 0| with hA
      have hja : ∀ m, |(a m : ℝ)| ≤ A := by
        intro m
        have hjm := hab m j hj
        have hle : 1 / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        have hjm' : |(j : ℝ) - ((a m : ℝ) * p j + b m)| < eps + 1 := by linarith
        have hdiff : |(a m : ℝ) * (p j - p 0)| ≤ (j : ℝ) + 2 * (eps + 1) := by
          have hid : (a m : ℝ) * (p j - p 0) =
              (j : ℝ) - ((j : ℝ) - ((a m : ℝ) * p j + b m)) - ((a m : ℝ) * p 0 + b m) := by
            ring
          rw [hid]
          have := h0 m
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          calc |(j : ℝ) - ((j : ℝ) - ((a m : ℝ) * p j + b m)) - ((a m : ℝ) * p 0 + b m)|
              ≤ |(j : ℝ)| + |(j : ℝ) - ((a m : ℝ) * p j + b m)| +
                  |(a m : ℝ) * p 0 + b m| := by
                have := abs_sub ((j : ℝ) - ((j : ℝ) - ((a m : ℝ) * p j + b m)))
                  ((a m : ℝ) * p 0 + b m)
                have := abs_sub (j : ℝ) ((j : ℝ) - ((a m : ℝ) * p j + b m))
                linarith
            _ ≤ (j : ℝ) + 2 * (eps + 1) := by
                rw [abs_of_nonneg hj0]; linarith
        rw [abs_mul] at hdiff
        rw [hA, le_div_iff₀ hd]
        exact hdiff
      refine prefixAffineFeasible_of_approx (fun m => ((a m : ℝ), (b m : ℝ)))
        (max A (eps + 1 + A * |p 0|)) (fun m => ?_) (fun m i hi => hab m i hi)
      rw [Prod.norm_def]
      apply max_le_max (by simpa [Real.norm_eq_abs] using hja m)
      rw [Real.norm_eq_abs]
      have hb : (b m : ℝ) = ((a m : ℝ) * p 0 + b m) - (a m : ℝ) * p 0 := by ring
      rw [hb]
      calc |((a m : ℝ) * p 0 + b m) - (a m : ℝ) * p 0|
          ≤ |(a m : ℝ) * p 0 + b m| + |(a m : ℝ) * p 0| := abs_sub _ _
        _ ≤ eps + 1 + A * |p 0| := by
            rw [abs_mul]
            have := h0 m
            have := mul_le_mul_of_nonneg_right (hja m) (abs_nonneg (p 0))
            linarith
    · push Not at hdist
      refine prefixAffineFeasible_of_approx (fun m => (0, (a m : ℝ) * p 0 + b m))
        (eps + 1) (fun m => ?_) (fun m i hi => ?_)
      · rw [Prod.norm_def]
        simp only [norm_zero, Real.norm_eq_abs]
        exact max_le (by linarith [abs_nonneg ((a m : ℝ) * p 0 + b m), h0 m]) (h0 m).le
      · have := hab m i hi
        simp only [zero_mul, zero_add]
        rwa [hdist i hi] at this

theorem measurableSet_prefixAffineFeasible (eps : ℝ) (len : ℕ) :
    MeasurableSet {p : ℕ → ℝ | prefixAffineFeasible eps p len} := by
  have : {p : ℕ → ℝ | prefixAffineFeasible eps p len} =
      ⋂ m : ℕ, ⋃ a : ℚ, ⋃ b : ℚ, ⋂ i ∈ Finset.range len,
        {p : ℕ → ℝ | |(i : ℝ) - ((a : ℝ) * p i + b)| < eps + 1 / ((m : ℝ) + 1)} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_iUnion, Finset.mem_range]
    exact prefixAffineFeasible_iff_rat
  rw [this]
  refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun a =>
    MeasurableSet.iUnion fun b => MeasurableSet.biInter (Finset.range len).countable_toSet
      fun i _ => ?_
  exact measurableSet_lt (by fun_prop) measurable_const

end PGM
