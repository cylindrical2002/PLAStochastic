import PLAStochastic.Index.Algorithm.EndpointHierarchyBounds
import PLAStochastic.Index.Algorithm.RankHierarchy
import PLAStochastic.Index.Algorithm.MeasurableEndpointHeight
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The top of the endpoint hierarchy: `q`-contraction and Jensen

Let `q = ⌊2 eps⌋ + 1`.  The constant line certifies that any `q` consecutive keys
are `eps`-feasible, so every ALG-OPT segment of a finite key list except the last
one has at least `q` keys, and ALG-OPT uses at most `⌈K/q⌉` segments on `K` keys.
Hence the ALG-PGM layer sizes contract, `K_{ℓ+j} ≤ ⌈K_ℓ/q^j⌉`, and from any layer
`ℓ` the run reaches a single key within `⌊log_q K_ℓ⌋ + 1` further layers:
`H ≤ ℓ + log K_ℓ / log q + 1`.  Jensen's inequality for the concave `log` on
`[1, ∞)` turns this into `E H ≤ ℓ + log (E K_ℓ) / log q + 1` for random keys.
-/

namespace PGM

noncomputable section

open Classical Finset MeasureTheory

/-! ## Non-final segments have at least `q` keys -/

/-- Every ALG-OPT segment of an infinite key sequence has at least `⌊2 eps⌋ + 1` keys. -/
theorem floor_add_one_le_segLen {eps : ℝ} (heps : 0 ≤ eps) (P : ℕ → ℝ) :
    ((⌊2 * eps⌋₊ + 1 : ℕ) : ℕ∞) ≤ segLen eps P :=
  constantLine_le_segLen (ConstantLineLengthCertificate.of_nonneg heps) P

/-- A finite segment has at least `q = ⌊2 eps⌋ + 1` keys unless the list ends first. -/
theorem min_floor_add_one_le_finSegLen {eps : ℝ} (heps : 0 ≤ eps) (P : ℕ → ℝ) (K a : ℕ) :
    min (⌊2 * eps⌋₊ + 1) (K - a) ≤ finSegLen eps P K a := by
  have h := finSegLen_eq_min eps P K a
  have hq := floor_add_one_le_segLen heps (shiftSeq P a)
  have hle : ((min (⌊2 * eps⌋₊ + 1) (K - a) : ℕ) : ℕ∞) ≤
      min (segLen eps (shiftSeq P a)) ((K - a : ℕ) : ℕ∞) := by
    refine le_min (le_trans ?_ hq) (by exact_mod_cast min_le_right _ (K - a))
    exact_mod_cast min_le_left _ (K - a)
  rw [← h] at hle
  exact_mod_cast hle

/-- **Non-final segments.**  If segment `j + 1` still starts inside the list, segment `j`
    has at least `q = ⌊2 eps⌋ + 1` keys. -/
theorem floor_add_one_le_finSegLen_of_lt {eps : ℝ} (heps : 0 ≤ eps) (P : ℕ → ℝ) {K j : ℕ}
    (hj : finCut eps P K (j + 1) < K) :
    ⌊2 * eps⌋₊ + 1 ≤ finSegLen eps P K (finCut eps P K j) := by
  have h := min_floor_add_one_le_finSegLen heps P K (finCut eps P K j)
  have hs : finCut eps P K (j + 1) =
      finCut eps P K j + finSegLen eps P K (finCut eps P K j) := rfl
  omega

theorem min_mul_le_finCut {eps : ℝ} (heps : 0 ≤ eps) (P : ℕ → ℝ) (K : ℕ) :
    ∀ j, min ((⌊2 * eps⌋₊ + 1) * j) K ≤ finCut eps P K j
  | 0 => by simp
  | j + 1 => by
    have ih := min_mul_le_finCut heps P K j
    have hle := finCut_le eps P K j
    have hs := min_floor_add_one_le_finSegLen heps P K (finCut eps P K j)
    show min ((⌊2 * eps⌋₊ + 1) * (j + 1)) K ≤
      finCut eps P K j + finSegLen eps P K (finCut eps P K j)
    rw [Nat.mul_succ]
    omega

/-- **Count bound**: ALG-OPT uses at most `⌈K/q⌉` segments on `K` keys, `q = ⌊2 eps⌋ + 1`. -/
theorem finSegCount_le_ceilDiv {eps : ℝ} (heps : 0 ≤ eps) (P : ℕ → ℝ) (K : ℕ) :
    finSegCount eps P K ≤ K ⌈/⌉ (⌊2 * eps⌋₊ + 1) := by
  unfold finSegCount
  rw [Nat.count_eq_card_filter_range]
  calc #{j ∈ range (K + 1) | finCut eps P K j < K}
      ≤ #(range (K ⌈/⌉ (⌊2 * eps⌋₊ + 1))) := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_range, lt_ceilDiv_iff_mul_lt (Nat.le_add_left 1 _), Nat.mul_comm]
        have := min_mul_le_finCut heps P K j
        omega
    _ = K ⌈/⌉ (⌊2 * eps⌋₊ + 1) := Finset.card_range _

/-! ## Layer contraction -/

theorem ceilDiv_le_ceilDiv_of_le {a a' c : ℕ} (hc : 0 < c) (h : a ≤ a') :
    a ⌈/⌉ c ≤ a' ⌈/⌉ c :=
  (ceilDiv_le_iff_le_mul hc).2 (h.trans (le_smul_ceilDiv hc))

theorem ceilDiv_ceilDiv_le (a : ℕ) {b c : ℕ} (hb : 0 < b) (hc : 0 < c) :
    a ⌈/⌉ b ⌈/⌉ c ≤ a ⌈/⌉ (b * c) := by
  apply (ceilDiv_le_iff_le_mul hc).2
  apply (ceilDiv_le_iff_le_mul hb).2
  rw [← Nat.mul_assoc]
  exact le_smul_ceilDiv (Nat.mul_pos hb hc)

/-- One layer of ALG-PGM divides the size by `q = ⌊2 eps⌋ + 1`, rounding up. -/
theorem epLayer_succ_snd_le {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) (n ℓ : ℕ) :
    (epLayer eps p n (ℓ + 1)).2 ≤ (epLayer eps p n ℓ).2 ⌈/⌉ (⌊2 * eps⌋₊ + 1) :=
  finSegCount_le_ceilDiv heps _ _

/-- `j` layers of ALG-PGM divide the size by `q^j`, rounding up. -/
theorem epLayer_add_snd_le {eps : ℝ} (heps : 0 ≤ eps) (p : ℕ → ℝ) (n ℓ : ℕ) :
    ∀ j, (epLayer eps p n (ℓ + j)).2 ≤ (epLayer eps p n ℓ).2 ⌈/⌉ (⌊2 * eps⌋₊ + 1) ^ j
  | 0 => by
    rw [Nat.add_zero, pow_zero]
    simp
  | j + 1 => by
    have hq : 0 < ⌊2 * eps⌋₊ + 1 := Nat.succ_pos _
    calc (epLayer eps p n (ℓ + (j + 1))).2
        ≤ (epLayer eps p n (ℓ + j)).2 ⌈/⌉ (⌊2 * eps⌋₊ + 1) :=
          epLayer_succ_snd_le heps p n (ℓ + j)
      _ ≤ (epLayer eps p n ℓ).2 ⌈/⌉ (⌊2 * eps⌋₊ + 1) ^ j ⌈/⌉ (⌊2 * eps⌋₊ + 1) :=
          ceilDiv_le_ceilDiv_of_le hq (epLayer_add_snd_le heps p n ℓ j)
      _ ≤ (epLayer eps p n ℓ).2 ⌈/⌉ (⌊2 * eps⌋₊ + 1) ^ (j + 1) := by
          rw [pow_succ]
          exact ceilDiv_ceilDiv_le _ (pow_pos hq j) hq

/-! ## Height above a layer -/

/-- For `n ≥ 1` every ALG-PGM layer is nonempty. -/
theorem one_le_epLayer_snd {eps : ℝ} (p : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∀ ℓ, 1 ≤ (epLayer eps p n ℓ).2
  | 0 => hn
  | ℓ + 1 => one_le_finSegCount _ (one_le_epLayer_snd p hn ℓ)

theorem one_lt_floor_add_one {eps : ℝ} (heps : 1 ≤ eps) : 1 < ⌊2 * eps⌋₊ + 1 := by
  have : 1 ≤ ⌊2 * eps⌋₊ := Nat.le_floor (by push_cast; linarith)
  omega

/-- From layer `ℓ`, the run reaches one key within `⌊log_q K_ℓ⌋ + 1` layers. -/
theorem epLayer_add_log_snd_eq_one {eps : ℝ} (heps : 1 ≤ eps) (p : ℕ → ℝ) {n : ℕ}
    (hn : 1 ≤ n) (ℓ : ℕ) :
    (epLayer eps p n
      (ℓ + (Nat.log (⌊2 * eps⌋₊ + 1) (epLayer eps p n ℓ).2 + 1))).2 = 1 := by
  set q := ⌊2 * eps⌋₊ + 1 with hqdef
  set j := Nat.log q (epLayer eps p n ℓ).2 + 1 with hj
  have hq : 1 < q := one_lt_floor_add_one heps
  have hpow : (epLayer eps p n ℓ).2 < q ^ j := Nat.lt_pow_succ_log_self hq _
  have h : (epLayer eps p n (ℓ + j)).2 ≤ (epLayer eps p n ℓ).2 ⌈/⌉ q ^ j :=
    epLayer_add_snd_le (by linarith) p n ℓ j
  have h1 : (epLayer eps p n ℓ).2 ⌈/⌉ q ^ j ≤ 1 :=
    (ceilDiv_le_iff_le_mul (pow_pos (by omega) j)).2 (by rw [Nat.mul_one]; exact hpow.le)
  have h0 := one_le_epLayer_snd (eps := eps) p hn (ℓ + j)
  omega

/-- **Height above a layer**: `H ≤ ℓ + ⌊log_q K_ℓ⌋ + 1` for every layer `ℓ`. -/
theorem epHeight_le_add_log {eps : ℝ} (heps : 1 ≤ eps) (p : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (ℓ : ℕ) :
    epHeight eps p n ≤ ℓ + Nat.log (⌊2 * eps⌋₊ + 1) (epLayer eps p n ℓ).2 + 1 :=
  Nat.sInf_le ⟨by omega, by rw [Nat.add_assoc]; exact epLayer_add_log_snd_eq_one heps p hn ℓ⟩

/-- **Height above a layer**, real form: `H ≤ ℓ + log K_ℓ / log q + 1`. -/
theorem epHeight_le_add_log_real {eps : ℝ} (heps : 1 ≤ eps) (p : ℕ → ℝ) {n : ℕ}
    (hn : 1 ≤ n) (ℓ : ℕ) :
    (epHeight eps p n : ℝ) ≤
      ℓ + Real.log (epLayer eps p n ℓ).2 / Real.log (⌊2 * eps⌋₊ + 1) + 1 := by
  have h : (epHeight eps p n : ℝ) ≤
      ((ℓ + Nat.log (⌊2 * eps⌋₊ + 1) (epLayer eps p n ℓ).2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast epHeight_le_add_log heps p hn ℓ
  have hlog := Real.natLog_le_logb (epLayer eps p n ℓ).2 (⌊2 * eps⌋₊ + 1)
  rw [← Real.log_div_log] at hlog
  push_cast at h hlog
  linarith

/-! ## Jensen's inequality for `log` -/

/-- **Jensen** for the concave `log` on `[1, ∞)`: `E log Y ≤ log E Y` when `Y ≥ 1` a.s. -/
theorem integral_log_le_log_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Integrable Y P) (h1 : ∀ᵐ ω ∂P, 1 ≤ Y ω) :
    ∫ ω, Real.log (Y ω) ∂P ≤ Real.log (∫ ω, Y ω ∂P) := by
  have hconc : ConcaveOn ℝ (Set.Ici (1 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn.subset
      (fun _ hx => Set.mem_Ioi.2 (lt_of_lt_of_le one_pos (Set.mem_Ici.1 hx))) (convex_Ici 1)
  have hcont : ContinuousOn Real.log (Set.Ici (1 : ℝ)) :=
    Real.continuousOn_log.mono fun x hx => (lt_of_lt_of_le one_pos hx).ne'
  have hlog : Integrable (Real.log ∘ Y) P := by
    refine hY.mono' (Real.measurable_log.comp_aemeasurable hY.aemeasurable).aestronglyMeasurable ?_
    filter_upwards [h1] with ω hω
    rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hω)]
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hω)
    linarith
  exact hconc.le_map_integral hcont isClosed_Ici h1 hY hlog

/-- **Jensen** for a random layer size `X ≥ 1`: `E log X ≤ log E X`. -/
theorem integral_log_natCast_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℕ} (hX : Integrable (fun ω => (X ω : ℝ)) P)
    (h1 : ∀ᵐ ω ∂P, 1 ≤ X ω) :
    ∫ ω, Real.log (X ω) ∂P ≤ Real.log (∫ ω, (X ω : ℝ) ∂P) :=
  integral_log_le_log_integral hX (h1.mono fun _ h => by exact_mod_cast h)

/-! ## The expected height -/

/-- With `eps ≥ 1` no layer is larger than the input. -/
theorem epLayer_snd_le {eps : ℝ} (heps : 1 ≤ eps) (p : ℕ → ℝ) (n : ℕ) :
    ∀ ℓ, (epLayer eps p n ℓ).2 ≤ n
  | 0 => le_rfl
  | ℓ + 1 => (finSegCount_le_self heps _ _).trans (epLayer_snd_le heps p n ℓ)

/-- **Expected height above a layer**: for random keys,
    `E H ≤ ℓ + log (E K_ℓ) / log q + 1` with `q = ⌊2 eps⌋ + 1`. -/
theorem integral_epHeight_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {eps : ℝ} (heps : 1 ≤ eps) {keys : Ω → ℕ → ℝ}
    (hkeys : Measurable keys) {n : ℕ} (hn : 1 ≤ n) (ℓ : ℕ) :
    ∫ ω, (epHeight eps (keys ω) n : ℝ) ∂P ≤
      ℓ + Real.log (∫ ω, ((epLayer eps (keys ω) n ℓ).2 : ℝ) ∂P) /
        Real.log (⌊2 * eps⌋₊ + 1) + 1 := by
  set c : ℝ := Real.log (⌊2 * eps⌋₊ + 1) with hc
  have hcpos : 0 < c := by
    have : (1 : ℝ) < ⌊2 * eps⌋₊ + 1 := by exact_mod_cast one_lt_floor_add_one heps
    exact Real.log_pos this
  set S : Ω → ℕ := fun ω => (epLayer eps (keys ω) n ℓ).2 with hSdef
  have hS : Measurable fun ω => ((S ω : ℕ) : ℝ) :=
    measurable_from_nat.comp (measurable_snd.comp ((measurable_epLayer eps n ℓ).comp hkeys))
  have hS1 : ∀ ω, (1 : ℝ) ≤ S ω := fun ω => by
    exact_mod_cast one_le_epLayer_snd (eps := eps) (keys ω) hn ℓ
  have hSn : ∀ ω, (S ω : ℝ) ≤ n := fun ω => by exact_mod_cast epLayer_snd_le heps (keys ω) n ℓ
  have hSint : Integrable (fun ω => (S ω : ℝ)) P :=
    Integrable.of_bound hS.aestronglyMeasurable n (ae_of_all _ fun ω => by
      rw [Real.norm_natCast]; exact hSn ω)
  have hlog : Integrable (fun ω => Real.log (S ω)) P :=
    Integrable.of_bound (Real.measurable_log.comp hS).aestronglyMeasurable (Real.log n)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (hS1 ω))]
        exact Real.log_le_log (by linarith [hS1 ω]) (hSn ω))
  have hdiv : Integrable (fun ω => Real.log (S ω) / c) P := hlog.div_const c
  have hsum : Integrable (fun ω => (ℓ : ℝ) + Real.log (S ω) / c) P :=
    (integrable_const _).add hdiv
  have hgint : Integrable (fun ω => (ℓ : ℝ) + Real.log (S ω) / c + 1) P :=
    hsum.add (integrable_const _)
  have hg : ∫ ω, ((ℓ : ℝ) + Real.log (S ω) / c + 1) ∂P =
      ℓ + (∫ ω, Real.log (S ω) ∂P) / c + 1 := by
    rw [integral_add hsum (integrable_const _), integral_add (integrable_const _) hdiv,
      integral_div, integral_const, integral_const]
    simp
  have hJ := integral_log_natCast_le hSint (ae_of_all _ fun ω =>
    one_le_epLayer_snd (eps := eps) (keys ω) hn ℓ)
  calc ∫ ω, (epHeight eps (keys ω) n : ℝ) ∂P
      ≤ ∫ ω, ((ℓ : ℝ) + Real.log (S ω) / c + 1) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => Nat.cast_nonneg _) hgint
          (ae_of_all _ fun ω => epHeight_le_add_log_real heps (keys ω) hn ℓ)
    _ = ℓ + (∫ ω, Real.log (S ω) ∂P) / c + 1 := hg
    _ ≤ ℓ + Real.log (∫ ω, (S ω : ℝ) ∂P) / c + 1 := by gcongr

end

end PGM
