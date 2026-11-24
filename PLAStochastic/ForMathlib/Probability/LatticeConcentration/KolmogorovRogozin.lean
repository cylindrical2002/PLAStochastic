import PLAStochastic.ForMathlib.Probability.LatticeConcentration.Elementary
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The lattice Kolmogorov–Rogozin inequality

We prove `RogozinLattice CRog` with `CRog = 6`, using the bridge `map_sum_eq_convFin` of
`PLAStochastic.ForMathlib.Probability.LatticeConcentration.Elementary` (the law of a sum of independent integer variables is `convFin` of
the laws).

The proof is combinatorial rather than Fourier-analytic:

* **Pair–sign representation** (`Rogozin.convFin_apply_eq_lintegral`). Draw independent pairs
  `(aᵢ, bᵢ) ∼ μᵢ ⊗ μᵢ` and independent fair coins `εᵢ`; then `∑ᵢ (εᵢ ? aᵢ : bᵢ)` has law
  `convFin m μ`. Hence `convFin m μ W` is the average over the pairs of the coin probability
  of `W`.
* **Littlewood–Offord** (`Rogozin.lo_card`, via Sperner's theorem `IsAntichain.sperner`). For
  fixed pairs, let `R` be the number of indices with `|aᵢ - bᵢ| ≥ δ := ⌈c/2⌉`. The coin
  probability of a window of length `δ` is at most `binom(R, ⌊R/2⌋) / 2^R ≤ R^{-1/2}`, so a
  window of length `w` has coin probability at most `(2w/c + 1) R^{-1/2}`.
* **Counting separated pairs** (`Rogozin.lintegral_pair_bound`). `P(|aᵢ - bᵢ| < δ) ≤ lconc μᵢ c`,
  so with `s = ∑ᵢ (1 - lconc μᵢ c)` the exponential moment gives `E[e^{s/4 - R}] ≤ e^{-s/4}`,
  which controls the event `R < s/4`; on `R ≥ s/4` the Littlewood–Offord bound is `2/√s`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Rogozin

/-! ### Littlewood–Offord -/

/-- Sperner step: subset sums of steps `≥ δ > 0` in a window of length `δ` form an antichain. -/
theorem lo_card_pos {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℤ) (δ : ℤ) (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ d i) (y : ℤ) :
    #(univ.filter (fun T : Finset α => y ≤ ∑ i ∈ T, d i ∧ ∑ i ∈ T, d i < y + δ)) ≤
      (Fintype.card α).choose (Fintype.card α / 2) := by
  apply IsAntichain.sperner
  intro T hT T' hT' hne hsub
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hT hT'
  obtain ⟨j, hj⟩ : (T' \ T).Nonempty := by
    rw [sdiff_nonempty]; intro h; exact hne (subset_antisymm hsub h)
  have h1 : ∑ i ∈ T' \ T, d i + ∑ i ∈ T, d i = ∑ i ∈ T', d i := sum_sdiff hsub
  have h2 : d j ≤ ∑ i ∈ T' \ T, d i :=
    single_le_sum (fun i _ => (hδ.le.trans (hd i))) hj
  have := hd j
  omega

/-- Littlewood–Offord for steps of absolute value `≥ δ`, indexed by sign choices. -/
theorem lo_card_sign {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℤ) (δ : ℤ) (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |d i|) (y : ℤ) :
    #(univ.filter (fun ε : α → Bool => y ≤ ∑ i, (if ε i then d i else 0) ∧
        ∑ i, (if ε i then d i else 0) < y + δ)) ≤
      (Fintype.card α).choose (Fintype.card α / 2) := by
  set K := ∑ i, min (d i) 0 with hK
  let T : (α → Bool) → Finset α := fun ε => univ.filter (fun i => ε i ≠ decide (d i < 0))
  have key : ∀ ε : α → Bool, ∑ i, (if ε i then d i else 0) = ∑ i ∈ T ε, |d i| + K := by
    intro ε
    simp only [T, hK, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    rcases lt_or_ge (d i) 0 with h | h
    · cases ε i <;> simp [h, abs_of_neg h, min_eq_left h.le]
    · cases ε i <;> simp [not_lt.2 h, abs_of_nonneg h, min_eq_right h]
  refine le_trans ?_ (lo_card_pos (fun i => |d i|) δ hδ hd (y - K))
  refine card_le_card_of_injOn T ?_ ?_
  · intro ε hε
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hε ⊢
    rw [key] at hε
    constructor <;> omega
  · intro ε _ ε' _ h
    funext i
    have := congrArg (fun S => i ∈ S) h
    simp only [T, mem_filter, mem_univ, true_and, eq_iff_iff] at this
    clear key
    cases hε : ε i <;> cases hε' : ε' i <;> simp_all <;> omega

/-- Littlewood–Offord with arbitrary steps: only the `r` steps of absolute value `≥ δ` count. -/
theorem lo_card {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℤ) (δ : ℤ) (hδ : 0 < δ)
    (y : ℤ) :
    #(univ.filter (fun ε : ι → Bool => y ≤ ∑ i, (if ε i then d i else 0) ∧
        ∑ i, (if ε i then d i else 0) < y + δ)) ≤
      2 ^ (Fintype.card {i // ¬ δ ≤ |d i|}) *
        (Fintype.card {i // δ ≤ |d i|}).choose (Fintype.card {i // δ ≤ |d i|} / 2) := by
  set p : ι → Prop := fun i => δ ≤ |d i| with hp
  set N := (Fintype.card {i // p i}).choose (Fintype.card {i // p i} / 2) with hN
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => Bool)
  let S₁ : ({i // p i} → Bool) → ℤ := fun ε₁ => ∑ j, (if ε₁ j then d j else 0)
  let S₂ : ({i // ¬ p i} → Bool) → ℤ := fun ε₂ => ∑ j, (if ε₂ j then d j else 0)
  have hsum : ∀ ε₁ ε₂, ∑ i, (if e.symm (ε₁, ε₂) i then d i else 0) = S₁ ε₁ + S₂ ε₂ := by
    intro ε₁ ε₂
    rw [← Fintype.sum_subtype_add_sum_subtype p]
    have h1 : ∀ j : {i // p i}, e.symm (ε₁, ε₂) j = ε₁ j := fun j => by
      simp [e, Equiv.piEquivPiSubtypeProd, j.2]
    have h2 : ∀ j : {i // ¬ p i}, e.symm (ε₁, ε₂) j = ε₂ j := fun j => by
      simp [e, Equiv.piEquivPiSubtypeProd, j.2]
    simp only [S₁, S₂, h1, h2]
  rw [card_filter, ← e.symm.sum_comp, Fintype.sum_prod_type_right]
  have inner : ∀ ε₂, (∑ ε₁, if y ≤ ∑ i, (if e.symm (ε₁, ε₂) i then d i else 0) ∧
      ∑ i, (if e.symm (ε₁, ε₂) i then d i else 0) < y + δ then 1 else 0) ≤ N := by
    intro ε₂
    have h := lo_card_sign (fun j : {i // p i} => d j) δ hδ (fun j => j.2) (y - S₂ ε₂)
    rw [card_filter] at h
    refine le_trans (le_of_eq ?_) h
    refine sum_congr rfl (fun ε₁ _ => ?_)
    rw [hsum]
    congr 1
    apply propext
    simp only [S₁]
    constructor <;> intro h <;> constructor <;> omega
  calc _ ≤ ∑ _ε₂ : {i // ¬ p i} → Bool, N := sum_le_sum (fun ε₂ _ => inner ε₂)
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, smul_eq_mul]

/-- Covering a window of length `n δ` by `n` windows of length `δ`. -/
theorem card_window_le {β : Type*} [Fintype β] [DecidableEq β] (τ : β → ℤ) (δ : ℤ) (B : ℕ)
    (hB : ∀ y, #(univ.filter (fun b => y ≤ τ b ∧ τ b < y + δ)) ≤ B) :
    ∀ (n : ℕ) (y : ℤ), #(univ.filter (fun b => y ≤ τ b ∧ τ b < y + n * δ)) ≤ n * B
  | 0, y => by
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [card_eq_zero.2]
    rw [filter_eq_empty_iff]
    intro b _ h
    omega
  | n + 1, y => by
    calc _ ≤ #(univ.filter (fun b => y ≤ τ b ∧ τ b < y + n * δ) ∪
          univ.filter (fun b => y + n * δ ≤ τ b ∧ τ b < y + n * δ + δ)) := by
          apply card_le_card
          intro b hb
          simp only [mem_filter, mem_univ, true_and, mem_union] at hb ⊢
          push_cast at hb
          by_cases h : τ b < y + n * δ
          · left; exact ⟨hb.1, h⟩
          · right; constructor <;> linarith [hb.2]
      _ ≤ n * B + B := (card_union_le _ _).trans
          (Nat.add_le_add (card_window_le τ δ B hB n y) (hB _))
      _ = (n + 1) * B := by ring

/-- `binom(2n, n)² (2n+1) ≤ 16ⁿ`. -/
theorem centralBinom_sq_le (n : ℕ) : n.centralBinom ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have key : ((n + 1) * (n + 1).centralBinom) ^ 2 * (2 * (n + 1) + 1) ≤
        (n + 1) ^ 2 * 16 ^ (n + 1) := by
      rw [h]
      have : (2 * (2 * n + 1) * n.centralBinom) ^ 2 * (2 * (n + 1) + 1) =
          (4 * (2 * n + 1) * (2 * n + 3)) * (n.centralBinom ^ 2 * (2 * n + 1)) := by ring
      rw [this, pow_succ]
      calc _ ≤ (4 * (2 * n + 1) * (2 * n + 3)) * 16 ^ n := Nat.mul_le_mul_left _ ih
        _ ≤ (n + 1) ^ 2 * (16 ^ n * 16) := by
          rw [show (n + 1) ^ 2 * (16 ^ n * 16) = (16 * (n + 1) ^ 2) * 16 ^ n by ring]
          apply Nat.mul_le_mul_right
          nlinarith
    have hpos : 0 < (n + 1) ^ 2 := by positivity
    rw [mul_pow, mul_assoc] at key
    exact Nat.le_of_mul_le_mul_left key hpos

/-- `binom(R, ⌊R/2⌋)² R ≤ 4^R`. -/
theorem choose_half_sq_le (R : ℕ) : (R.choose (R / 2)) ^ 2 * R ≤ 4 ^ R := by
  rcases Nat.even_or_odd' R with ⟨n, rfl | rfl⟩
  · have h := centralBinom_sq_le n
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    rw [show 2 * n / 2 = n by omega, pow_mul, show (4 : ℕ) ^ 2 = 16 by norm_num]
    exact le_trans (Nat.mul_le_mul_left _ (by omega)) h
  · have h := centralBinom_sq_le (n + 1)
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Nat.choose_succ_succ, Nat.choose_symm_half] at h
    rw [show (2 * n + 1) / 2 = n by omega]
    have e16 : (16 : ℕ) ^ (n + 1) = 4 * 4 ^ (2 * n + 1) := by
      rw [pow_succ, pow_succ, pow_mul]; norm_num; ring
    rw [e16, show (2 * n + 1).choose n + (2 * n + 1).choose n = 2 * (2 * n + 1).choose n by ring,
      mul_pow] at h
    generalize (2 * n + 1).choose n ^ 2 = X at h ⊢
    generalize (4 : ℕ) ^ (2 * n + 1) = Y at h ⊢
    nlinarith

/-! ### Concentration function: elementary bounds -/

theorem lconc_le_one (ν : Measure ℤ) [IsProbabilityMeasure ν] (c : ℕ) : lconc ν c ≤ 1 :=
  ciSup_le fun _ => ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

/-! ### The pair–sign representation -/

/-- The fair coin on `Bool`. -/
def coin : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

theorem coin_singleton (t : Bool) : coin {t} = 2⁻¹ := by
  cases t <;> simp [coin]

instance : IsProbabilityMeasure coin := by
  constructor
  simp only [coin, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- Select the first or the second coordinate of a pair according to a coin. -/
def sel (q : (ℤ × ℤ) × Bool) : ℤ := if q.2 then q.1.1 else q.1.2

theorem map_sel (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ((ν.prod ν).prod coin).map sel = ν := by
  ext S hS
  rw [Measure.map_apply Measurable.of_discrete hS, Measure.prod_apply_symm .of_discrete]
  simp only [coin, lintegral_smul_measure, lintegral_add_measure]
  rw [lintegral_dirac, lintegral_dirac]
  have h1 : (fun x => (x, true)) ⁻¹' (sel ⁻¹' S) = S ×ˢ (Set.univ : Set ℤ) := by
    ext x; simp [sel]
  have h2 : (fun x => (x, false)) ⁻¹' (sel ⁻¹' S) = (Set.univ : Set ℤ) ×ˢ S := by
    ext x; simp [sel]
  rw [h1, h2, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, one_mul, ← two_mul,
    smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- Pair–sign representation: `convFin` is a mixture, over independent pairs `(aᵢ, bᵢ) ∼ μᵢ ⊗ μᵢ`,
of the laws of `∑ᵢ (aᵢ or bᵢ)` with independent fair choices. -/
theorem convFin_apply_eq_lintegral (m : ℕ) (μ : Fin m → Measure ℤ)
    [∀ i, IsProbabilityMeasure (μ i)] (W : Set ℤ) :
    convFin m μ W = ∫⁻ p, (Measure.pi fun _ : Fin m => coin)
        {ε | (∑ i, if ε i then (p i).1 else (p i).2) ∈ W}
        ∂(Measure.pi fun i => (μ i).prod (μ i)) := by
  set P' := Measure.pi fun i => ((μ i).prod (μ i)).prod coin
  have hind : iIndepFun (fun i (ω : Fin m → (ℤ × ℤ) × Bool) => sel (ω i)) P' :=
    iIndepFun_pi (X := fun _ => sel) (fun _ => Measurable.of_discrete.aemeasurable)
  have hlaw : ∀ i, P'.map (fun ω => sel (ω i)) = μ i := by
    intro i
    calc P'.map (fun ω => sel (ω i)) = (P'.map (Function.eval i)).map sel :=
          (Measure.map_map (μ := P') (g := sel) (f := Function.eval i) Measurable.of_discrete
            (measurable_pi_apply i)).symm
      _ = (((μ i).prod (μ i)).prod coin).map sel := by rw [(measurePreserving_eval _ i).map_eq]
      _ = μ i := map_sel _
  have hbr := map_sum_eq_convFin m (fun i (ω : Fin m → (ℤ × ℤ) × Bool) => sel (ω i))
    (fun _ => Measurable.of_discrete) hind
  simp only [hlaw] at hbr
  rw [← hbr, Measure.map_apply Measurable.of_discrete .of_discrete]
  have hmp := measurePreserving_arrowProdEquivProdArrow (ℤ × ℤ) Bool (Fin m)
    (fun i => (μ i).prod (μ i)) (fun _ => coin)
  set E : Set ((Fin m → ℤ × ℤ) × (Fin m → Bool)) :=
    {q | (∑ i, if q.2 i then (q.1 i).1 else (q.1 i).2) ∈ W}
  have hE : (fun ω => ∑ i, sel (ω i)) ⁻¹' W =
      (MeasurableEquiv.arrowProdEquivProdArrow (ℤ × ℤ) Bool (Fin m)) ⁻¹' E := rfl
  rw [hE, hmp.measure_preimage MeasurableSet.of_discrete.nullMeasurableSet,
    Measure.prod_apply .of_discrete]
  rfl

theorem pi_coin_apply (m : ℕ) (P : (Fin m → Bool) → Prop) [DecidablePred P] :
    (Measure.pi fun _ : Fin m => coin) {ε | P ε} = #(univ.filter P) * (2⁻¹ : ℝ≥0∞) ^ m := by
  calc _ = (Measure.pi fun _ : Fin m => coin) ↑(univ.filter P) := by congr 1; ext; simp
    _ = ∑ ε ∈ univ.filter P, (Measure.pi fun _ : Fin m => coin) {ε} :=
        (sum_measure_singleton ..).symm
    _ = _ := by simp [Measure.pi_singleton, coin_singleton, sum_const]

/-- Littlewood–Offord bound for the coin measure with fixed pairs `p`. -/
theorem pi_coin_window_le (m : ℕ) (p : Fin m → ℤ × ℤ) (δ : ℤ) (hδ : 0 < δ) (x : ℤ) (n w : ℕ)
    (hw : (w : ℤ) ≤ n * δ) :
    ((Measure.pi fun _ : Fin m => coin)
        {ε | (∑ i, if ε i then (p i).1 else (p i).2) ∈ Set.Ico x (x + w)}).toReal ≤
      n * ((Fintype.card {i // δ ≤ |(p i).1 - (p i).2|}).choose
        (Fintype.card {i // δ ≤ |(p i).1 - (p i).2|} / 2) : ℝ) /
        2 ^ (Fintype.card {i // δ ≤ |(p i).1 - (p i).2|}) := by
  set d : Fin m → ℤ := fun i => (p i).1 - (p i).2 with hd
  set B := ∑ i, (p i).2 with hB
  set R := Fintype.card {i // δ ≤ |d i|} with hR
  set R' := Fintype.card {i // ¬ δ ≤ |d i|} with hR'
  have hRR : R' + R = m := by
    have h1 := Fintype.card_subtype_compl (fun i => δ ≤ |d i|)
    have h2 := Fintype.card_subtype_le (fun i => δ ≤ |d i|)
    simp only [Fintype.card_fin] at h1 h2
    omega
  let τ : (Fin m → Bool) → ℤ := fun ε => ∑ i, (if ε i then d i else 0)
  have hστ : ∀ ε : Fin m → Bool, (∑ i, if ε i then (p i).1 else (p i).2) = B + τ ε := by
    intro ε
    simp only [hB, τ, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    cases ε i <;> simp [hd]
  have hcard : #(univ.filter (fun ε : Fin m → Bool =>
      (∑ i, if ε i then (p i).1 else (p i).2) ∈ Set.Ico x (x + w))) ≤
      n * (2 ^ R' * R.choose (R / 2)) := by
    refine le_trans (card_le_card ?_) (card_window_le τ δ _ (lo_card d δ hδ) n (x - B))
    intro ε
    simp only [mem_filter, mem_univ, true_and, Set.mem_Ico, hστ]
    intro h
    constructor <;> linarith [h.1, h.2]
  rw [show {ε : Fin m → Bool | (∑ i, if ε i then (p i).1 else (p i).2) ∈ Set.Ico x (x + w)} =
    {ε | (fun ε : Fin m → Bool => (∑ i, if ε i then (p i).1 else (p i).2) ∈ Set.Ico x (x + w)) ε}
    from rfl, pi_coin_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  have hF : (#(univ.filter (fun ε : Fin m → Bool =>
      (∑ i, if ε i then (p i).1 else (p i).2) ∈ Set.Ico x (x + w))) : ℝ) ≤
      n * (2 ^ R' * R.choose (R / 2)) := by exact_mod_cast hcard
  have h2m : (2⁻¹ : ℝ) ^ m = ((2 : ℝ) ^ R' * 2 ^ R)⁻¹ := by rw [← pow_add, hRR, inv_pow]
  rw [h2m]
  calc _ ≤ (n * (2 ^ R' * R.choose (R / 2)) : ℝ) * ((2 : ℝ) ^ R' * 2 ^ R)⁻¹ := by gcongr
    _ = _ := by field_simp

/-! ### Real-variable estimates -/

/-- `binom(R, ⌊R/2⌋) / 2^R ≤ 1/√R`. -/
theorem choose_half_div_le (R : ℕ) (hR : 1 ≤ R) :
    (R.choose (R / 2) : ℝ) / 2 ^ R ≤ 1 / Real.sqrt R := by
  have h := choose_half_sq_le R
  have hR' : (0 : ℝ) < Real.sqrt R := Real.sqrt_pos.2 (by exact_mod_cast hR)
  have key : (R.choose (R / 2) : ℝ) * Real.sqrt R ≤ 2 ^ R := by
    have h' : ((R.choose (R / 2) : ℝ) * Real.sqrt R) ^ 2 ≤ ((2 : ℝ) ^ R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, mul_comm R 2, pow_mul]
      norm_num
      exact_mod_cast h
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h'
  rw [div_le_div_iff₀ (by positivity) hR']
  linarith

theorem window_real_bound (v A s : ℝ) (n R : ℕ) (hv1 : v ≤ 1)
    (hv : v ≤ n * (R.choose (R / 2) : ℝ) / 2 ^ R) (hA : 1 ≤ A) (hn : (n : ℝ) ≤ A)
    (hs : 0 < s) :
    v ≤ A * Real.exp (s / 4) * Real.exp (-1) ^ R + 2 * A / Real.sqrt s := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have h2 : 0 ≤ 2 * A / Real.sqrt s := by positivity
  have h1 : 0 ≤ A * Real.exp (s / 4) * Real.exp (-1) ^ R := by positivity
  rcases lt_or_ge (R : ℝ) (s / 4) with h | h
  · have : 1 ≤ Real.exp (s / 4) * Real.exp (-1) ^ R := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    nlinarith
  · have hR : 1 ≤ R := by
      have : (0 : ℝ) < R := by linarith
      exact_mod_cast this
    have hc := choose_half_div_le R hR
    have hRpos : (0 : ℝ) < Real.sqrt R := Real.sqrt_pos.2 (by exact_mod_cast hR)
    have hv' : v ≤ A * (1 / Real.sqrt R) := by
      calc v ≤ n * ((R.choose (R / 2) : ℝ) / 2 ^ R) := by rw [← mul_div_assoc]; exact hv
        _ ≤ A * (1 / Real.sqrt R) := by gcongr
    have hsR : 1 / Real.sqrt R ≤ 2 / Real.sqrt s := by
      rw [div_le_div_iff₀ hRpos hsq]
      have h4 : Real.sqrt s ≤ Real.sqrt (4 * R) := Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h4
      linarith
    calc v ≤ A * (1 / Real.sqrt R) := hv'
      _ ≤ A * (2 / Real.sqrt s) := by gcongr
      _ = 2 * A / Real.sqrt s := by ring
      _ ≤ _ := by linarith

/-- The weight `e^{-1}` on pairs separated by at least `δ`, and `1` otherwise. -/
def sepWeight (δ : ℤ) (x : ℤ × ℤ) : ℝ := if δ ≤ |x.1 - x.2| then Real.exp (-1) else 1

theorem sepWeight_nonneg (δ : ℤ) (x : ℤ × ℤ) : 0 ≤ sepWeight δ x := by
  unfold sepWeight; split_ifs <;> positivity

theorem lintegral_sepWeight_le (ν : Measure ℤ) [IsProbabilityMeasure ν] (c : ℕ) (δ : ℤ)
    (hδc : 2 * δ ≤ c + 1) :
    ∫⁻ x, ENNReal.ofReal (sepWeight δ x) ∂(ν.prod ν) ≤
      ENNReal.ofReal (Real.exp (-(1 - lconc ν c) / 2)) := by
  set L := lconc ν c with hL
  have hL1 : L ≤ 1 := lconc_le_one ν c
  have hL0 : 0 ≤ L := lconc_nonneg ν c
  set e := Real.exp (-1) with he_def
  have he0 : 0 < e := Real.exp_pos _
  have he : e ≤ 1 / 2 := by
    rw [he_def, Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp 1])
  set A := {x : ℤ × ℤ | ¬ δ ≤ |x.1 - x.2|} with hA_def
  have hpt : ∀ x, ENNReal.ofReal (sepWeight δ x) ≤
      ENNReal.ofReal e + ENNReal.ofReal (1 - e) * A.indicator 1 x := by
    intro x
    by_cases hx : δ ≤ |x.1 - x.2|
    · simp [sepWeight, hx, A, he_def]
    · simp only [sepWeight, hx, if_false, A, Set.indicator_of_mem (show x ∈ A from hx),
        Pi.one_apply, mul_one]
      rw [← ENNReal.ofReal_add he0.le (by linarith)]
      simp
  have hAm : (ν.prod ν) A ≤ ENNReal.ofReal L := by
    rw [Measure.prod_apply .of_discrete]
    calc ∫⁻ a, ν (Prod.mk a ⁻¹' A) ∂ν ≤ ∫⁻ _a, ENNReal.ofReal L ∂ν := lintegral_mono fun a => ?_
      _ = ENNReal.ofReal L := by simp
    refine le_trans (measure_mono ?_) (window_le_ofReal_lconc ν c (a - δ + 1))
    intro b hb
    simp only [A, Set.mem_preimage, Set.mem_ofPred_eq, not_le, Set.mem_Ico] at hb ⊢
    rw [abs_lt] at hb
    constructor <;> omega
  calc ∫⁻ x, ENNReal.ofReal (sepWeight δ x) ∂(ν.prod ν)
      ≤ ∫⁻ x, (ENNReal.ofReal e + ENNReal.ofReal (1 - e) * A.indicator 1 x) ∂(ν.prod ν) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal e + ENNReal.ofReal (1 - e) * (ν.prod ν) A := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul _ (measurable_one.indicator .of_discrete),
        lintegral_indicator_one .of_discrete]
    _ ≤ ENNReal.ofReal e + ENNReal.ofReal (1 - e) * ENNReal.ofReal L := by gcongr
    _ = ENNReal.ofReal (e + (1 - e) * L) := by
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add he0.le (by nlinarith)]
    _ ≤ ENNReal.ofReal (Real.exp (-(1 - L) / 2)) := by
      apply ENNReal.ofReal_le_ofReal
      have := Real.add_one_le_exp (-(1 - L) / 2)
      nlinarith [mul_nonneg (sub_nonneg.2 he) (sub_nonneg.2 hL1)]

/-! ### The window bound and the lattice Kolmogorov–Rogozin inequality -/

theorem pair_window_le (m : ℕ) (p : Fin m → ℤ × ℤ) (δ : ℤ) (hδ : 0 < δ) (x : ℤ) (n w : ℕ)
    (hw : (w : ℤ) ≤ n * δ) (A s : ℝ) (hA : 1 ≤ A) (hn : (n : ℝ) ≤ A) (hs : 0 < s) :
    (Measure.pi fun _ : Fin m => coin)
        {ε | (∑ i, if ε i then (p i).1 else (p i).2) ∈ Set.Ico x (x + w)} ≤
      ENNReal.ofReal (A * Real.exp (s / 4)) * ∏ i, ENNReal.ofReal (sepWeight δ (p i)) +
        ENNReal.ofReal (2 * A / Real.sqrt s) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hprod : ∏ i, sepWeight δ (p i) =
      Real.exp (-1) ^ (Fintype.card {i // δ ≤ |(p i).1 - (p i).2|}) := by
    simp only [sepWeight]
    rw [prod_ite, prod_const, prod_const_one, mul_one, Fintype.card_subtype]
  have hA0 : 0 ≤ A * Real.exp (s / 4) := mul_nonneg (by linarith) (Real.exp_pos _).le
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => sepWeight_nonneg δ (p i)),
    ← ENNReal.ofReal_mul hA0,
    ← ENNReal.ofReal_add (mul_nonneg hA0 (prod_nonneg fun i _ => sepWeight_nonneg δ (p i)))
      (div_nonneg (by linarith) hsq.le), hprod, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  refine window_real_bound _ A s n _ ?_ (pi_coin_window_le m p δ hδ x n w hw) hA hn hs
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

theorem lintegral_pair_bound (m : ℕ) (μ : Fin m → Measure ℤ) [∀ i, IsProbabilityMeasure (μ i)]
    (c : ℕ) (δ : ℤ) (hδc : 2 * δ ≤ c + 1) (K K' : ℝ≥0∞) :
    ∫⁻ p, (K * ∏ i, ENNReal.ofReal (sepWeight δ (p i)) + K')
        ∂(Measure.pi fun i => (μ i).prod (μ i)) ≤
      K * ENNReal.ofReal (Real.exp (-(∑ i, (1 - lconc (μ i) c)) / 2)) + K' := by
  have hind : iIndepFun (fun i (p : Fin m → ℤ × ℤ) => ENNReal.ofReal (sepWeight δ (p i)))
      (Measure.pi fun i => (μ i).prod (μ i)) :=
    iIndepFun_pi (X := fun _ q => ENNReal.ofReal (sepWeight δ q))
      (fun _ => Measurable.of_discrete.aemeasurable)
  have hmeas : Measurable fun p : Fin m → ℤ × ℤ => ∏ i, ENNReal.ofReal (sepWeight δ (p i)) :=
    Measurable.of_discrete
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ hmeas,
    lintegral_prod_eq_prod_lintegral_of_indepFun univ _ hind (fun _ => Measurable.of_discrete)]
  gcongr
  have hi : ∀ i, ∫⁻ p, ENNReal.ofReal (sepWeight δ (p i)) ∂(Measure.pi fun i => (μ i).prod (μ i))
      ≤ ENNReal.ofReal (Real.exp (-(1 - lconc (μ i) c) / 2)) := by
    intro i
    have h := (measurePreserving_eval (fun i => (μ i).prod (μ i)) i).lintegral_comp
      (f := fun q => ENNReal.ofReal (sepWeight δ q)) Measurable.of_discrete
    exact h.trans_le (lintegral_sepWeight_le (μ i) c δ hδc)
  calc _ ≤ ∏ i, ENNReal.ofReal (Real.exp (-(1 - lconc (μ i) c) / 2)) :=
        prod_le_prod' fun i _ => hi i
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
        ← sum_div, sum_neg_distrib]

theorem convFin_window_le (m : ℕ) (μ : Fin m → Measure ℤ) [∀ i, IsProbabilityMeasure (μ i)]
    (c w : ℕ) (hc : 1 ≤ c) (hs : 0 < ∑ i, (1 - lconc (μ i) c)) (x : ℤ) :
    convFin m μ (Set.Ico x (x + w)) ≤
      ENNReal.ofReal (3 * (2 * w / c + 1) / Real.sqrt (∑ i, (1 - lconc (μ i) c))) := by
  set s := ∑ i, (1 - lconc (μ i) c) with hs_def
  have hδn0 : 0 < (c + 1) / 2 := by omega
  have hδ0 : (0 : ℤ) < ((c + 1) / 2 : ℕ) := by omega
  have hδc : 2 * (((c + 1) / 2 : ℕ) : ℤ) ≤ c + 1 := by omega
  have hwn : (w : ℤ) ≤ ((w / ((c + 1) / 2) + 1 : ℕ) : ℤ) * (((c + 1) / 2 : ℕ) : ℤ) := by
    have h1 := Nat.div_add_mod w ((c + 1) / 2)
    have h2 := Nat.mod_lt w hδn0
    have : w ≤ (w / ((c + 1) / 2) + 1) * ((c + 1) / 2) := by nlinarith
    exact_mod_cast this
  have hA1 : (1 : ℝ) ≤ 2 * w / c + 1 := by
    have : 0 ≤ (2 * w / c : ℝ) := by positivity
    linarith
  have hnA : ((w / ((c + 1) / 2) + 1 : ℕ) : ℝ) ≤ 2 * w / c + 1 := by
    push_cast
    have h1 : ((w / ((c + 1) / 2) : ℕ) : ℝ) ≤ (w : ℝ) / ((c + 1) / 2 : ℕ) := Nat.cast_div_le
    have h2 : (w : ℝ) / ((c + 1) / 2 : ℕ) ≤ 2 * w / c := by
      have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
      have hd0 : (0 : ℝ) < ((c + 1) / 2 : ℕ) := by exact_mod_cast hδn0
      rw [div_le_div_iff₀ hd0 hc0]
      have : (c : ℝ) ≤ 2 * ((c + 1) / 2 : ℕ) := by exact_mod_cast (show c ≤ 2 * ((c + 1) / 2) by omega)
      have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
      nlinarith
    linarith
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  rw [convFin_apply_eq_lintegral]
  refine (lintegral_mono fun p => pair_window_le m p _ hδ0 x _ w hwn _ s hA1 hnA hs).trans ?_
  refine (lintegral_pair_bound m μ c _ hδc _ _).trans ?_
  have hA0 : 0 ≤ (2 * w / c + 1 : ℝ) * Real.exp (s / 4) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_add (mul_nonneg hA0 (Real.exp_pos _).le)
    (div_nonneg (by linarith) hsq.le)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : Real.exp (s / 4) * Real.exp (-s / 2) = Real.exp (-(s / 4)) := by
    rw [← Real.exp_add]; ring_nf
  have hsq2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hlin : Real.sqrt s ≤ 1 + s / 4 := by nlinarith [sq_nonneg (Real.sqrt s - 2)]
  have hle : Real.sqrt s ≤ Real.exp (s / 4) :=
    hlin.trans (by have := Real.add_one_le_exp (s / 4); linarith)
  have hkey : Real.exp (-(s / 4)) ≤ 1 / Real.sqrt s := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hsq hle
  rw [mul_assoc, hexp]
  calc (2 * w / c + 1 : ℝ) * Real.exp (-(s / 4)) + 2 * (2 * w / c + 1) / Real.sqrt s
      ≤ (2 * w / c + 1 : ℝ) * (1 / Real.sqrt s) + 2 * (2 * w / c + 1) / Real.sqrt s := by
        gcongr
    _ = 3 * (2 * w / c + 1) / Real.sqrt s := by ring

end Rogozin

/-- The constant in the lattice Kolmogorov–Rogozin inequality. -/
def CRog : ℝ := 6

open Rogozin in
/-- **Lattice Kolmogorov–Rogozin inequality** with the constant `CRog = 6`. -/
theorem rogozinLattice : RogozinLattice CRog := by
  intro m μ hμ c w hc hw
  set s := ∑ i, (1 - lconc (μ i) c) with hs_def
  have hrhs : 0 ≤ CRog * ((w : ℝ) / c + 1) := by unfold CRog; positivity
  rcases le_or_gt s 0 with hs | hs
  · rw [Real.sqrt_eq_zero'.2 hs, mul_zero]
    exact hrhs
  · have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
    have hkey : lconc (convFin m μ) w ≤ 3 * (2 * w / c + 1) / Real.sqrt s := by
      refine ciSup_le fun x => ?_
      have hA : (0 : ℝ) ≤ 3 * (2 * w / c + 1) / Real.sqrt s := by positivity
      exact ENNReal.toReal_le_of_le_ofReal hA (convFin_window_le m μ c w hc hs x)
    calc lconc (convFin m μ) w * Real.sqrt s
        ≤ 3 * (2 * w / c + 1) / Real.sqrt s * Real.sqrt s := by gcongr
      _ = 3 * (2 * w / c + 1) := by field_simp
      _ ≤ CRog * ((w : ℝ) / c + 1) := by
        unfold CRog
        have : (0 : ℝ) ≤ w / c := by positivity
        linarith [show (2 * w / c : ℝ) = 2 * (w / c) by ring]

end

end PGM
