import PLAStochastic.Index.CEPS.Output.Counting
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Track O: the second moment of the centred single-insertion sum

`output-closure.md` (O6). Under the iid product law `ν^{⊗n}` with `E ρ(X) = 0` and
`E ρ(X)² = J_F`, two products `∏_{l ∈ S} ρ(X_l)` and `∏_{l ∈ S'} ρ(X_l)` are orthogonal
unless `S = S'` (`integral_prod_score_mul`). Hence

`E (outCentred f j β)² = J_F^k · #{(c, c') : high part β, same singles} ≤ n^k j^{2j} J_F^k`,

`k = j - ∑ β` (`lintegral_sq_outCentred_le`).
-/

noncomputable section

open Finset MeasureTheory
open scoped ENNReal

namespace PGM

variable {n : ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ}

theorem prod_mul_prod_eq_pow (S S' : Finset (Fin n)) (x : Fin n → ℝ) :
    (∏ l ∈ S, g (x l)) * ∏ l ∈ S', g (x l) =
      ∏ l, g (x l) ^ ((if l ∈ S then 1 else 0) + (if l ∈ S' then 1 else 0)) := by
  classical
  have h : ∀ T : Finset (Fin n), ∏ l ∈ T, g (x l) = ∏ l, g (x l) ^ (if l ∈ T then 1 else 0) := by
    intro T
    have h1 : ∏ l ∈ T, g (x l) = ∏ l, (if l ∈ T then g (x l) else 1) := by
      rw [Finset.prod_ite_mem, Finset.univ_inter]
    rw [h1]
    exact Finset.prod_congr rfl fun l _ => by split_ifs <;> simp
  rw [h S, h S', ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun l _ => (pow_add _ _ _).symm

theorem integrable_pow_of_sq (hg : Measurable g) (hg2 : Integrable (fun x => g x ^ 2) ν) :
    ∀ e ≤ 2, Integrable (fun x => g x ^ e) ν := by
  have hL2 : MemLp g 2 ν := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hg2
  intro e he
  interval_cases e
  · simp
  · simpa using hL2.integrable one_le_two
  · exact hg2

theorem integral_prod_score_mul (hg0 : ∫ x, g x ∂ν = 0) (S S' : Finset (Fin n)) :
    ∫ x, (∏ l ∈ S, g (x l)) * ∏ l ∈ S', g (x l) ∂(Measure.pi fun _ => ν) =
      if S = S' then (∫ x, g x ^ 2 ∂ν) ^ #S else 0 := by
  classical
  simp_rw [prod_mul_prod_eq_pow S S']
  rw [integral_fintype_prod_eq_prod (f := fun l y =>
    g y ^ ((if l ∈ S then 1 else 0) + (if l ∈ S' then 1 else 0)))]
  split_ifs with hSS
  · subst hSS
    have : ∀ l, ∫ y, g y ^ ((if l ∈ S then 1 else 0) + (if l ∈ S then 1 else 0)) ∂ν =
        if l ∈ S then ∫ y, g y ^ 2 ∂ν else 1 := by
      intro l
      split_ifs <;> simp
    simp_rw [this]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  · obtain ⟨l, hl⟩ : ∃ l, ¬ (l ∈ S ↔ l ∈ S') := by
      by_contra h
      push Not at h
      exact hSS (Finset.ext h)
    refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
    by_cases h1 : l ∈ S
    · have h2 : l ∉ S' := fun h2 => hl ⟨fun _ => h2, fun _ => h1⟩
      simp [h1, h2, hg0]
    · have h2 : l ∈ S' := by
        by_contra h2
        exact hl ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      simp [h1, h2, hg0]

theorem integrable_prod_score_mul (hg : Measurable g) (hg2 : Integrable (fun x => g x ^ 2) ν)
    (S S' : Finset (Fin n)) :
    Integrable (fun x : Fin n → ℝ => (∏ l ∈ S, g (x l)) * ∏ l ∈ S', g (x l))
      (Measure.pi fun _ => ν) := by
  classical
  simp_rw [prod_mul_prod_eq_pow S S']
  refine Integrable.fintype_prod (f := fun l y =>
    g y ^ ((if l ∈ S then 1 else 0) + (if l ∈ S' then 1 else 0))) fun l => ?_
  exact integrable_pow_of_sq hg hg2 _ (by split_ifs <;> omega)

/-- **The second moment of the centred single-insertion sum** (`output-closure.md` (O6)). -/
theorem lintegral_sq_outCentred_le {f : ℝ → ℝ} (hρm : Measurable (mellinScore f))
    (hρ2 : Integrable (fun x => mellinScore f x ^ 2) ν) (hρ0 : ∫ x, mellinScore f x ∂ν = 0)
    {J : ℝ} (hJ : ∫ x, mellinScore f x ^ 2 ∂ν ≤ J) (j : ℕ) (β : Fin n → ℕ) :
    ∫⁻ x, ENNReal.ofReal (outCentred f j β x ^ 2) ∂(Measure.pi fun _ => ν) ≤
      ENNReal.ofReal ((n : ℝ) ^ (j - ∑ l, β l) * (j : ℝ) ^ j * (j : ℝ) ^ j *
        J ^ (j - ∑ l, β l)) := by
  classical
  set k := j - ∑ l, β l with hk
  set C := ({c : Fin j → Fin n | outHigh c = β} : Finset (Fin j → Fin n)) with hC
  set JF := ∫ x, mellinScore f x ^ 2 ∂ν with hJF
  have hJF0 : 0 ≤ JF := integral_nonneg fun x => sq_nonneg _
  have hsq : ∀ x, outCentred f j β x ^ 2 = ∑ c ∈ C, ∑ c' ∈ C,
      (∏ l ∈ outSingles c, mellinScore f (x l)) * ∏ l ∈ outSingles c', mellinScore f (x l) := by
    intro x
    rw [outCentred, sq, Finset.sum_mul_sum]
  have hint : ∀ c c' : Fin j → Fin n, Integrable (fun x : Fin n → ℝ =>
      (∏ l ∈ outSingles c, mellinScore f (x l)) * ∏ l ∈ outSingles c', mellinScore f (x l))
      (Measure.pi fun _ => ν) := fun c c' =>
    integrable_prod_score_mul hρm hρ2 _ _
  have hVint : Integrable (fun x => outCentred f j β x ^ 2) (Measure.pi fun _ => ν) := by
    simp_rw [hsq]
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ => hint c c'
  have hval : ∫ x, outCentred f j β x ^ 2 ∂(Measure.pi fun _ => ν) =
      ∑ c ∈ C, ∑ c' ∈ C, if outSingles c = outSingles c' then JF ^ k else 0 := by
    simp_rw [hsq]
    rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ => hint c c']
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [integral_finsetSum _ fun c' _ => hint c c']
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [integral_prod_score_mul hρ0]
    have hc' : outHigh c = β := by simpa [hC] using hc
    rw [card_outSingles_of_high hc']
  have hcount : (∑ c ∈ C, ∑ c' ∈ C, if outSingles c = outSingles c' then JF ^ k else 0) =
      #{p : (Fin j → Fin n) × (Fin j → Fin n) |
        outHigh p.1 = β ∧ outHigh p.2 = β ∧ outSingles p.1 = outSingles p.2} * JF ^ k := by
    have hset : ((C ×ˢ C).filter fun p => outSingles p.1 = outSingles p.2) =
        ({p : (Fin j → Fin n) × (Fin j → Fin n) |
          outHigh p.1 = β ∧ outHigh p.2 = β ∧ outSingles p.1 = outSingles p.2} :
          Finset ((Fin j → Fin n) × (Fin j → Fin n))) := by
      ext p
      simp [hC, Finset.mem_product, and_assoc]
    rw [← Finset.sum_product', Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, hset]
  rw [← ofReal_integral_eq_lintegral_ofReal hVint
    (Filter.Eventually.of_forall fun x => sq_nonneg _), hval, hcount]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcard := card_outHigh_pairs_le (n := n) (j := j) β
  have hcard' : (#{p : (Fin j → Fin n) × (Fin j → Fin n) |
        outHigh p.1 = β ∧ outHigh p.2 = β ∧ outSingles p.1 = outSingles p.2} : ℝ) ≤
      (n : ℝ) ^ k * (j : ℝ) ^ j * (j : ℝ) ^ j := by exact_mod_cast hcard
  have hJk : JF ^ k ≤ J ^ k := pow_le_pow_left₀ hJF0 hJ k
  calc (#{p : (Fin j → Fin n) × (Fin j → Fin n) |
        outHigh p.1 = β ∧ outHigh p.2 = β ∧ outSingles p.1 = outSingles p.2} : ℝ) * JF ^ k
      ≤ ((n : ℝ) ^ k * (j : ℝ) ^ j * (j : ℝ) ^ j) * J ^ k :=
        mul_le_mul hcard' hJk (pow_nonneg hJF0 _) (by positivity)
    _ = _ := rfl

end PGM
