import PLAStochastic.Index.CEPS.Tails.OccupationSeries

/-!
# The exact drawup occupation/exit identity

The `OK` occupation and `Cross` exit series are distinct actual objects. This
module proves `(1 - φ(t)) Fdr(t) = 1 - E exp(-t S_τ)` over `Re t ≥ 0`.
At `t = 0` the multiplicative identity remains valid; no zero division is used.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset

/-- Updating the next unused gap leaves drawup survival unchanged. -/
theorem cepsDrawupOK_update (β a l : ℝ) (g : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    cepsDrawupOK β a l (Function.update g n x) n ↔ cepsDrawupOK β a l g n := by
  have he : ∀ m ≤ n, kWalk 0 β a (Function.update g n x) m = kWalk 0 β a g m := by
    intro m hm
    exact surv_kWalk_congr fun s hs => Function.update_of_ne (by omega : s ≠ n) _ _
  constructor <;> intro h i j hij hj
  · simpa only [he i (by omega), he j hj] using h i j hij hj
  · simpa only [he i (by omega), he j hj] using h i j hij hj

/-- The first-crossing event is the loss of drawup survival in one time step. -/
theorem cepsDrawupCross_iff_survival_diff (β a l : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    cepsDrawupCross β a l g n ↔ cepsDrawupOK β a l g n ∧ ¬ cepsDrawupOK β a l g (n + 1) := by
  constructor
  · rintro ⟨hok, i, hi, hlt⟩
    exact ⟨hok, fun hn => not_le.mpr hlt (hn i (n + 1) hi le_rfl)⟩
  · rintro ⟨hok, hn⟩
    unfold cepsDrawupOK at hn
    push Not at hn
    obtain ⟨i, j, hij, hj, hlt⟩ := hn
    have hj' : j = n + 1 := by
      by_contra h
      have := hok i j hij (by omega)
      linarith
    subst j
    exact ⟨hok, i, hij, hlt⟩

/-- Marked next-gap expectation on a surviving drawup prefix. -/
theorem CepsGapDensity.integral_drawup_next {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D δ l : ℝ} (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) (n : ℕ) :
    ∫ g, {g | cepsDrawupOK (1 + δ) 1 l g n}.indicator
      (fun g => Complex.exp (-t * gapKeys g (n + 1))) g ∂(iidLaw ν) =
        cepsLaplace ν t * cepsDrawupOccupationTerm ν δ l t n := by
  have hi := hf.integrable_marked_event ht (n + 1) (measurableSet_cepsDrawupOK (1 + δ) 1 l n)
  rw [integral_iidLaw_update ν n hi, cepsDrawupOccupationTerm, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  by_cases hg : cepsDrawupOK (1 + δ) 1 l g n
  · have hg' : ∀ x, Function.update g n x ∈ {g | cepsDrawupOK (1 + δ) 1 l g n} :=
      fun x => (cepsDrawupOK_update _ _ _ _ _ _).mpr hg
    simp only [indicator_of_mem (show g ∈ {g | cepsDrawupOK (1 + δ) 1 l g n} from hg),
      indicator_of_mem (hg' _), gapKeys_update_succ]
    have he : ∀ x : ℝ, Complex.exp (-t * ((gapKeys g n + x : ℝ) : ℂ)) =
        Complex.exp (-t * gapKeys g n) * Complex.exp (-t * x) := by
      intro x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [he]
    rw [integral_const_mul]
    unfold cepsLaplace
    ring
  · have hg' : ∀ x, Function.update g n x ∉ {g | cepsDrawupOK (1 + δ) 1 l g n} :=
      fun x h => hg ((cepsDrawupOK_update _ _ _ _ _ _).mp h)
    simp only [indicator_of_notMem (show g ∉ {g | cepsDrawupOK (1 + δ) 1 l g n} from hg),
      indicator_of_notMem (hg' _), integral_zero, mul_zero]

/-- The actual marked drawup exit coefficient is one step of occupation loss. -/
theorem CepsGapDensity.drawup_exit_coeff_eq {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D δ l : ℝ} (hf : CepsGapDensity ν f D) {t : ℂ} (ht : 0 ≤ t.re) (n : ℕ) :
    Complex.exp (-(t * ((1 + δ : ℝ) : ℂ)) * ((n : ℂ) + 1)) *
      cepsDrawupTerm ν (1 + δ) 1 l t n =
        cepsLaplace ν t * cepsDrawupOccupationTerm ν δ l t n -
          cepsDrawupOccupationTerm ν δ l t (n + 1) := by
  rw [cepsDrawupTerm_gapKeys, ← hf.integral_drawup_next ht n, cepsDrawupOccupationTerm,
    ← integral_sub (hf.integrable_marked_event ht (n + 1) (measurableSet_cepsDrawupOK (1 + δ) 1 l n))
      (hf.integrable_marked_event ht (n + 1) (measurableSet_cepsDrawupOK (1 + δ) 1 l (n + 1)))]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have he := cepsDrawupCross_iff_survival_diff (1 + δ) 1 l g n
  by_cases h1 : cepsDrawupOK (1 + δ) 1 l g (n + 1)
  · have h0 : cepsDrawupOK (1 + δ) 1 l g n := fun i j hij hj => h1 i j hij (by omega)
    have hx : ¬ cepsDrawupCross (1 + δ) 1 l g n := fun h => (he.mp h).2 h1
    simp [h0, h1, hx]
  · by_cases h0 : cepsDrawupOK (1 + δ) 1 l g n
    · have hx := he.mpr ⟨h0, h1⟩
      simp [h0, h1, hx]
    · have hx : ¬ cepsDrawupCross (1 + δ) 1 l g n := fun h => h0 h.1
      simp [h0, h1, hx]

/-- At time zero, drawup occupation is one when the level is nonnegative. -/
theorem cepsDrawupOccupationTerm_zero (ν : ProbabilityMeasure ℝ) (δ : ℝ) {l : ℝ}
    (hl : 0 ≤ l) (t : ℂ) : cepsDrawupOccupationTerm ν δ l t 0 = 1 := by
  have he : {g | cepsDrawupOK (1 + δ) 1 l g 0} = univ := by
    ext g
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    intro i j hij hj
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    simpa only [sub_self] using hl
  simp [cepsDrawupOccupationTerm, he, gapKeys_zero]

/-- Exact multiplicative drawup occupation identity on the whole right half-plane. -/
theorem cepsDrawupOccupation_mul_of_regLaw {ν : ProbabilityMeasure ℝ}
    {D θ vlo vhi δ l : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D)
    (hvlo : 0 < vlo) (hδ : 0 < δ) (hl : 0 ≤ l) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {t : ℂ} (ht : 0 ≤ t.re) :
    (1 - cepsLaplace ν t) * cepsDrawupOccupation ν δ l t =
      1 - cepsDrawup ν (1 + δ) 1 l t (t * ((1 + δ : ℝ) : ℂ)) := by
  have hs := (summable_norm_cepsDrawupOccupation_of_regLaw (l := l) hν hθ hD hvlo hδ hf ht).of_norm
  have hshift := (summable_nat_add_iff 1).mpr hs
  have he : cepsDrawup ν (1 + δ) 1 l t (t * ((1 + δ : ℝ) : ℂ)) =
      cepsLaplace ν t * cepsDrawupOccupation ν δ l t -
        (cepsDrawupOccupation ν δ l t - 1) := by
    unfold cepsDrawup
    simp_rw [hf.drawup_exit_coeff_eq ht]
    rw [(hs.mul_left _).tsum_sub hshift, tsum_mul_left]
    have htel := hs.sum_add_tsum_nat_add 1
    simp only [sum_range_one, cepsDrawupOccupationTerm_zero ν δ hl t] at htel
    unfold cepsDrawupOccupation
    linear_combination -htel
  rw [he]
  ring

end

end PGM
