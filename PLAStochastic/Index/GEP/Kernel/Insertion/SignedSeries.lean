import PLAStochastic.Index.GEP.Kernel.Insertion.LongRows
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.Reversal
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Actual signed insertion series

Absolute budgets are summed before the reward, which may depend on both
lengths and the slope. No factorization or slope smoothness is used.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

theorem kernel_measurable_summable_decomposition {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {q g r : ι → X → ℝ → ℂ} {U E L : X → ι → ℝ} {UB EB LB : ℝ}
    (hg : ∀ i, Measurable fun p : X × ℝ => g i p.1 p.2)
    (hr : ∀ i, Measurable fun p : X × ℝ => r i p.1 p.2)
    (he : ∀ i p x, q i p x = g i p x+r i p x)
    (hU : ∀ p, Summable (U p)) (hE : ∀ p, Summable (E p)) (hL : ∀ p, Summable (L p))
    (hUB : ∀ p, ∑' i, U p i ≤ UB) (hEB : ∀ p, ∑' i, E p i ≤ EB)
    (hLB : ∀ p, ∑' i, L p i ≤ LB)
    (hgn : ∀ i p x, ‖g i p x‖ ≤ U p i) (hrn : ∀ i p x, ‖r i p x‖ ≤ E p i)
    (hgl : ∀ i p x y, ‖g i p x-g i p y‖ ≤ L p i*|x-y|) :
    (∀ p x, Summable fun i => q i p x) ∧
    ∃ G R : X → ℝ → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => R p.1 p.2) ∧
      (∀ p x, (∑' i, q i p x) = G p x+R p x) ∧
      (∀ p x y, ‖G p x-G p y‖ ≤ LB*|x-y|) ∧
      (∀ p x, ‖R p x‖ ≤ EB) ∧ (∀ p x, ‖G p x‖ ≤ UB) := by
  have hgs : ∀ p x, Summable fun i => g i p x := fun p x => (hU p).of_norm_bounded (fun i => hgn i p x)
  have hrs : ∀ p x, Summable fun i => r i p x := fun p x => (hE p).of_norm_bounded (fun i => hrn i p x)
  refine ⟨fun p x => ((hgs p x).add (hrs p x)).congr (fun i => (he i p x).symm),
    (fun p x => ∑' i, g i p x), (fun p x => ∑' i, r i p x),
    Measurable.tsum hg, Measurable.tsum hr, ?_, ?_, ?_, ?_⟩
  · intro p x
    simp_rw [he]
    exact (hgs p x).tsum_add (hrs p x)
  · intro p x y
    rw [← (hgs p x).tsum_sub (hgs p y)]
    refine (tsum_of_norm_bounded ((hL p).mul_right |x-y|).hasSum (fun i => hgl i p x y)).trans ?_
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hLB p) (abs_nonneg _)
  · intro p x
    exact (tsum_of_norm_bounded (hE p).hasSum (fun i => hrn i p x)).trans (hEB p)
  · intro p x
    exact (tsum_of_norm_bounded (hU p).hasSum (fun i => hgn i p x)).trans (hUB p)

set_option maxHeartbeats 800000 in
/-- The actual signed sum with a positive left row and a long right row. -/
theorem krInsertion_signed_long_right {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a β a' : X → ℝ} (hβ : Measurable β) (ha' : Measurable a')
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) (β p) (a' p))
    {b c : ℝ} (hb : b=0 ∨ b=w) (hc : c=0 ∨ c=w) {P : ℕ} (hP : 12 ≤ P)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krEps D vlo vhi)
    {v : (ℕ × ℕ) → X → ℝ} (hv : ∀ q, Measurable (v q))
    (hvb : ∀ q p, |v q p| ≤ Real.exp (ε*((q.1+1 : ℕ) : ℝ)/w^2) *
      Real.exp (ε*((P+1+q.2 : ℕ) : ℝ)/w^2)) :
    let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
    let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
    let BB := Real.exp (3*ε)*((krCG D K L vlo vhi+4*krC₄ D K L/krKappa D vlo vhi)*(1+A)*(1+Real.log w))
    let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
    (∀ p x, Summable fun q : ℕ × ℕ => v q p *
      kernelMarkedFullDens (Icc 0 w) ν f (β p) (a' p) x (q.1+1) (P+1+q.2) b c) ∧
    ∃ G R : X → ℝ → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => R p.1 p.2) ∧
      (∀ p x, ((∑' q : ℕ × ℕ, v q p * kernelMarkedFullDens (Icc 0 w) ν f
        (β p) (a' p) x (q.1+1) (P+1+q.2) b c : ℝ) : ℂ) = G p x+R p x) ∧
      (∀ p x y, ‖G p x-G p y‖ ≤ (2*VB*BB)*|x-y|) ∧
      (∀ p x, ‖R p x‖ ≤ 4*RB*OB) ∧ (∀ p x, ‖G p x‖ ≤ VB*OB) := by
  classical
  dsimp only
  have H₀ := H (Classical.choice ‹Nonempty X›)
  have hεκ : ε ≤ krKappa D vlo vhi/16 := by
    have := hε.trans H₀.krEps_le_kappa
    have := H₀.kappa_pos
    linarith
  let ω : ℕ → ℝ := fun n => Real.exp (ε*(n : ℝ)/w^2)
  let V : ℕ → ℝ := fun i => ω (P+1+i)*krRowVarBudget D K L vlo vhi w A (P+1+i)
  let E : ℕ → ℝ := fun i => ω (P+1+i)*krRowRemBudget D K L vlo vhi A (P+1+i)
  let B : ℕ → ℝ := fun l => ω (l+1)*krRowSupBudget D K L vlo vhi w A (l+1)
  let S : X → ℕ → ℝ := fun p l => ω (l+1)*krSurv (Icc 0 w) (ν : Measure ℝ) (β p) (a' p) (l+1) b
  let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
  let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
  let BB := Real.exp (3*ε)*((krCG D K L vlo vhi+4*krC₄ D K L/krKappa D vlo vhi)*(1+A)*(1+Real.log w))
  let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
  obtain ⟨hVs, hVB, hEs, hEB⟩ := krRow_expw_absolute_budgets ν H₀ hP hε0 hε
  obtain ⟨hBs, hBB⟩ := krRow_expw_sup_absolute_budget ν H₀ hε0 hεκ
  change Summable V at hVs
  change Summable E at hEs
  change Summable B at hBs
  change (∑' i, V i) ≤ VB at hVB
  change (∑' i, E i) ≤ RB at hEB
  change (∑' i, B i) ≤ BB at hBB
  have hω : ∀ n, 0 ≤ ω n := fun n => (Real.exp_pos _).le
  have hV : ∀ i, 0 ≤ V i := fun i => mul_nonneg (hω _) (mul_nonneg
    (mul_nonneg (mul_nonneg H₀.classConsts.2.2.2.2.le (Real.sqrt_nonneg _))
      (by linarith [H₀.hA])) (krVarTerm_nonneg H₀.hw0 _))
  have hE : ∀ i, 0 ≤ E i := fun i => mul_nonneg (hω _) (mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg H₀.classConsts.2.2.2.1.le (Real.sqrt_nonneg _))
      (by linarith [H₀.hA])) (pow_nonneg H₀.classConsts.1 _)))
  have hB : ∀ l, 0 ≤ B l := fun l => mul_nonneg (hω _) (krRowSupBudget_nonneg ν H₀ _)
  have hS : ∀ p l, 0 ≤ S p l := fun p l => mul_nonneg (hω _)
    (krSurv_nonneg (H p).hJ ν (β p) (a' p) (l+1) b)
  have hSs : ∀ p, Summable (S p) := by
    intro p
    simpa only [S, ω, Nat.add_comm] using (summable_nat_add_iff 1).2
      (summable_expw_krSurv_bdry ν (H p) hb hε0 hεκ)
  have hSB : ∀ p, ∑' l, S p l ≤ OB := by
    intro p
    apply Real.tsum_le_of_sum_range_le (hS p)
    intro M
    have hsum := sum_expw_krSurv_bdry_le ν (H p) hb hε0 hεκ (M+1)
    rw [Finset.sum_range_succ'] at hsum
    exact (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le
      (krSurv_nonneg (H p).hJ ν (β p) (a' p) 0 b))).trans hsum
  have hVB0 : 0 ≤ VB := (tsum_nonneg hV).trans hVB
  have hRB0 : 0 ≤ RB := (tsum_nonneg hE).trans hEB
  have hBB0 : 0 ≤ BB := (tsum_nonneg hB).trans hBB
  have hOB0 : 0 ≤ OB := (tsum_nonneg (hS (Classical.choice ‹Nonempty X›))).trans (hSB _)
  have hUV : ∀ p, Summable (fun q : ℕ × ℕ => S p q.1*V q.2) :=
    fun p => (hSs p).mul_of_nonneg hVs (hS p) hV
  have hUE : ∀ p, Summable (fun q : ℕ × ℕ => S p q.1*E q.2) :=
    fun p => (hSs p).mul_of_nonneg hEs (hS p) hE
  have hUL : Summable (fun q : ℕ × ℕ => B q.1*V q.2) := hBs.mul_of_nonneg hVs hB hV
  have hUVB : ∀ p, (∑' q : ℕ × ℕ, S p q.1*V q.2) ≤ VB*OB := by
    intro p
    rw [← (hSs p).tsum_mul_tsum hVs (hUV p)]
    simpa only [mul_comm] using mul_le_mul (hSB p) hVB (tsum_nonneg hV) hOB0
  have hUEB : ∀ p, (∑' q : ℕ × ℕ, 4*(S p q.1*E q.2)) ≤ 4*RB*OB := by
    intro p
    rw [tsum_mul_left, ← (hSs p).tsum_mul_tsum hEs (hUE p)]
    have h := mul_le_mul (hSB p) hEB (tsum_nonneg hE) hOB0
    nlinarith
  have hULB : (∑' q : ℕ × ℕ, 2*(B q.1*V q.2)) ≤ 2*VB*BB := by
    rw [tsum_mul_left, ← hBs.tsum_mul_tsum hVs hUL]
    have h := mul_le_mul hBB hVB (tsum_nonneg hV) hBB0
    nlinarith
  obtain ⟨g, r, hg, hr, he, hl, hrem, hnorm⟩ :=
    krInsertion_long_right_family ν hβ ha' H hb hc hP
  let qf : (ℕ × ℕ) → X → ℝ → ℂ := fun q p x =>
    (v q p * kernelMarkedFullDens (Icc 0 w) ν f (β p) (a' p) x (q.1+1) (P+1+q.2) b c : ℝ)
  let gf : (ℕ × ℕ) → X → ℝ → ℂ := fun q p x => (v q p : ℂ)*g q.1 q.2 p x
  let rf : (ℕ × ℕ) → X → ℝ → ℂ := fun q p x => (v q p : ℂ)*r q.1 q.2 p x
  have hgm : ∀ q, Measurable (fun p : X × ℝ => gf q p.1 p.2) := fun q =>
    (Complex.measurable_ofReal.comp ((hv q).comp measurable_fst)).mul (hg q.1 q.2)
  have hrm : ∀ q, Measurable (fun p : X × ℝ => rf q p.1 p.2) := fun q =>
    (Complex.measurable_ofReal.comp ((hv q).comp measurable_fst)).mul (hr q.1 q.2)
  have heq : ∀ q p x, qf q p x=gf q p x+rf q p x := by
    intro q p x
    dsimp only [qf, gf, rf]
    rw [Complex.ofReal_mul, he, mul_add]
  have hgn : ∀ q p x, ‖gf q p x‖ ≤ S p q.1*V q.2 := by
    intro q p x
    dsimp only [gf]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h := mul_le_mul (hvb q p) (hnorm q.1 q.2 p x) (norm_nonneg _) (mul_nonneg (hω _) (hω _))
    exact h.trans_eq (by dsimp only [S, V, ω]; ring)
  have hrn : ∀ q p x, ‖rf q p x‖ ≤ 4*(S p q.1*E q.2) := by
    intro q p x
    dsimp only [rf]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h := mul_le_mul (hvb q p) (hrem q.1 q.2 p x) (norm_nonneg _) (mul_nonneg (hω _) (hω _))
    exact h.trans_eq (by dsimp only [S, E, ω]; ring)
  have hgl : ∀ q p x y, ‖gf q p x-gf q p y‖ ≤ (2*(B q.1*V q.2))*|x-y| := by
    intro q p x y
    dsimp only [gf]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h := mul_le_mul (hvb q p) (hl q.1 q.2 p x y) (norm_nonneg _) (mul_nonneg (hω _) (hω _))
    exact h.trans_eq (by dsimp only [B, V, ω]; ring)
  obtain ⟨hqs, G, R, hG, hR, hsplit, hLip, hRem, hNorm⟩ :=
    kernel_measurable_summable_decomposition hgm hrm heq hUV (fun p => (hUE p).mul_left 4)
      (fun _ => hUL.mul_left 2) hUVB hUEB (fun _ => hULB) hgn hrn hgl
  refine ⟨fun p x => Complex.summable_ofReal.mp (hqs p x), G, R, hG, hR, ?_, hLip, hRem, hNorm⟩
  intro p x
  rw [Complex.ofReal_tsum]
  exact hsplit p x

set_option maxHeartbeats 800000 in
/-- The actual signed sum with a long left row and a positive right row. -/
theorem krInsertion_signed_long_left {X : Type*} [MeasurableSpace X] [Nonempty X]
    {D θ vlo vhi K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {a β a' : X → ℝ} (hβ : Measurable β) (ha' : Measurable a')
    (H : ∀ p, KrBand D θ vlo vhi K L ν f w A (a p) (β p) (a' p))
    {b c : ℝ} (hb : b=0 ∨ b=w) (hc : c=0 ∨ c=w) {P : ℕ} (hP : 12 ≤ P)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krEps D vlo vhi)
    {v : (ℕ × ℕ) → X → ℝ} (hv : ∀ q, Measurable (v q))
    (hvb : ∀ q p, |v q p| ≤ Real.exp (ε*((q.1+1 : ℕ) : ℝ)/w^2) *
      Real.exp (ε*((P+1+q.2 : ℕ) : ℝ)/w^2)) :
    let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
    let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
    let BB := Real.exp (3*ε)*((krCG D K L vlo vhi+4*krC₄ D K L/krKappa D vlo vhi)*(1+A)*(1+Real.log w))
    let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
    (∀ p x, Summable fun q : ℕ × ℕ => v q p *
      kernelMarkedFullDens (Icc 0 w) ν f (β p) (a' p) x (P+1+q.2) (q.1+1) b c) ∧
    ∃ G R : X → ℝ → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => R p.1 p.2) ∧
      (∀ p x, ((∑' q : ℕ × ℕ, v q p * kernelMarkedFullDens (Icc 0 w) ν f
        (β p) (a' p) x (P+1+q.2) (q.1+1) b c : ℝ) : ℂ) = G p x+R p x) ∧
      (∀ p x y, ‖G p x-G p y‖ ≤ (2*VB*BB)*|x-y|) ∧
      (∀ p x, ‖R p x‖ ≤ 4*RB*OB) ∧ (∀ p x, ‖G p x‖ ≤ VB*OB) := by
  classical
  dsimp only
  obtain ⟨hS, G, R, hG, hR, he, hl, hr, hn⟩ :=
    krInsertion_signed_long_right ν hβ.neg ha'.neg (fun p => (H p).rev)
      hc hb hP hε0 hε hv hvb
  have hrev : ∀ q : ℕ × ℕ, ∀ p x,
      kernelMarkedFullDens (Icc 0 w) ν f (β p) (a' p) x (P+1+q.2) (q.1+1) b c =
        kernelMarkedFullDens (Icc 0 w) ν f (-β p) (-a' p) x (q.1+1) (P+1+q.2) c b :=
    fun q p x => kernelMarkedFullDens_symm (H p).hJ (H p).hJfin ν (H p).hf (H p).hf0
      (H p).hfD (H p).hνf (H p).ha' (β p) x _ _ b c
  refine ⟨?_, G, R, hG, hR, ?_, hl, hr, hn⟩
  · intro p x
    simp_rw [hrev]
    simpa only [Pi.neg_apply] using hS p x
  · intro p x
    simp_rw [hrev]
    simpa only [Pi.neg_apply] using he p x

end
end PGM
