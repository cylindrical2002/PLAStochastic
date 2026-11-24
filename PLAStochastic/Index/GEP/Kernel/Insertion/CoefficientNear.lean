import PLAStochastic.Index.GEP.Kernel.Insertion.Coefficient
import PLAStochastic.Index.GEP.Response.InfluenceDecomposition

/-!
# Near-slope AL for the actual exterior-weighted insertion coefficient

The three exterior length sums are performed before normalizing the marked
Green coefficient. The original reward remains jointly measurable and may
depend on every block length and both exterior paths.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

set_option maxHeartbeats 1200000 in
/-- The near-slope AL bound after the actual other pin and both outside paths
have been integrated and summed. The reward envelope `M` may already contain
its scalar or output normalization by `C`. -/
theorem krInsertion_coefficient_near (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ cS KS : ℝ, 0 < cS ∧ 0 < KS ∧
    ∀ {K L w A : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
      {S : Set ℝ} (_hS : MeasurableSet S) (_hne : S.Nonempty)
      (_hSI : S ⊆ Ioo (1/2 : ℝ) 2)
      (_H : ∀ a ∈ S, KrBand D θ vlo vhi K L ν f w A a 1 a)
      (_hAw : A ≤ w) (up outerUp : Bool) {P : ℕ} (_hP : 12 ≤ P) (_hPw : (P : ℝ) ≤ w/8)
      {R : ℝ} (_hR0 : 0 ≤ R) (_hRw : R ≤ w/8)
      {ε M : ℝ} (_hε0 : 0 ≤ ε) (_hε : ε ≤ krEps D vlo vhi) (_hM : 0 ≤ M)
      {W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ}
      (_hW : ∀ l r t, Measurable (fun p : ℝ × (ℕ → ℝ) => W l r t p.1 p.2))
      (_hWB : ∀ a ∈ S, ∀ l r t g, krInsertionOuter w outerUp l r t a g ≠ 0 →
        |W l r t a g| ≤ M*Real.exp (ε*((t.1 : ℝ)+l+r+t.2.1+t.2.2+2)/w^2)),
    let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot P+1)
    let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(P/3-1)
    let BB := Real.exp (3*ε)*((krCG D K L vlo vhi+4*krC₄ D K L/krKappa D vlo vhi)*(1+A)*(1+Real.log w))
    let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
    let PB := Real.exp (3*ε)*((krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi)*(1+A)^2/Real.sqrt w)
    let WB := Real.exp (3*ε)*((krCB D K L vlo vhi+264*krC₂ D K L/krKappa D vlo vhi^2)*(1+A)^2*w)
    let ST := ((P+1 : ℕ) : ℝ)^2*Real.exp (2*ε*(P : ℝ)/w^2)*(KS*Real.exp (-cS*w))
    let N := M*Real.exp (ε/w^2)*(1+OB^2*WB)
    KernelApproxLip R (N*(volume.real S*(4*VB*BB+8*D*VB)+4*(2*PB+8*RB)))
      (N*(volume.real S*(8*RB*OB+8*RB+ST)))
      (fun x => ∫ a in S, ∑' q : ℕ × ℕ,
        krInsertionCoefficient ν f w up outerUp W q.1 q.2 a*
        kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2
          (if up then 0 else w) (if up then w else 0)) := by
  classical
  obtain ⟨cS,KS,hcS,hKS,hnear⟩ := krInsertion_signed_near D θ vlo vhi hD hθ hvlo hvhi
  refine ⟨cS,KS,hcS,hKS,?_⟩
  intro K L w A ν f S hS hne hSI H hAw up outerUp P hP hPw R hR0 hRw ε M hε0 hε hM W hW hWB
  obtain ⟨a₀,ha₀⟩ := hne
  have H₀ := H a₀ ha₀
  have hεκ : ε ≤ krKappa D vlo vhi/16 := by
    have hh := hε.trans H₀.krEps_le_kappa
    linarith [H₀.kappa_pos]
  by_cases hMz : M=0
  · subst M
    dsimp only
    simp only [zero_mul]
    have hc (q : ℕ × ℕ) (a : ℝ) (ha : a ∈ S) :
        krInsertionCoefficient ν f w up outerUp W q.1 q.2 a = 0 := by
      have hmeas (l r : ℕ) (t : ℕ × ℕ × ℕ) : Measurable (W l r t a) :=
        (hW l r t).comp (show Measurable (fun g : ℕ → ℝ => (a,g)) from
          measurable_const.prodMk measurable_id)
      have hb := (krInsertion_coefficient_budget ν (H a ha) up outerUp hε0 hεκ
        (le_refl 0) hmeas (hWB a ha) q.1 q.2).2
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa only [zero_mul] using hb) (abs_nonneg _)
    refine ⟨fun _ => 0,fun _ _ _ _ => by simp,?_⟩
    apply ae_of_all
    intro x
    have hi : (∫ a in S, ∑' q : ℕ × ℕ,
        krInsertionCoefficient ν f w up outerUp W q.1 q.2 a*
          kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2
            (if up then 0 else w) (if up then w else 0)) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro a ha
      simp only [hc _ a ha,zero_mul,tsum_zero]
    simp only [hi,sub_self,abs_zero,le_refl]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMz)
  let OB := Real.exp (3*ε)*((krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi)*(1+A)*w)
  let WB := Real.exp (3*ε)*((krCB D K L vlo vhi+264*krC₂ D K L/krKappa D vlo vhi^2)*(1+A)^2*w)
  let N := M*Real.exp (ε/w^2)*(1+OB^2*WB)
  have hWB0 : 0 ≤ WB := by
    have hq := tsum_expw_weighted_krDens_bdry_pin_le ν H₀
      (b := 0) (b' := 0) (Or.inl rfl) (Or.inl rfl) hε0 hεκ
    apply le_trans (tsum_nonneg (fun n : ℕ => mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (by linarith [H₀.hw0,(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        (krDens_nonneg ν H₀.hf0 (n+1) 0 0)))) hq
  have hN : 0 < N := by dsimp [N]; positivity
  let v (q : ℕ × ℕ) (a : ℝ) := krInsertionCoefficient ν f w up outerUp W q.1 q.2 a/N
  have hv (q : ℕ × ℕ) : Measurable (v q) :=
    (measurable_krInsertionCoefficient ν H₀.hf w up outerUp hW q.1 q.2).div_const N
  have hvb (q : ℕ × ℕ) (a : ℝ) (ha : a ∈ S) : |v q a| ≤
      Real.exp (ε*(q.1 : ℝ)/w^2)*Real.exp (ε*(q.2 : ℝ)/w^2) := by
    have hmeas (l r : ℕ) (t : ℕ × ℕ × ℕ) : Measurable (W l r t a) := by
      exact (hW l r t).comp (show Measurable (fun g : ℕ → ℝ => (a,g)) from
        measurable_const.prodMk measurable_id)
    have hb := (krInsertion_coefficient_budget ν (H a ha) up outerUp hε0 hεκ hM
      hmeas (hWB a ha) q.1 q.2).2
    change |krInsertionCoefficient ν f w up outerUp W q.1 q.2 a| ≤
      (M*Real.exp (ε/w^2)*OB^2*WB)*_ at hb
    dsimp only [v]
    rw [abs_div,abs_of_pos hN,div_le_iff₀ hN]
    apply hb.trans
    have hc : M*Real.exp (ε/w^2)*OB^2*WB ≤ N := by
      dsimp [N]
      nlinarith [show 0 ≤ M*Real.exp (ε/w^2) by positivity]
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring)
  have hn := hnear ν hS ⟨a₀,ha₀⟩ hSI H hAw up hP hPw hR0 hRw hε0 hε hv hvb
  have hh := hn.const_mul N
  rw [abs_of_pos hN] at hh
  have he (x : ℝ) : N*(∫ a in S, ∑' q : ℕ × ℕ, v q a*
      kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2 (if up then 0 else w) (if up then w else 0)) =
      ∫ a in S, ∑' q : ℕ × ℕ, krInsertionCoefficient ν f w up outerUp W q.1 q.2 a*
        kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2 (if up then 0 else w) (if up then w else 0) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro a
    dsimp only
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    dsimp only [v]
    field_simp [hN.ne']
  simpa only [he] using hh

end
end PGM
