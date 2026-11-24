import PLAStochastic.Index.GEP.Kernel.Insertion.ScaleArithmetic

/-! # The actual near insertion at its original width scale -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

set_option maxHeartbeats 1600000 in
/-- Class-uniform AL scale for the actual exterior-weighted insertion.
After a reward envelope of order M/C and C of order w², the Lipschitz
constant has the required M√w scale, with a fixed near-window power. -/
theorem krInsertion_coefficient_width_scale (D θ vlo vhi K L : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {w A : ℝ}
      (_hw : 96 ≤ w) {S : Set ℝ} (_hS : MeasurableSet S) (_hne : S.Nonempty)
      (_hSI : S ⊆ Ioo (1/2 : ℝ) 2)
      (_H : ∀ a ∈ S, KrBand D θ vlo vhi K L ν f w A a 1 a)
      (_hAw : A ≤ w) (up outerUp : Bool) {R : ℝ} (_hR0 : 0 ≤ R) (_hRw : R ≤ w/8)
      {ε M : ℝ} (_hε0 : 0 ≤ ε) (_hε : ε ≤ krEps D vlo vhi) (_hM : 0 ≤ M)
      {W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ}
      (_hW : ∀ l r t, Measurable (fun p : ℝ × (ℕ → ℝ) => W l r t p.1 p.2))
      (_hWB : ∀ a ∈ S, ∀ l r t g, krInsertionOuter w outerUp l r t a g ≠ 0 →
        |W l r t a g| ≤ M*Real.exp (ε*((t.1 : ℝ)+l+r+t.2.1+t.2.2+2)/w^2)),
    KernelApproxLip R (C*M*(1+A)^7*w^2*Real.sqrt w*(1+Real.log w))
      (C*M*(1+A)^7*w^4*Real.exp (-c*w))
      (fun x => ∫ a in S, ∑' q : ℕ × ℕ,
        krInsertionCoefficient ν f w up outerUp W q.1 q.2 a*
        kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2
          (if up then 0 else w) (if up then w else 0)) := by
  obtain ⟨cS,KS,hcS,hKS,hnear⟩ := krInsertion_coefficient_near D θ vlo vhi hD hθ hvlo hvhi
  let c := min cS ((1-kBVClassRho D vlo vhi)/192)
  have hcc := kBVClass_constants hD hvlo hvhi
  have hc : 0 < c := lt_min hcS (by linarith [hcc.2.1])
  let Cb := krCG D K L vlo vhi+4*krC₄ D K L/krKappa D vlo vhi
  let Co := krCO D K L vlo vhi+4*krC₃ D K L/krKappa D vlo vhi
  let Cp := krCP D θ K L vlo vhi+12*krC₂ D K L/krKappa D vlo vhi
  let Cw := krCB D K L vlo vhi+264*krC₂ D K L/krKappa D vlo vhi^2
  obtain ⟨T,hT,hDT,heT,hcT,hVT,hRT,hBT,hOT,hPT,hWT,hSTT⟩ :=
    krInsertion_majorant_exists D (krCV D K L vlo vhi) (krCR D K L vlo vhi) Cb Co Cp Cw KS c
  have hT0 : 0 < T := by linarith
  refine ⟨c,128*T^6,hc,by positivity,?_⟩
  intro ν f w A hw S hS hne hSI H hAw up outerUp R hR0 hRw ε M hε0 hε hM W hW hWB
  obtain ⟨a₀,ha₀⟩ := hne
  have H₀ := H a₀ ha₀
  have hw1 : 1 ≤ w := by linarith
  have hA := H₀.hA
  have hU : 1 ≤ 1+A := by linarith
  have hκ := H₀.kappa_pos
  have hC₁ := krC₁_nonneg (K := K) (L := L) H₀.hD0 H₀.hK H₀.hL0.le
  have hC₂ := krC₂_nonneg (K := K) (L := L) H₀.hD0 H₀.hK H₀.hL0.le
  have hCpin := krCpin_nonneg (K := K) H₀.hD0 H₀.hL0.le
  have hCb : 0 ≤ Cb := by dsimp only [Cb,krCG,krC₄]; positivity
  have hCo : 0 ≤ Co := by
    have hK := H₀.hK
    dsimp only [Co,krCO,krC₃]
    positivity
  have hCp : 0 ≤ Cp := by dsimp only [Cp,krCP]; positivity
  have hCw : 0 ≤ Cw := by dsimp only [Cw,krCB]; positivity
  have hε1 : ε ≤ 1 := by
    have he := hε.trans H₀.krEps_le_kappa
    linarith [H₀.kappa_le_one]
  have he3 : Real.exp (3*ε) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by linarith)
  have he5 : Real.exp (5*ε) ≤ Real.exp 5 := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨hP,hPw,_⟩ := krInsertion_cutoff hw
  have hn := hnear ν hS ⟨a₀,ha₀⟩ hSI H hAw up outerUp hP hPw hR0 hRw hε0 hε hM hW hWB
  let VB := 2*Real.exp (3*ε)*krCV D K L vlo vhi*(1+A)*(Real.sqrt w/krFourthRoot (⌊w/8⌋₊ : ℝ)+1)
  let RB := 2*Real.exp (5*ε)*krCR D K L vlo vhi*(1+A)*((1+kBVClassRho D vlo vhi)/2)^(⌊w/8⌋₊/3-1)
  let BB := Real.exp (3*ε)*(Cb*(1+A)*(1+Real.log w))
  let OB := Real.exp (3*ε)*(Co*(1+A)*w)
  let PB := Real.exp (3*ε)*(Cp*(1+A)^2/Real.sqrt w)
  let WB := Real.exp (3*ε)*(Cw*(1+A)^2*w)
  let ST := ((⌊w/8⌋₊+1 : ℕ) : ℝ)^2*Real.exp (2*ε*(⌊w/8⌋₊ : ℝ)/w^2)*(KS*Real.exp (-cS*w))
  have hCV := H₀.krCV_nonneg
  have hCR := H₀.krCR_nonneg
  have hμ : volume.real S ≤ 2*(1+A)/w :=
    (krInsertion_window_measure H₀.hw0 hA (fun a ha => (H a ha).haA)).trans (by gcongr; linarith)
  have hroot : krFourthRoot w ≤ Real.sqrt w := by
    apply Real.sqrt_le_self_iff.mpr
    right
    exact (Real.le_sqrt (by norm_num) H₀.hw0.le).2 (by norm_num; linarith)
  have hroot0 := krFourthRoot_nonneg w
  have hrootP0 := krFourthRoot_nonneg (⌊w/8⌋₊ : ℝ)
  have hratio0 : 0 ≤ Real.sqrt w/krFourthRoot (⌊w/8⌋₊ : ℝ)+1 := by positivity
  have hlog0 := Real.log_nonneg hw1
  have hrho0 : 0 ≤ (1+kBVClassRho D vlo vhi)/2 := by linarith [hcc.1]
  have hpow0 : 0 ≤ ((1+kBVClassRho D vlo vhi)/2)^(⌊w/8⌋₊/3-1) := pow_nonneg hrho0 _
  have hVB : VB ≤ T*(1+A)*Real.sqrt w := by
    calc
      _ ≤ 2*Real.exp 3*krCV D K L vlo vhi*(1+A)*(3*krFourthRoot w) := by
        dsimp only [VB]
        exact mul_le_mul (by gcongr) (krInsertion_cutoff_fourth hw) hratio0 (by positivity)
      _ = (6*Real.exp 3*krCV D K L vlo vhi)*(1+A)*krFourthRoot w := by ring
      _ ≤ _ := by gcongr
  have hBB : BB ≤ T*(1+A)*(1+Real.log w) := by
    calc
      _ = (Real.exp (3*ε)*Cb)*(1+A)*(1+Real.log w) := by dsimp only [BB]; ring
      _ ≤ (Real.exp 3*Cb)*(1+A)*(1+Real.log w) := by gcongr
      _ ≤ _ := by gcongr
  have hOB : OB ≤ T*(1+A)*w := by
    calc
      _ = (Real.exp (3*ε)*Co)*(1+A)*w := by dsimp only [OB]; ring
      _ ≤ (Real.exp 3*Co)*(1+A)*w := by gcongr
      _ ≤ _ := by gcongr
  have hPB : PB ≤ T*(1+A)^2/Real.sqrt w := by
    calc
      _ = (Real.exp (3*ε)*Cp)*(1+A)^2/Real.sqrt w := by dsimp only [PB]; ring
      _ ≤ (Real.exp 3*Cp)*(1+A)^2/Real.sqrt w := by gcongr
      _ ≤ _ := by gcongr
  have hWB' : WB ≤ T*(1+A)^2*w := by
    calc
      _ = (Real.exp (3*ε)*Cw)*(1+A)^2*w := by dsimp only [WB]; ring
      _ ≤ (Real.exp 3*Cw)*(1+A)^2*w := by gcongr
      _ ≤ _ := by gcongr
  have hgeo : ((1+kBVClassRho D vlo vhi)/2)^(⌊w/8⌋₊/3-1) ≤ Real.exp (-c*w) := by
    apply (krInsertion_cutoff_geometric hw (by linarith [hcc.1]) (by linarith [hcc.2.1])).trans
    apply Real.exp_le_exp.mpr
    have hh : c ≤ (1-kBVClassRho D vlo vhi)/192 := min_le_right _ _
    nlinarith
  have hRB : RB ≤ T*(1+A)*Real.exp (-c*w) := by
    calc
      _ ≤ (2*Real.exp 5*krCR D K L vlo vhi)*(1+A)*Real.exp (-c*w) := by dsimp only [RB]; gcongr
      _ ≤ _ := by gcongr
  have hExp : Real.exp (-cS*w) ≤ Real.exp (-c*w) :=
    Real.exp_le_exp.mpr (by nlinarith [show c ≤ cS from min_le_left _ _])
  have hST : ST ≤ T*w^2*Real.exp (-c*w) := by
    calc
      _ ≤ (w^2*Real.exp 1)*(KS*Real.exp (-c*w)) := by
        dsimp only [ST]
        exact mul_le_mul (krInsertion_cutoff_short_factor hw hε0 hε1)
          (mul_le_mul_of_nonneg_left hExp hKS.le) (by positivity) (by positivity)
      _ = (Real.exp 1*KS)*w^2*Real.exp (-c*w) := by ring
      _ ≤ _ := by gcongr
  have he : Real.exp (ε/w^2) ≤ T := by
    apply (Real.exp_le_exp.mpr ?_).trans heT
    exact (div_le_one (sq_pos_of_pos H₀.hw0)).2 (by nlinarith)
  have hb := krInsertion_algebra hw1 hU hT hM (measureReal_nonneg) hμ H₀.hD0 hDT
    (show 0 ≤ VB by dsimp [VB]; positivity)
    (show 0 ≤ BB by dsimp only [BB]; positivity [Real.log_nonneg hw1])
    (show 0 ≤ OB by dsimp only [OB]; positivity)
    (show 0 ≤ PB by dsimp only [PB]; positivity)
    (show 0 ≤ RB by dsimp only [RB]; positivity)
    (show 0 ≤ WB by dsimp only [WB]; positivity)
    (show 0 ≤ ST by dsimp only [ST]; positivity)
    (Real.exp_nonneg _) hVB hBB hOB hPB hRB hWB' hST he
    (krInsertion_exp_le_trace hw1 hc hcT)
  apply hn.mono
  · exact hb.1.trans_eq (by ring)
  · apply hb.2.trans
    have ht : 68*M*T^6*(1+A)^7*w^4*Real.exp (-c*w) ≤
        128*M*T^6*(1+A)^7*w^4*Real.exp (-c*w) := by gcongr; norm_num
    exact ht.trans_eq (by ring)

end
end PGM
