import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Piece
import VerifiedGarbage.Proof.MlDsa.KeyGen.Good

/-!
# ML-DSA key generation on 32-bit ARM: what holds throughout, and the prologue

What holds of the state throughout (`KC`: the layout, the permissions and
stack pointer of the entry state, our caller's registers saved in `scratch`,
and the seed `ξ`), which a part keeps if it writes apart from the saved
registers and the seed (`kcChk`); the pieces of key generation (`KPiece`); and
the prologue, which saves our caller's registers and keeps the pointers
(`pro_piece`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak)
open VG.Spec.Sha3 (bytesAt)

/-! ## The seed and what it gives -/

/-- `ξ`. -/
abbrev xiOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (pSeed σ)) 32
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).1
abbrev rho'Of (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.1
abbrev kOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.2

/-- The public data of `keyGenContract`. -/
def kgPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ pSeed σ₁ = pSeed σ₂ ∧ pPk σ₁ = pPk σ₂ ∧ pSk σ₁ = pSk σ₂ ∧ pScr σ₁ = pScr σ₂ ∧
    keyGenLeak p (xiOf σ₁) = keyGenLeak p (xiOf σ₂)

/-- The pieces of key generation. -/
abbrev KPiece (p : Params) (STK : Nat) := Piece (Pre p STK) (kgPub p)

/-- Two runs of a key generation with public data that agree have the same layout. -/
theorem lay_pub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h : kgPub p σ₁ σ₂) : lay p STK σ₁ = lay p STK σ₂ := by
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := h
  simp only [lay, pSeed, pPk, pSk, pScr] at *
  rw [e0, e1, e2, e3, e4]

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (STK : Nat) (σ s : State) : Prop where
  site : Site (lay p STK σ) kWb STK s
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  sav : Saved s.mem ((lay p STK σ).A 0 840) σ.gpr
  lr : s.mem.readW ((lay p STK σ).A 0 872) 32 = σ.gpr .lr
  xi : bytesAt s.mem ((lay p STK σ).A 2 0) 32 = xiOf σ

theorem xi_eq (p : Params) (STK : Nat) (σ : State) : bytesAt σ.mem ((lay p STK σ).A 2 0) 32 = xiOf σ := by
  simp only [Lay.A, add_ofNat_zero]; rfl

/-- A part that writes the regions `W` keeps `KC`. -/
def kcChk (p : Params) (STK : Nat) (W : List (Nat × Nat × Nat)) : Bool :=
  sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, 840, 36) W &&
    sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (2, 0, 32) W

theorem KC.keep {p : Params} {STK : Nat} {σ s s' : State} (h : KC p STK σ s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((lay p STK σ).RL W) s s') (hc : kcChk p STK W = true) : KC p STK σ s' := by
  simp only [kcChk, Bool.and_eq_true] at hc
  have hL := h.site.ok
  have hd : ∀ r ∈ (lay p STK σ).RL W, ((lay p STK σ).R 0 840 36).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact disjW hL (List.all_eq_true.mp hc.1 w hw) (.inl (by decide))
  have hd2 : ∀ r ∈ (lay p STK σ).RL W, ((lay p STK σ).R 2 0 32).Disjoint r :=
    fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      have hs := List.all_eq_true.mp hc.2 w hw
      refine disjW' hL hs (.inr ?_)
      have hb : w.1 < 5 := by
        simp only [sepB, Bool.and_eq_true, decide_eq_true_eq, List.length_cons, List.length_nil] at hs
        exact hs.1.1.1.2
      rcases (by omega : w.1 = 0 ∨ w.1 = 1 ∨ w.1 = 2 ∨ w.1 = 3 ∨ w.1 = 4) with e | e | e | e | e <;> rw [e]
      · exact .inl (by decide)
      · exact .inl (by decide)
      · exact .inr rfl
      · exact .inl (by decide)
      · exact .inl (by decide)
  refine ⟨h.site.kept hk, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_⟩
  · rw [hk.frame.readW (r := (lay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW (r := (lay p STK σ).R 0 840 36) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.lr
  · rw [Proof.MlKem.bytesAt_frame hk.frame hd2 (by decide)]; exact h.xi

end VG.Proof.MlDsa.Arm.KeyGen

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds keyGenLeak)
open VG.Spec.Sha3 (bytesAt)

/-! ## The prologue -/

theorem pro_ok {p : Params} (hF : PFacts p) {STK : Nat} (hSTK : 8 ≤ STK) {σ : State} (hp : Pre p STK σ) :
    WP isa (.block pro) σ fun s => KC p STK σ s ∧ s.gpr .r11 = 1 := by
  have hL := lay_ok hp
  have fc := hp.f_c
  obtain ⟨hs1, -⟩ := hF.scr
  have w0 : (lay p STK σ).buf 0 ∈ σ.wr := by
    rw [show (lay p STK σ).buf 0 = regA (pScr σ) (scrLen p) from rfl, hp.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have eA : ∀ o, (lay p STK σ).A 0 o = State.addr (σ.gpr .r3) + BitVec.ofNat 64 o := fun o => rfl
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions σ.wr ((lay p STK σ).A 0 o) n := fun {o n} h =>
    Lay.covers (o := o) (l := n) w0 (by rw [lay_size0]; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [pro, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by omega) fc) fun i hi => by
    rw [add_ofNat_add, ← eA]; exact wS (o := 840 + 4 * i) (n := 4) (by omega)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = pScr σ := by rw [h₁.gpr]
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = (lay p STK σ).A 0 872 := by
    rw [g3]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have o1 : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  have e1 : encodable (1 : BitVec 32) = true := by decide
  run_block [i872, o1, e1]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((lay p STK σ).A 0 872) v).readW
      ((lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by rw [eA] at h1 h2; bv_omega) (by decide)
  have fr : Frame [(lay p STK σ).R 0 840 36] σ.mem (s₁.mem.writeW ((lay p STK σ).A 0 872) (s₁.gpr .lr)) := by
    refine (h₁.frame.sub fun r hr => ⟨(lay p STK σ).R 0 840 36, List.mem_singleton_self _, ?_⟩).writeW
      (r := (lay p STK σ).R 0 840 36) (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      intro x hx; simp only [Region.Contains, eA] at hx ⊢; bv_omega
    · simp only [Region.Contains, eA]; bv_omega
  refine ⟨⟨⟨hL, rfl, by decide, by decide, by rw [lay_size0]; omega, rfl,
    show σ.sp - BitVec.ofNat 32 STK = s₁.sp - BitVec.ofNat 32 STK by rw [h₁.sp], hSTK,
    by rw [h₁.sp]; exact hp.stk, ?_, ?_, ?_, ?_, fun i hi hi1 => ?_, fun i hi hi1 => ?_⟩, h₁.rd, h₁.wr, h₁.sp,
    fun i hi => ?_, ?_, ?_⟩, ?_⟩
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · show _ ∈ s₁.wr
    rw [h₁.wr, hp.wr]
    simp only [kWb, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp [Lay.buf, lay]
    · exact absurd rfl hi1
    · simp [Lay.buf, lay]
    · simp [Lay.buf, lay]
  · show _ ∈ s₁.rd ++ s₁.wr
    rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
    rcases (by omega : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl <;> simp [Lay.buf, lay]
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, ne1 i hi]
    exact h₁.saved i hi
  · show (s₁.mem.writeW _ _).readW _ _ = _
    rw [e872, show (lay p STK σ).A 0 872 = (lay p STK σ).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], Mem.readW_writeW_self32, h₁.gpr]
  · show bytesAt (s₁.mem.writeW _ _) _ _ = _
    rw [e872, ← xi_eq p STK σ]
    exact Proof.MlKem.bytesAt_frame fr (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact disjW' (i := 2) (o := 0) (l := 32) (j := 0) (o' := 840) (l' := 36) hL (by lsep hF)
        (.inr (.inl (by decide)))) (by decide)
  · trivial

theorem pro_piece {p : Params} (hF : PFacts p) {STK : Nat} (hSTK : 8 ≤ STK) :
    KPiece p STK (fun σ s => s = σ) (fun σ s => KC p STK σ s ∧ s.gpr .r11 = 1) (.block pro) :=
  ⟨fun σ s hp hs => by subst hs; exact pro_ok hF hSTK hp,
    Sample.taint_block [.r0, .r1, .r2, .r3] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      obtain ⟨-, e0, e1, e2, e3, -⟩ := pub
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [e0, e1, e2, e3]) (by taint_decide)⟩

end VG.Proof.MlDsa.Arm.KeyGen
