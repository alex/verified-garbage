import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Hash
import VerifiedGarbage.Proof.MlDsa.Sign.Setup

/-!
# ML-DSA signing on ARMv7: the function's contract, layout, entry and exit

Untrusted: everything here is checked by Lean. As on x86-64: the contract
the proof is written against (`signK`, which the shared contract implies),
the layout of the function's buffers (`sk`, `mu`, `rnd` read, in `r4`, `r5`,
`r6`; `scratch` and `sig` written, in `r7` and `r8`), what holds of the
state throughout (`Top`: the permissions and the stack pointer of entry, the
pointers in their registers, and the caller's `r4`–`r11` and `lr` saved in
`scratch`), the prologue (`pro_ok`), the return (`topEnd_ok`), branches on
`r11` (`ifOkElse_ok`, `ifOkElse_tr`) and sequences of pieces indexed by a
number (`seqR_ok`, `seqR_tr`).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (Saved SaveInv RestoreInv saveRegs_ok restoreRegs_ok)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- `vg_mldsa*_sign(sk = r0, mu = r1, rnd = r2, sig = r3, scratch = [sp]) -> r0`, with
`D` bytes of stack, and the leakage `signLeakT`. -/
def signK (p : Params) (D : Nat) : Contract isa where
  pre s :=
    let sk : Region := ⟨State.addr (s.gpr .r0), p.skLen⟩
    let mu : Region := ⟨State.addr (s.gpr .r1), 64⟩
    let rnd : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let sig : Region := ⟨State.addr (s.gpr .r3), p.sigLen⟩
    let scr : Region := ⟨State.addr (stackArg s 0), scrLen p⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sk, mu, rnd, args] ∧ s.wr = [sig, scr] ∧
    sk.Disjoint sig ∧ sk.Disjoint scr ∧ mu.Disjoint sig ∧ mu.Disjoint scr ∧ rnd.Disjoint sig ∧
    rnd.Disjoint scr ∧ sig.Disjoint scr ∧ sig.Disjoint args ∧ scr.Disjoint args ∧
    (belowA s.sp D).Disjoint sk ∧ (belowA s.sp D).Disjoint mu ∧ (belowA s.sp D).Disjoint rnd ∧
    (belowA s.sp D).Disjoint sig ∧ (belowA s.sp D).Disjoint scr ∧
    (s.gpr .r0).toNat + p.skLen ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + p.sigLen ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + scrLen p ≤ 2 ^ 32 ∧ D ≤ s.sp.toNat
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (State.addr (s.gpr .r0)) p.skLen)
      (bytesAt s.mem (State.addr (s.gpr .r1)) 64) (bytesAt s.mem (State.addr (s.gpr .r2)) 32)) (s'.gpr .r0)
      (bytesAt s'.mem (State.addr (s.gpr .r3)) p.sigLen)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ s₁.sp = s₂.sp ∧
    signLeakT p (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) p.skLen) (bytesAt s₁.mem (State.addr (s₁.gpr .r1)) 64)
        (bytesAt s₁.mem (State.addr (s₁.gpr .r2)) 32) =
      signLeakT p (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) p.skLen) (bytesAt s₂.mem (State.addr (s₂.gpr .r1)) 64)
        (bytesAt s₂.mem (State.addr (s₂.gpr .r2)) 32)

/-! ## The layout -/

/-- `sk`, `mu` and `rnd`. -/
abbrev sgR (p : Params) : List (Reg × Nat) := [(.r4, p.skLen), (.r5, 64), (.r6, 32)]
/-- `scratch` and `sig`. -/
abbrev sgW (p : Params) : List (Reg × Nat) := [(.r7, scrLen p), (.r8, p.sigLen)]
abbrev sgB (p : Params) : List (Reg × Nat) := sgR p ++ sgW p

/-- The pointer the function keeps in each register of `bases`, from its entry state. -/
def ptrOf (σ : State) : Reg → BitVec 32
  | .r7 => stackArg σ 0
  | .r4 => σ.gpr .r0
  | .r5 => σ.gpr .r1
  | .r6 => σ.gpr .r2
  | _ => σ.gpr .r3

theorem sgB_bases (p : Params) : ∀ b ∈ sgB p, b.1 ∈ bases := by
  intro b hb; simp only [sgB, sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- What holds throughout the function entered in `σ`. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  regs : ∀ r ∈ bases, s.gpr r = ptrOf σ r
  saved : Saved s.mem (pa s (sc oSV)) σ.gpr
  savlr : s.mem.readW (pa s (sc (oSV + 32))) 32 = σ.gpr .lr

section
variable {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ)
include hp

theorem sgLay (hsz : scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : Top σ s) : Lay D (sgR p) (sgW p) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, -, -, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩ := hp
  have e7 : s.gpr .r7 = stackArg σ 0 := h.regs .r7 (by decide)
  have e4 : s.gpr .r4 = σ.gpr .r0 := h.regs .r4 (by decide)
  have e5 : s.gpr .r5 = σ.gpr .r1 := h.regs .r5 (by decide)
  have e6 : s.gpr .r6 = σ.gpr .r2 := h.regs .r6 (by decide)
  have e8 : s.gpr .r8 = σ.gpr .r3 := h.regs .r8 (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have memw : ∀ r ∈ σ.wr, InRegions s.wr r.base r.len := fun r hr =>
    ⟨r, by rw [h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    by rw [h.sp]; exact hsp⟩
  · intro b hb
    simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      simp only [wRegs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_self, ne_eq,
        not_true_eq_false] at hne hw ⊢ <;> simp only [e4, e5, e6, e7, e8]
    all_goals first
      | exact d1 | exact d2 | exact d3 | exact d4 | exact d5 | exact d6 | exact d7
      | exact d1.symm | exact d2.symm | exact d3.symm | exact d4.symm | exact d5.symm | exact d6.symm | exact d7.symm
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8, h.sp]
    exacts [k1, k2, k3, k5, k4]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8]
    exacts [n1, n2, n3, n5, n4]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e4, e5, e6, e7, e8]
    · exact mem ⟨State.addr (σ.gpr .r0), p.skLen⟩ (List.mem_append_left _ (hrd ▸ List.mem_cons_self ..))
    · exact mem ⟨State.addr (σ.gpr .r1), 64⟩
        (List.mem_append_left _ (hrd ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact mem ⟨State.addr (σ.gpr .r2), 32⟩
        (List.mem_append_left _ (hrd ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    · exact mem ⟨State.addr (stackArg σ 0), scrLen p⟩
        (List.mem_append_right _ (hwr ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    · exact mem ⟨State.addr (σ.gpr .r3), p.sigLen⟩ (List.mem_append_right _ (hwr ▸ List.mem_cons_self ..))
  · simp only [sgW, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [e7, e8]
    · exact memw ⟨State.addr (stackArg σ 0), scrLen p⟩ (hwr ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact memw ⟨State.addr (σ.gpr .r3), p.sigLen⟩ (hwr ▸ List.mem_cons_self ..)

end

theorem pa_add (s : State) (r : Reg) (a b : Nat) : pa s (r, a + b) = pa s (r, a) + BitVec.ofNat 64 b := by
  simp only [pa]; rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- The saved registers are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool := keepB bs ws (sc oSV) 36

theorem Top.step {D : Nat} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : Top σ s)
    (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws)
    (hc : topChk (rbs ++ wbs) ws = true) : Top σ s' := by
  have hs : ∀ k < 9, s'.mem.readW (pa s' (sc (oSV + 4 * k))) 32 = s.mem.readW (pa s (sc (oSV + 4 * k))) 32 :=
    fun k hk => L.keepW hP (keepB_sub hc (by simp [oSV]) (by simp [oSV]; omega))
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.sp.trans h.sp,
    fun r hr => (hP.bs _ hr).trans (h.regs r hr), fun i hi => ?_, ?_⟩
  · have e := hs i (by omega)
    rw [pa_add, pa_add] at e
    rw [e]; exact h.saved i hi
  · have e := hs 8 (by omega)
    rw [e]; exact h.savlr

/-! ## The prologue -/

theorem pro_eq : pro = ([.ldrSp .r12 0] : List Instr) ++ Impl.MlKem.Arm.saveRegs .r12 oSV ++
    ([.str .lr .r12 (oSV + 32), .mov .r7 (.reg .r12), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1),
      .mov .r6 (.reg .r2), .mov .r8 (.reg .r3), .mov .r11 (.imm 1)] : List Instr) := rfl

theorem scrLen_ge (p : Params) : 5120 ≤ scrLen p := by
  unfold scrLen scratchWords; omega

theorem pro_ok {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ) :
    WP isa (.block pro) σ fun s => Top σ s ∧ Frame [⟨State.addr (stackArg σ 0), scrLen p⟩] σ.mem s.mem ∧
      s.gpr .r11 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n5, -⟩ := hp'
  have hge := scrLen_ge p
  have hS : (⟨State.addr (stackArg σ 0), scrLen p⟩ : Region) ∈ σ.wr := by rw [hwr]; simp
  have hA : InRegions (σ.rd ++ σ.wr) (State.addr (σ.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), by simp [stackArgAddr, Region.Contains]⟩
  rw [pro_eq, List.append_assoc, WP.block_append_iff]
  have hl : WP isa (.block [.ldrSp .r12 0]) σ fun s₁ => s₁.gpr .r12 = stackArg σ 0 ∧
      (∀ r, r ≠ .r12 → s₁.gpr r = σ.gpr r) ∧ s₁.mem = σ.mem ∧ s₁.rd = σ.rd ∧ s₁.wr = σ.wr ∧ s₁.sp = σ.sp := by
    run_block [hA, show (0 : Nat) < 4096 by decide]
    exact ⟨by simp [stackArg, stackArgAddr], fun r hr => by simp [hr], trivial⟩
  refine WP.mono hl fun s₁ ⟨h12, hr, hm, hrd₁, hwr₁, hsp₁⟩ => ?_
  rw [WP.block_append_iff]
  have wS : ∀ o n, o + n ≤ scrLen p → InRegions s₁.wr (State.addr (stackArg σ 0) + BitVec.ofNat 64 o) n :=
    fun o n h => by rw [hwr₁]; exact inRegions_sub ⟨_, hS, Region.contains_self _ _⟩ h (by omega)
  refine WP.mono (saveRegs_ok .r12 (off := 840) (by decide) (by rw [h12]; omega) fun i hi => by
    rw [h12, BitVec.add_assoc, ← BitVec.ofNat_add]; exact wS _ _ (by omega)) fun s₂ h₂ => ?_
  have g12 : s₂.gpr .r12 = stackArg σ 0 := by rw [h₂.gpr, h12]
  have e872 : State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSV + 32)) =
      State.addr (stackArg σ 0) + BitVec.ofNat 64 872 := by
    rw [g12]; exact addr_add (by simp only [oSV]; omega)
  have i872 : InRegions s₂.wr (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (oSV + 32))) 4 := by
    rw [e872, h₂.wr]; exact wS _ _ (by omega)
  have o1 : oSV + 32 < 4096 := by decide
  run_block [i872, o1]
  have g : ∀ r, r ≠ .r12 → s₂.gpr r = σ.gpr r := fun r hr' => by rw [h₂.gpr, hr r hr']
  have hne : ∀ i < 8, Impl.MlKem.Arm.savedRegs.getD i Reg.r4 ≠ Reg.r12 := by decide
  rw [e872]
  refine ⟨⟨by simp [h₂.rd, hrd₁], by simp [h₂.wr, hwr₁], by simp [h₂.sp, hsp₁], fun r hr => ?_, fun i hi => ?_, ?_⟩,
    ?_, trivial⟩
  · simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [ptrOf, g12, g]
  · simp only [pa, ite_true, ite_false, reduceCtorEq, g12]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Mem.readW_writeW_sep (Offset.sep _ (by simp only [oSV]; omega)
      (by omega) (by omega)) (by decide)]
    have := h₂.saved i hi
    rw [h12, BitVec.add_assoc, ← BitVec.ofNat_add] at this
    rw [show oSV = 840 from rfl, this, hr _ (hne i hi)]
  · simp only [pa, ite_true, ite_false, reduceCtorEq, g12]
    rw [show oSV + 32 = 872 from rfl, Mem.readW_writeW_self32, g _ (by decide)]
  · have f₁ := h₂.frame
    rw [h12, hm] at f₁
    refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.sub_base _ (by omega)

/-! ## The return -/

theorem topEnd_ok {σ s : State} (h : Top σ s) (hin : InRegions (s.rd ++ s.wr) (pa s (sc oSV)) 36)
    (hfit : (s.gpr .r7).toNat + 876 ≤ 2 ^ 32) :
    WP isa (.block Impl.MlKem.Arm.topEnd) s fun s' => s'.gpr .r0 = s.gpr .r11 ∧
      (∀ r ∈ preserved, s'.gpr r = σ.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp := by
  rw [Impl.MlKem.Arm.topEnd, List.append_assoc, WP.block_append_iff]
  have hk : WP isa (.block [.mov .r0 (.reg .r11), .mov .r3 (.reg .r7)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r11 ∧ s'.gpr .r3 = s.gpr .r7 ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
    run_block []
  refine WP.mono hk fun s₁ ⟨r0, r3, m₁, rd₁, wr₁, sp₁⟩ => ?_
  rw [WP.block_append_iff]
  have e3 : State.addr (s₁.gpr .r3) + BitVec.ofNat 64 840 = pa s (sc oSV) := by rw [r3]; rfl
  refine WP.mono (restoreRegs_ok .r3 (by decide) (off := 840) (by decide)
    (by rw [r3]; omega) (g := σ.gpr) (by rw [e3, m₁]; exact h.saved)
    fun i hi => by
      rw [e3, rd₁, wr₁]
      exact inRegions_sub hin (by omega) (by decide))
    fun s₂ h₂ => ?_
  have g3 : s₂.gpr .r3 = s.gpr .r7 := by rw [h₂.other .r3 (by decide), r3]
  have e872 : State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32)) = pa s (sc (oSV + 32)) := by
    rw [g3]; exact addr_add (by simp only [Impl.MlKem.Arm.oSave]; omega)
  have i12 : InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 4 := by
    rw [e872, h₂.rd, h₂.wr, rd₁, wr₁, pa_add]
    exact inRegions_sub hin (by omega) (by decide)
  have ho : Impl.MlKem.Arm.oSave + 32 < 4096 := by decide
  have hl : WP isa (.block [.ldr .lr .r3 (Impl.MlKem.Arm.oSave + 32)]) s₂ fun s' =>
      s'.gpr .lr = s₂.mem.readW (State.addr (s₂.gpr .r3 + BitVec.ofNat 32 (Impl.MlKem.Arm.oSave + 32))) 32 ∧
      (∀ r, r ≠ .lr → s'.gpr r = s₂.gpr r) ∧ s'.mem = s₂.mem ∧ s'.sp = s₂.sp := by
    run_block [i12, ho, and_self, and_true]
    exact ⟨trivial, fun r hr => by simp [hr]⟩
  refine WP.mono hl fun s' ⟨lr, rr, m, sp⟩ => ⟨?_, fun r hr => ?_, ?_, ?_⟩
  · rw [rr .r0 (by decide), h₂.other .r0 (by decide), r0]
  · by_cases e : r = .lr
    · subst e
      rw [lr, e872, h₂.mem, m₁]; exact h.savlr
    · have hs : ∀ r ∈ preserved, r ≠ .lr → ∃ i < 8, Impl.MlKem.Arm.savedRegs.getD i .r4 = r := by decide
      obtain ⟨i, hi, rfl⟩ := hs r hr e
      rw [rr _ e]; exact h₂.loaded i hi
  · rw [m, h₂.mem, m₁]
  · rw [sp, h₂.sp, sp₁]

/-! ## Branches on `r11` -/

/-- The comparison of `r11` with 0 writes only the flags. -/
theorem cmp11_ok (s : State) (D : Nat) :
    WP isa (.block [.cmp .r11 (.imm 0)]) s fun s₁ => PPostB D s s₁ [] ∧ CS s s₁ ∧ s₁.mem = s.mem ∧
      s₁.z = (s.gpr .r11 == 0) := by
  have h : WP isa (.block [.cmp .r11 (.imm 0)]) s fun s₁ => s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.sp = s.sp ∧ s₁.z = (s.gpr .r11 == 0) := by
    run_block []
    simp
  refine WP.mono h fun s₁ ⟨g, m, rd, wr, sp, z⟩ => ?_
  have hcs : CS s s₁ := fun r _ _ => by rw [g]
  exact ⟨PostB.of_cs hcs rd wr sp (by rw [m]; exact Frame.refl _ _), hcs, m, z⟩

theorem ifOkElse_ok {D : Nat} {t e : Prog isa} {s : State} {Q : State → Prop}
    (ht : ∀ s₁, PPostB D s s₁ [] → CS s s₁ → s₁.mem = s.mem → s.gpr .r11 ≠ 0 → WP isa t s₁ Q)
    (he : ∀ s₁, PPostB D s s₁ [] → CS s s₁ → s₁.mem = s.mem → s.gpr .r11 = 0 → WP isa e s₁ Q) :
    WP isa (ifOkElse t e) s Q := by
  unfold ifOkElse
  refine WP.seq (WP.mono (cmp11_ok s D) fun s₁ ⟨hP, hcs, hm, hz⟩ => ?_)
  refine WP.ite (M := isa) (!(s.gpr .r11 == 0)) (show some (!s₁.z) = _ by rw [hz]) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP hcs hm (by simpa using hb)
  · exact he s₁ hP hcs hm (by simpa using hb)

theorem ifOkElse_tr {D : Nat} {t e : Prog isa} {P Q : State → State → Prop}
    (hq : ∀ x y, P x y → x.gpr .r11 = y.gpr .r11)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (PPostB D x₀ x [] ∧ CS x₀ x ∧ x.mem = x₀.mem) ∧
      (PPostB D y₀ y [] ∧ CS y₀ y ∧ y.mem = y₀.mem) ∧ x₀.gpr .r11 ≠ 0) t Q)
    (he : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (PPostB D x₀ x [] ∧ CS x₀ x ∧ x.mem = x₀.mem) ∧
      (PPostB D y₀ y [] ∧ CS y₀ y ∧ y.mem = y₀.mem) ∧ x₀.gpr .r11 = 0) e Q) :
    RelCT isa P (ifOkElse t e) Q := by
  unfold ifOkElse
  refine RelCT.seq (postDep (block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => (PPostB D x x₁ [] ∧ CS x x₁ ∧ x₁.mem = x.mem) ∧ x₁.z = (x.gpr .r11 == 0))
    (fun x y _ => ⟨WP.mono (cmp11_ok x D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩,
      WP.mono (cmp11_ok y D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩)
    (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      ((PPostB D x₀ x₁ [] ∧ CS x₀ x₁ ∧ x₁.mem = x₀.mem) ∧ x₁.z = (x₀.gpr .r11 == 0)) ∧
      ((PPostB D y₀ y₁ [] ∧ CS y₀ y₁ ∧ y₁.mem = y₀.mem) ∧ y₁.z = (y₀.gpr .r11 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩
    show some (!x₁.z) = some (!y₁.z)
    rw [hx, hy, hq x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : some (!x₁.z) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono he (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : some (!x₁.z) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))

end VG.Proof.MlDsa.Arm.Sign
