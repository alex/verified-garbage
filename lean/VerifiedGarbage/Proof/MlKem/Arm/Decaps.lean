import VerifiedGarbage.Proof.MlKem.Arm.Encrypt
import VerifiedGarbage.Proof.MlKem.Arm.CmpSel

/-!
# ML-KEM-768 on 32-bit ARM: `vg_mlkem768_decaps`, correctness

Untrusted: everything here is checked by Lean. The buffers of the function
(`lay`): `scratch`, the stack below the stack pointer, `dk` and `key`; `c`,
which may overlap `dk`, is only read by its copy into `scratch`, with a
layout of its own (`layC`). What every phase keeps (`DEnv`), and the phases:
the setup, `c` copied, K-PKE.Decrypt into `m'`, `G(m' ‖ h)` into `K' ‖ r'`,
`J(z ‖ c)` into `K̄`, the re-encryption `c'` (`Enc.encrypt_ok`), the
comparison of `c` and `c'`, and the selection of `K'` or `K̄` into `key`.
-/

namespace VG.Proof.MlKem.Arm.Decaps

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.Arm.Enc

section
variable (s₀ : State)

def pDk : BitVec 32 := s₀.gpr .r0
def pC : BitVec 32 := s₀.gpr .r1
def pKey : BitVec 32 := s₀.gpr .r2
def pScr : BitVec 32 := s₀.gpr .r3

/-- The buffers: `scratch`, the 8 bytes below the stack pointer, `dk` and `key`. -/
def lay : Lay := ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 32 8, pDk s₀, pKey s₀].getD i 0, [32768, 8, 2400, 32]⟩

/-- The buffers of the copy of `c`: `scratch`, the stack and `c`. -/
def layC : Lay := ⟨fun i => [pScr s₀, s₀.sp - BitVec.ofNat 32 8, pC s₀].getD i 0, [32768, 8, 1088]⟩

end

theorem lay_sizes (s₀ : State) : (lay s₀).sizes = [32768, 8, 2400, 32] := rfl
theorem layC_sizes (s₀ : State) : (layC s₀).sizes = [32768, 8, 1088] := rfl
theorem lay_ptr0 (s₀ : State) : (lay s₀).ptr 0 = pScr s₀ := rfl
theorem layC_ptr0 (s₀ : State) : (layC s₀).ptr 0 = pScr s₀ := rfl

/-- Decides a fact about the offsets in the buffers. -/
macro "ddecide" : tactic => `(tactic| first | decide | (simp only [lay_sizes]; decide))

/-- The precondition of the contract. -/
structure Pre (s : State) : Prop where
  sp8 : 8 ≤ s.sp.toNat
  spf : s.sp.toNat ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (pDk s), 2400⟩, ⟨State.addr (pC s), 1088⟩]
  wr : s.wr = [⟨State.addr (pKey s), 32⟩, ⟨State.addr (pScr s), 32768⟩]
  d_dk_key : (⟨State.addr (pDk s), 2400⟩ : Region).Disjoint ⟨State.addr (pKey s), 32⟩
  d_dk_scr : (⟨State.addr (pDk s), 2400⟩ : Region).Disjoint ⟨State.addr (pScr s), 32768⟩
  d_c_key : (⟨State.addr (pC s), 1088⟩ : Region).Disjoint ⟨State.addr (pKey s), 32⟩
  d_c_scr : (⟨State.addr (pC s), 1088⟩ : Region).Disjoint ⟨State.addr (pScr s), 32768⟩
  d_key_scr : (⟨State.addr (pKey s), 32⟩ : Region).Disjoint ⟨State.addr (pScr s), 32768⟩
  b_dk : (below s 8).Disjoint ⟨State.addr (pDk s), 2400⟩
  b_c : (below s 8).Disjoint ⟨State.addr (pC s), 1088⟩
  b_key : (below s 8).Disjoint ⟨State.addr (pKey s), 32⟩
  b_scr : (below s 8).Disjoint ⟨State.addr (pScr s), 32768⟩
  f_dk : (pDk s).toNat + 2400 ≤ 2 ^ 32
  f_c : (pC s).toNat + 1088 ≤ 2 ^ 32
  f_key : (pKey s).toNat + 32 ≤ 2 ^ 32
  f_scr : (pScr s).toNat + 32768 ≤ 2 ^ 32

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem stack_eq : (⟨State.addr (s₀.sp - BitVec.ofNat 32 8), 8⟩ : Region) = below s₀ 8 := by
  rw [addr_sub hp.sp8]

theorem stack_fit : (s₀.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32 := by
  have := hp.sp8; have := s₀.sp.isLt; bv_omega

theorem lay_ok : (lay s₀).Ok := by
  have es := stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [lay, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_dk
    · exact hp.f_key
  · simp only [lay, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;>
    simp only [lay, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_scr.symm
    · exact hp.d_dk_scr.symm
    · exact hp.d_key_scr.symm
    · rw [es]; exact hp.b_dk
    · rw [es]; exact hp.b_key
    · exact hp.d_dk_key

theorem layC_ok : (layC s₀).Ok := by
  have es := stack_eq hp
  refine Lay.ok_of (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · simp only [layC, List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact hp.f_scr
    · exact stack_fit hp
    · exact hp.f_c
  · simp only [layC, List.length_cons, List.length_nil] at hi hj
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl <;>
    simp only [layC, Lay.size, List.getD_cons_zero, List.getD_cons_succ] <;>
    first | omega | skip
    · rw [es]; exact hp.b_scr.symm
    · exact hp.d_c_scr.symm
    · rw [es]; exact hp.b_c

end

/-- What every phase keeps: `scratch`, our caller's registers and `key` in
`scratch`, and `dk`. -/
structure DEnv (s₀ s : State) : Prop where
  ctx : Ctx (lay s₀) s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  sav : Saved s.mem ((lay s₀).A 0 840) s₀.gpr
  savlr : s.mem.readW ((lay s₀).A 0 872) 32 = s₀.gpr .lr
  key : s.mem.readW ((lay s₀).A 0 876) 32 = pKey s₀
  dk : bytesAt s.mem ((lay s₀).A 2 0) 2400 = bytesAt s₀.mem ((lay s₀).A 2 0) 2400

/-- A region the phases may change: apart from the saved registers, `key`'s pointer and `dk`. -/
def okW (w : Nat × Nat × Nat) : Bool := sepB [32768, 8, 2400, 32] (0, 840, 40) w &&
  sepB [32768, 8, 2400, 32] (2, 0, 2400) w

theorem DEnv.keep {s₀ s s' : State} (hp : Pre s₀) (h : DEnv s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (hk : KeptX xs ((lay s₀).RL W) s s') (h7 : Reg.r7 ∉ xs) (hW : W.all okW = true) : DEnv s₀ s' := by
  have hL := lay_ok hp
  have h1 : sepAll (lay s₀).sizes (0, 840, 40) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.1
  have h2 : sepAll (lay s₀).sizes (2, 0, 2400) W = true :=
    List.all_eq_true.mpr fun w hw => by
      have := List.all_eq_true.mp hW w hw; simp only [okW, Bool.and_eq_true] at this; exact this.2
  have hd := Lay.disjAll hL h1
  have c872 : (Lay.R (lay s₀) 0 840 40).Contains ((lay s₀).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  have c876 : (Lay.R (lay s₀) 0 840 40).Contains ((lay s₀).A 0 876) 4 := by
    simp only [Region.Contains]; bv_omega
  refine ⟨hk.ctx h7 h.ctx, hk.rd.trans h.rd, hk.wr.trans h.wr, hk.sp.trans h.sp, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [hk.frame.readW (r := Lay.R (lay s₀) 0 840 40) (by simp only [Region.Contains]; bv_omega) hd (by decide)]
    exact h.sav i hi
  · rw [hk.frame.readW c872 hd (by decide)]; exact h.savlr
  · rw [hk.frame.readW c876 hd (by decide)]; exact h.key
  · rw [Lay.bytes_keep hL hk.frame h2 (by decide)]; exact h.dk

theorem buf_wr {s₀ : State} (hp : Pre s₀) :
    (lay s₀).buf 0 ∈ s₀.wr ∧ (lay s₀).buf 3 ∈ s₀.wr ∧ (lay s₀).buf 2 ∈ s₀.rd ++ s₀.wr ∧
      (layC s₀).buf 2 ∈ s₀.rd ++ s₀.wr ∧ (layC s₀).buf 0 ∈ s₀.wr := by
  rw [hp.wr, hp.rd]; simp [Lay.buf, lay, layC]

/-! ## The setup -/

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block decapsSetup) s₀ fun s => DEnv s₀ s ∧ s.gpr .r4 = pDk s₀ ∧ s.gpr .r6 = pC s₀ ∧
      bytesAt s.mem ((layC s₀).A 2 0) 1088 = bytesAt s₀.mem ((layC s₀).A 2 0) 1088 := by
  have hL := lay_ok hp
  have fc := hp.f_scr
  obtain ⟨w0, -, -, -, -⟩ := buf_wr hp
  have wS : ∀ {o n : Nat}, o + n ≤ 32768 → InRegions s₀.wr ((lay s₀).A 0 o) n := fun h =>
    Lay.covers w0 h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [decapsSetup, WP.block_append_iff]
  refine WP.mono (saveRegs_ok .r3 (off := 840) (by decide) (fit_le (by decide) fc) fun i hi => by
    rw [add_ofNat_add]; exact wS (by omega)) fun s₁ h₁ => ?_
  have g3 : s₁.gpr .r3 = pScr s₀ := by rw [h₁.gpr]; rfl
  have e872 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32)) = (lay s₀).A 0 872 := by
    rw [g3, ← lay_ptr0]; exact addr_add (by rw [lay_ptr0]; offs)
  have e876 : State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oExtra) = (lay s₀).A 0 876 := by
    rw [g3, ← lay_ptr0]; exact addr_add (by rw [lay_ptr0]; offs)
  have i872 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 (oSave + 32))) 4 := by
    rw [e872, h₁.wr]; exact wS (by decide)
  have i876 : InRegions s₁.wr (State.addr (s₁.gpr .r3 + BitVec.ofNat 32 oExtra)) 4 := by
    rw [e876, h₁.wr]; exact wS (by decide)
  have o1 : oSave + 32 < 4096 := by decide
  have o2 : oExtra < 4096 := by decide
  run_block [i872, i876, o1, o2]
  have ne1 : ∀ i < 8, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((lay s₀).A 0 872) v).readW
      ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  have ne2 : ∀ i < 9, ∀ (m : Mem) (v : BitVec 32), (m.writeW ((lay s₀).A 0 876) v).readW
      ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 = m.readW ((lay s₀).A 0 840 + BitVec.ofNat 64 (4 * i)) 32 :=
    fun i hi m v => Mem.readW_writeW_sep (fun x h1 h2 => by bv_omega) (by decide)
  have fr₀ : Frame ((lay s₀).RL [(0, 840, 40)]) s₀.mem s₁.mem := by
    refine h₁.frame.sub fun r hr' => ⟨Lay.R (lay s₀) 0 840 40, by simp, ?_⟩
    rw [List.mem_singleton] at hr'; subst hr'
    show Region.Sub ⟨State.addr (s₀.gpr .r3) + BitVec.ofNat 64 840, 32⟩ _
    exact Lay.R_sub_R hL (i := 0) (a := 840) (l := 32) (by simp [lay]) (by decide) (by decide) (by simp [lay])
  have c872 : ((lay s₀).R 0 840 40).Contains ((lay s₀).A 0 872) 4 := by
    simp only [Region.Contains]; bv_omega
  have c876 : ((lay s₀).R 0 840 40).Contains ((lay s₀).A 0 876) 4 := by
    simp only [Region.Contains]; bv_omega
  have fr : Frame ((lay s₀).RL [(0, 840, 40)]) s₀.mem
      ((s₁.mem.writeW ((lay s₀).A 0 872) (s₁.gpr .lr)).writeW ((lay s₀).A 0 876) (s₁.gpr .r2)) :=
    (fr₀.writeW (List.mem_singleton_self _) _ c872).writeW (List.mem_singleton_self _) _ c876
  refine ⟨⟨⟨hL, rfl, rfl, by simp [lay], ?_, by show 8 ≤ s₁.sp.toNat; rw [h₁.sp]; exact hp.sp8, ?_, ?_⟩,
    h₁.rd, h₁.wr, h₁.sp, fun i hi => ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [h₁.gpr]; rfl
  · show s₀.sp - BitVec.ofNat 32 8 = s₁.sp - BitVec.ofNat 32 8
    rw [h₁.sp]
  · show (⟨State.addr (pScr s₀), 32768⟩ : Region) ∈ s₁.wr
    rw [h₁.wr, hp.wr]; simp
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e876, ne2 i (by omega), ne1 i hi]
    exact h₁.saved i hi
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e876, show (lay s₀).A 0 872 = (lay s₀).A 0 840 + BitVec.ofNat 64 (4 * 8) by
      rw [add_ofNat_add], ne2 8 (by decide), add_ofNat_add, Mem.readW_writeW_self32, h₁.gpr]
  · show ((s₁.mem.writeW _ _).writeW _ _).readW _ _ = _
    rw [e872, e876, Mem.readW_writeW_self32, h₁.gpr]; rfl
  · show bytesAt ((s₁.mem.writeW _ _).writeW _ _) _ _ = _
    rw [e872, e876]
    exact Lay.bytes_keep hL fr (by ddecide) (by decide)
  · simp [h₁.gpr]; rfl
  · simp [h₁.gpr]; rfl
  · show bytesAt ((s₁.mem.writeW _ _).writeW _ _) _ _ = _
    rw [e872, e876]
    have fC : Frame ((layC s₀).RL [(0, 840, 40)]) s₀.mem
        ((s₁.mem.writeW ((lay s₀).A 0 872) (s₁.gpr .lr)).writeW ((lay s₀).A 0 876) (s₁.gpr .r2)) := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, lay_ptr0, layC_ptr0] using fr
    exact Lay.bytes_keep (layC_ok hp) fC (by rw [layC_sizes]; decide) (by decide)


/-! ## `c` copied -/

/-- `dk`. -/
abbrev DK (s₀ : State) : List Byte := bytesAt s₀.mem ((lay s₀).A 2 0) 2400

/-- `c`. -/
abbrev CT (s₀ : State) : List Byte := bytesAt s₀.mem ((layC s₀).A 2 0) 1088

theorem layA0 (s₀ : State) (o : Nat) : (layC s₀).A 0 o = (lay s₀).A 0 o := by
  simp only [Lay.A, lay_ptr0, layC_ptr0]

theorem copyC_ok {s₀ s : State} (hp : Pre s₀) (h : DEnv s₀ s) (h6 : s.gpr .r6 = pC s₀)
    (hc : bytesAt s.mem ((layC s₀).A 2 0) 1088 = CT s₀) :
    WP isa (copy .r6 0 .r7 oCin 1088) s fun s' =>
      DEnv s₀ s' ∧ s'.gpr .r4 = s.gpr .r4 ∧ bytesAt s'.mem ((lay s₀).A 0 oCin) 1088 = CT s₀ := by
  obtain ⟨-, -, -, wC, wC0⟩ := buf_wr hp
  refine WP.mono (copyL (layC_ok hp) (i := 2) (j := 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h6
    (by rw [h.ctx.r7, lay_ptr0, layC_ptr0]) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [layC_sizes]; decide) (by rw [h.rd, h.wr]; exact wC) (by rw [h.wr]; exact wC0)) fun s' ⟨k, e⟩ =>
    ⟨?_, k.cs .r4 (by decide) (by decide), ?_⟩
  · have k' : Kept ((lay s₀).RL [(0, oCin, 1088)]) s s' := by
      simpa only [Lay.RL, List.map_cons, List.map_nil, Lay.R, lay_ptr0, layC_ptr0] using k
    exact h.keep hp (k'.x []) (by simp) (by decide)
  · rw [← layA0, e, hc]

theorem ptr6_ok {s : State} :
    WP isa (.block [ptrTo .r6 .r7 oCin]) s fun s' =>
      KeptX [.r6] [] s s' ∧ s'.gpr .r6 = s.gpr .r7 + BitVec.ofNat 32 oCin ∧ s'.mem = s.mem := by
  have e1 : encodable (BitVec.ofNat 32 oCin) = true := by decide
  run_block [ptrTo, e1]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  show (if r = .r6 then _ else s.gpr r) = s.gpr r
  exact ite_eq_right (fun e : r = .r6 => hx (by rw [e]; exact List.mem_singleton_self _))

/-- What decryption keeps: `DEnv`, `dk` in `r4`, and the copy of `c` in `r6`. -/
structure DD (s₀ s : State) : Prop where
  env : DEnv s₀ s
  r4 : s.gpr .r4 = pDk s₀
  r6 : s.gpr .r6 = (lay s₀).ptr 0 + BitVec.ofNat 32 oCin
  c : bytesAt s.mem ((lay s₀).A 0 oCin) 1088 = CT s₀

/-- A region decryption may change. -/
def okD (w : Nat × Nat × Nat) : Bool := okW w && sepB [32768, 8, 2400, 32] (0, oCin, 1088) w

theorem DD.keep {s₀ s s' : State} (hp : Pre s₀) (h : DD s₀ s) {xs : List Reg} {W : List (Nat × Nat × Nat)}
    (hk : KeptX xs ((lay s₀).RL W) s s') (hx : ∀ r ∈ [Reg.r4, .r6, .r7], r ∉ xs) (hW : W.all okD = true) :
    DD s₀ s' := by
  have w1 : W.all okW = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [okD, Bool.and_eq_true] at this; exact this.1
  have w2 : sepAll (lay s₀).sizes (0, oCin, 1088) W = true := List.all_eq_true.mpr fun w hw => by
    have := List.all_eq_true.mp hW w hw; simp only [okD, Bool.and_eq_true] at this; exact this.2
  refine ⟨h.env.keep hp hk (hx .r7 (by simp)) w1, ?_, ?_, ?_⟩
  · rw [hk.cs .r4 (by decide) (by decide) (hx .r4 (by simp)), h.r4]
  · rw [hk.cs .r6 (by decide) (by decide) (hx .r6 (by simp)), h.r6]
  · rw [Lay.bytes_keep (lay_ok hp) hk.frame w2 (by decide)]; exact h.c

/-! ## `û` -/

theorem uArgs_ok {s : State} {P C : BitVec 32} {j : Nat} (h7 : s.gpr .r7 = P) (h6 : s.gpr .r6 = C)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 j) :
    WP isa (.block (at320 .r0 .r6 .r9 ++ ([.mov .r1 (.imm 320), .mov .r2 (.imm 10)] : List Instr) ++
      slotAt .r3 .r9 (oPoly 3))) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = C + BitVec.ofNat 32 j <<< 8 + BitVec.ofNat 32 j <<< 6 ∧
        s'.gpr .r1 = BitVec.ofNat 32 (32 * 10) ∧ s'.gpr .r2 = BitVec.ofNat 32 10 ∧
        s'.gpr .r3 = P + BitVec.ofNat 32 j <<< 10 + BitVec.ofNat 32 (oPoly 3) := by
  have e1 : encodable (320 : BitVec 32) = true := by decide
  have e2 : encodable (10 : BitVec 32) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 (oPoly 3)) = true := by decide
  run_block [at320, slotAt, ptrTo, e1, e2, e3, h7, h6, h9]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

/-- `û` for the first `j` rows, from `s₁`. -/
structure UInv (s₀ s₁ : State) (j : Nat) (s : State) : Prop where
  kx : KeptX [.r9] ((lay s₀).RL [(0, oPoly 3, 3072), (0, oNtt, 1024)]) s₁ s
  r9 : s.gpr .r9 = BitVec.ofNat 32 j
  u : ∀ i < j, PolyIs s.mem ((lay s₀).A 0 (oPoly (3 + i))) (ntt (VG.Proof.MlKem.dcU (CT s₀) i))

/-- In row `j` of `û`, from `s`, after the decompression. -/
structure UB (s₀ : State) (j : Nat) (s : State) (s' : State) : Prop where
  K : KeptX [] ((lay s₀).RL [(0, oPoly (3 + j), 1024)]) s s'
  p : PolyIs s'.mem ((lay s₀).A 0 (oPoly (3 + j))) (VG.Proof.MlKem.dcU (CT s₀) j)

theorem u_facts : ∀ j < 3, [((0 : Nat), oPoly (3 + j), (1024 : Nat)), (0, oNtt, 1024)].all
      (fun w => [(0, oPoly 3, 3072), (0, oNtt, 1024)].any (subB0 w)) = true ∧
    (∀ i < 3, (i == j || [((0 : Nat), oPoly (3 + j), (1024 : Nat)), (0, oNtt, 1024)].all
      (sep0 (oPoly (3 + i)) 1024)) = true) ∧
    [((0 : Nat), oPoly 3, (3072 : Nat)), (0, oNtt, 1024)].all (sep0 oCin 1088) = true := by
  decide

section
variable {s₀ : State} (hp : Pre s₀) {s₁ : State} (h₁ : DD s₀ s₁) {j : Nat} (hj : j < 3) {s : State}
  (h : UInv s₀ s₁ j s)
include hp h₁ hj h

omit hp in
theorem u1_ok : WP isa (.block (at320 .r0 .r6 .r9 ++ ([.mov .r1 (.imm 320), .mov .r2 (.imm 10)] : List Instr) ++
      slotAt .r3 .r9 (oPoly 3))) s fun s' =>
      Only s s' ∧ s'.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oCin + 320 * j) ∧
        s'.gpr .r1 = BitVec.ofNat 32 (32 * 10) ∧ s'.gpr .r2 = BitVec.ofNat 32 10 ∧
        s'.gpr .r3 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly (3 + j)) := by
  have hc := h.kx.ctx (by decide) h₁.env.ctx
  have g6 : s.gpr .r6 = (lay s₀).ptr 0 + BitVec.ofNat 32 oCin := by
    rw [h.kx.cs .r6 (by decide) (by decide) (by decide), h₁.r6]
  refine WP.mono (uArgs_ok hc.r7 g6 h.r9) fun s' ⟨o, a0, a1, a2, a3⟩ => ⟨o, ?_, a1, a2, ?_⟩
  · rw [a0, at320_eq _ (by omega), ptr_add_add32]
  · rw [a3, slot_eq _ (by offs), show oPoly 3 + 1024 * j = oPoly (3 + j) by offs]

theorem u2_ok {s' : State} (o : Only s s') (a0 : s'.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oCin + 320 * j))
    (a1 : s'.gpr .r1 = BitVec.ofNat 32 (32 * 10)) (a2 : s'.gpr .r2 = BitVec.ofNat 32 10)
    (a3 : s'.gpr .r3 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly (3 + j))) :
    WP isa callDecompress s' (UB s₀ j s) := by
  have hL := lay_ok hp
  have hc := (h.kx.ctx (by decide) h₁.env.ctx).only o
  obtain ⟨-, -, c3⟩ := u_facts j hj
  have hcb : bytesAt s'.mem ((lay s₀).A 0 (oCin + 320 * j)) (32 * 10) =
      (((CT s₀).drop (320 * j)).take 320) := by
    rw [o.mem, ← h₁.c, ← Lay.bytes_keep hL h.kx.frame (h₁.env.ctx.sepAll0 (by decide) c3) (by decide),
      bytesAt_slice _ _ (by omega), add_ofNat_add]
  refine decompressL hL a0 a1 a2 a3 (by decide) (hc.sep00 (by offs) (by offs) (by offs)) (mem_rd_wr hc.buf0)
    hc.buf0 fun s'' k p => ⟨(o.x _ _).trans (k.x _), ?_⟩
  rw [hcb] at p; exact p

/-- In row `j` of `û`, from `s`, after the NTT. -/
structure UD (s₀ : State) (j : Nat) (s : State) (s' : State) : Prop where
  K : KeptX [] ((lay s₀).RL [(0, oPoly (3 + j), 1024), (0, oNtt, 1024)]) s s'
  p : PolyIs s'.mem ((lay s₀).A 0 (oPoly (3 + j))) (ntt (VG.Proof.MlKem.dcU (CT s₀) j))

omit hp in
theorem u3_ok {s₂ : State} (r : UB s₀ j s s₂) :
    WP isa (.block (slotAt .r0 .r9 (oPoly 3) ++ ([ptrTo .r1 .r7 oNtt] : List Instr))) s₂ fun s₃ =>
      UB s₀ j s s₃ ∧ s₃.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly (3 + j)) ∧
        s₃.gpr .r1 = (lay s₀).ptr 0 + BitVec.ofNat 32 oNtt := by
  have hc₂ := r.K.ctx (by decide) (h.kx.ctx (by decide) h₁.env.ctx)
  have g9 : s₂.gpr .r9 = BitVec.ofNat 32 j := by
    rw [r.K.cs .r9 (by decide) (by decide) (by simp), h.r9]
  refine WP.mono (nttArgs_ok hc₂.r7 g9) fun s₃ ⟨o, a0, a1⟩ => ⟨⟨r.K.trans (o.x _ _), by rw [o.mem]; exact r.p⟩, ?_, a1⟩
  rw [a0, slot_eq _ (by offs), show oPoly 3 + 1024 * j = oPoly (3 + j) by offs]

theorem u4_ok {s₃ : State} (r : UB s₀ j s s₃) (a0 : s₃.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly (3 + j)))
    (a1 : s₃.gpr .r1 = (lay s₀).ptr 0 + BitVec.ofNat 32 oNtt) : WP isa callNtt s₃ (UD s₀ j s) := by
  have hc₃ := r.K.ctx (by decide) (h.kx.ctx (by decide) h₁.env.ctx)
  exact nttL (lay_ok hp) a0 a1 (hc₃.sep00 (by offs) (by offs) (by offs)) hc₃.buf0 hc₃.buf0 r.p fun s₄ k p =>
    ⟨(r.K.monoL (by simp)).trans (k.x _), p⟩

theorem u5_ok {s₄ : State} (r : UD s₀ j s s₄) :
    WP isa (.block (count .r9 3)) s₄ fun s' => UInv s₀ s₁ (j + 1) s' ∧ s'.z = decide (j + 1 = 3) := by
  obtain ⟨c1, c2, -⟩ := u_facts j hj
  have g9 : s₄.gpr .r9 = BitVec.ofNat 32 j := by
    rw [r.K.cs .r9 (by decide) (by decide) (by simp), h.r9]
  refine WP.mono (count_ok (by omega) (by decide) (by decide) g9) fun s' ⟨k', g', z'⟩ => ⟨⟨?_, g', fun i hi => ?_⟩, z'⟩
  · exact h.kx.trans (((r.K.weaken (by simp)).trans (k'.mono (fun _ h => absurd h List.not_mem_nil))).subL
      h₁.env.ctx c1)
  · by_cases e : i = j
    · subst e
      exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil) r.p
    · have := c2 i (by omega)
      simp only [Bool.or_eq_true, beq_iff_eq, e, false_or] at this
      exact polyIs_frame k'.frame (fun _ h => absurd h List.not_mem_nil)
        (Lay.polyIs_keep (lay_ok hp) r.K.frame (h₁.env.ctx.sepAll0 (by offs) this) (h.u i (by omega)))

theorem decU_step : WP isa decUBody s fun s' => UInv s₀ s₁ (j + 1) s' ∧ s'.z = decide (j + 1 = 3) :=
  WP.seq (WP.mono (u1_ok h₁ hj h) fun _ ⟨o, a0, a1, a2, a3⟩ =>
    WP.seq (WP.mono (u2_ok hp h₁ hj h o a0 a1 a2 a3) fun _ r₂ =>
    WP.seq (WP.mono (u3_ok h₁ hj h r₂) fun _ ⟨r₃, b0, b1⟩ =>
    WP.seq (WP.mono (u4_ok hp h₁ hj h r₃ b0 b1) fun _ r₄ => u5_ok hp h₁ hj h r₄))))

end


/-! ## The rest of K-PKE.Decrypt -/

section
variable {s₀ : State} (hp : Pre s₀)
include hp

omit hp in
theorem dU_init {s₁ : State} : WP isa (.block [.mov .r9 (.imm 0)]) s₁ (UInv s₀ s₁ 0) :=
  WP.mono (movc_ok .r9 (N := 0) (by decide)) fun _ ⟨k, g, _⟩ =>
    ⟨k.mono (fun _ h => absurd h List.not_mem_nil), g, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

theorem dU_done {s₁ s : State} (h₁ : DD s₀ s₁) (h : UInv s₀ s₁ 3 s) : DD s₀ s :=
  h₁.keep hp h.kx (by simp) (by decide)

theorem dT_pre {s : State} (h : DD s₀ s) :
    Ctx (lay s₀) s ∧ s.gpr .r4 = (lay s₀).ptr 2 + BitVec.ofNat 32 0 ∧
      sepAll (lay s₀).sizes (2, 0, 1152) [(0, 2048, 3072)] = true ∧ (lay s₀).buf 2 ∈ s.rd ++ s.wr := by
  obtain ⟨-, -, w2, -, -⟩ := buf_wr hp
  exact ⟨h.env.ctx, by rw [h.r4, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]; rfl, by ddecide,
    by rw [h.env.rd, h.env.wr]; exact w2⟩

/-- `ŝ` of `dk`. -/
abbrev sHat (s₀ : State) : Nat → Poly := VG.Proof.MlKem.dcS (VG.Proof.MlKem.dkPke (DK s₀))

/-- `NTT(u')` of `c`. -/
abbrev uHat (s₀ : State) (i : Nat) : Poly := ntt (VG.Proof.MlKem.dcU (CT s₀) i)

theorem dT_done {s₂ s : State} (h₂ : DD s₀ s₂) (hu : ∀ i < 3, PolyIs s₂.mem ((lay s₀).A 0 (oPoly (3 + i))) (uHat s₀ i))
    (h : DecInv (lay s₀) 2 0 s₂ 3 s) :
    DD s₀ s ∧ (∀ k < 3, PolyIs s.mem ((lay s₀).A 0 (oPoly k)) (sHat s₀ k)) ∧
      ∀ i < 3, PolyIs s.mem ((lay s₀).A 0 (oPoly (3 + i))) (uHat s₀ i) := by
  have hL := lay_ok hp
  refine ⟨h₂.keep hp h.kx (by simp) (by decide), fun k hk => ?_, fun i hi => ?_⟩
  · have := h.t k hk
    have e : bytesAt s₂.mem ((lay s₀).A 2 (0 + 384 * k)) 384 = ((DK s₀).drop (384 * k)).take 384 := by
      have dk : bytesAt s₂.mem ((lay s₀).A 2 0) 2400 = DK s₀ := h₂.env.dk
      rw [← dk, bytesAt_slice _ _ (by omega), add_ofNat_add]
    rw [e] at this
    show PolyIs _ _ (decode12 ((((DK s₀).take 1152).drop (384 * k)).take 384))
    rw [VG.Proof.MlKem.slice_take _ (by omega)]; exact this
  · exact Lay.polyIs_keep hL h.kx.frame (h₂.env.ctx.sepAll0 (by offs) (by
      have : ∀ i < 3, [((0 : Nat), (2048 : Nat), (3072 : Nat))].all (sep0 (oPoly (3 + i)) 1024) = true := by decide
      exact this i hi)) (hu i hi)

/-- After `dot`, with the sum `f`. -/
abbrev DV (s₀ : State) (f : Poly) (s : State) : Prop := DD s₀ s ∧ PolyIs s.mem ((lay s₀).A 0 oAcc) f

theorem dDot_ok {s : State} (h : DD s₀ s) (hs : ∀ k < 3, PolyIs s.mem ((lay s₀).A 0 (oPoly k)) (sHat s₀ k))
    (hu : ∀ i < 3, PolyIs s.mem ((lay s₀).A 0 (oPoly (3 + i))) (uHat s₀ i)) :
    WP isa dot s (DV s₀ (VG.Proof.MlKem.dot3 (sHat s₀) (uHat s₀))) :=
  WP.mono (dot_ok h.env.ctx hs hu) fun _ ⟨k, p⟩ => ⟨h.keep hp k (by simp) (by decide), p⟩

theorem dArgs_ok {s : State} {f : Poly} (h : DV s₀ f s) {o o' : Nat} (he : encodable (BitVec.ofNat 32 o) = true)
    (he' : encodable (BitVec.ofNat 32 o') = true) :
    WP isa (.block [ptrTo .r0 .r7 o, ptrTo .r1 .r7 o']) s fun s' => (DV s₀ f s' ∧ s'.mem = s.mem) ∧
      s'.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 o ∧ s'.gpr .r1 = (lay s₀).ptr 0 + BitVec.ofNat 32 o' :=
  WP.mono (accArgs_ok h.1.env.ctx.r7 he he') fun _ ⟨o₁, a0, a1⟩ =>
    ⟨⟨⟨h.1.keep hp (xs := []) (W := []) (o₁.x _ _) (by simp) rfl, by rw [o₁.mem]; exact h.2⟩, o₁.mem⟩, a0, a1⟩

theorem dInv_ok {s : State} {f : Poly} (h : DV s₀ f s) (a0 : s.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 oAcc)
    (a1 : s.gpr .r1 = (lay s₀).ptr 0 + BitVec.ofNat 32 oNtt) : WP isa callNttInv s (DV s₀ (nttInv f)) := by
  have hc := h.1.env.ctx
  exact nttInvL (lay_ok hp) a0 a1 (hc.sep00 (by decide) (by decide) (by decide)) hc.buf0 hc.buf0 h.2
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (by decide), p⟩

omit hp in
theorem vDArgs_ok {s : State} {P C : BitVec 32} (h7 : s.gpr .r7 = P) (h6 : s.gpr .r6 = C) :
    WP isa (.block [ptrTo .r0 .r6 960, .mov .r1 (.imm 128), .mov .r2 (.imm 4), ptrTo .r3 .r7 (oPoly 9)]) s
      fun s' => Only s s' ∧ s'.gpr .r0 = C + BitVec.ofNat 32 960 ∧ s'.gpr .r1 = BitVec.ofNat 32 (32 * 4) ∧
        s'.gpr .r2 = BitVec.ofNat 32 4 ∧ s'.gpr .r3 = P + BitVec.ofNat 32 (oPoly 9) := by
  have e1 : encodable (BitVec.ofNat 32 960) = true := by decide
  have e2 : encodable (128 : BitVec 32) = true := by decide
  have e3 : encodable (4 : BitVec 32) = true := by decide
  have e4 : encodable (BitVec.ofNat 32 (oPoly 9)) = true := by decide
  run_block [ptrTo, e1, e2, e3, e4, h7, h6]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem dV1_ok {s : State} {f : Poly} (h : DV s₀ f s) :
    WP isa (.block [ptrTo .r0 .r6 960, .mov .r1 (.imm 128), .mov .r2 (.imm 4), ptrTo .r3 .r7 (oPoly 9)]) s
      fun s' => DV s₀ f s' ∧ s'.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oCin + 960) ∧
        s'.gpr .r1 = BitVec.ofNat 32 (32 * 4) ∧ s'.gpr .r2 = BitVec.ofNat 32 4 ∧
        s'.gpr .r3 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly 9) :=
  WP.mono (vDArgs_ok h.1.env.ctx.r7 h.1.r6) fun _ ⟨o, a0, a1, a2, a3⟩ =>
    ⟨⟨h.1.keep hp (xs := []) (W := []) (o.x _ _) (by simp) rfl, by rw [o.mem]; exact h.2⟩,
      by rw [a0, ptr_add_add32], a1, a2, a3⟩

theorem dV2_ok {s : State} {f : Poly} (h : DV s₀ f s)
    (a0 : s.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oCin + 960)) (a1 : s.gpr .r1 = BitVec.ofNat 32 (32 * 4))
    (a2 : s.gpr .r2 = BitVec.ofNat 32 4) (a3 : s.gpr .r3 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly 9)) :
    WP isa callDecompress s fun s' => DV s₀ f s' ∧
      PolyIs s'.mem ((lay s₀).A 0 (oPoly 9)) (VG.Proof.MlKem.dcV (CT s₀)) := by
  have hc := h.1.env.ctx
  have hcb : bytesAt s.mem ((lay s₀).A 0 (oCin + 960)) (32 * 4) = ((CT s₀).drop 960).take 128 := by
    rw [← h.1.c, bytesAt_slice _ _ (by decide), add_ofNat_add]
  refine decompressL (lay_ok hp) a0 a1 a2 a3 (by decide) (hc.sep00 (by offs) (by offs) (by offs))
    (mem_rd_wr hc.buf0) hc.buf0 fun s' k p => ⟨⟨h.1.keep hp (k.x []) (by simp) (by decide), ?_⟩, ?_⟩
  · exact Lay.polyIs_keep (lay_ok hp) k.frame (hc.sepAll0 (by decide) (by decide)) h.2
  · rw [hcb] at p; exact p

theorem dV4_ok {s : State} {f : Poly} (h : DV s₀ f s)
    (hv : PolyIs s.mem ((lay s₀).A 0 (oPoly 9)) (VG.Proof.MlKem.dcV (CT s₀)))
    (a0 : s.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly 9)) (a1 : s.gpr .r1 = (lay s₀).ptr 0 + BitVec.ofNat 32 oAcc) :
    WP isa callSub s fun s' => DD s₀ s' ∧
      PolyIs s'.mem ((lay s₀).A 0 (oPoly 9)) (sub (VG.Proof.MlKem.dcV (CT s₀)) f) := by
  have hc := h.1.env.ctx
  exact subL (lay_ok hp) a0 a1 (hc.sep00 (by offs) (by offs) (by offs)) hc.buf0 (mem_rd_wr hc.buf0) hv h.2
    fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (by decide), p⟩

omit hp in
theorem mArgs_ok {s : State} {P : BitVec 32} (h7 : s.gpr .r7 = P) :
    WP isa (.block [ptrTo .r0 .r7 (oPoly 9), .mov .r1 (.imm 1), ptrTo .r2 .r7 oMsg, .mov .r3 (.imm 32)]) s
      fun s' => Only s s' ∧ s'.gpr .r0 = P + BitVec.ofNat 32 (oPoly 9) ∧ s'.gpr .r1 = BitVec.ofNat 32 1 ∧
        s'.gpr .r2 = P + BitVec.ofNat 32 oMsg ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * 1) := by
  have e1 : encodable (BitVec.ofNat 32 (oPoly 9)) = true := by decide
  have e2 : encodable (1 : BitVec 32) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 oMsg) = true := by decide
  have e4 : encodable (32 : BitVec 32) = true := by decide
  run_block [ptrTo, e1, e2, e3, e4, h7]
  refine ⟨Only.of_gpr _ fun r hr hl => ?_, trivial⟩
  obtain ⟨m0, m1, m2, m3, -⟩ := pres_ne hr hl
  simp only [m0, m1, m2, m3, ite_false]

theorem dM1_ok {s : State} {g : Poly} (h : DD s₀ s) (hg : PolyIs s.mem ((lay s₀).A 0 (oPoly 9)) g) :
    WP isa (.block [ptrTo .r0 .r7 (oPoly 9), .mov .r1 (.imm 1), ptrTo .r2 .r7 oMsg, .mov .r3 (.imm 32)]) s
      fun s' => (DD s₀ s' ∧ PolyIs s'.mem ((lay s₀).A 0 (oPoly 9)) g) ∧
        s'.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly 9) ∧ s'.gpr .r1 = BitVec.ofNat 32 1 ∧
        s'.gpr .r2 = (lay s₀).ptr 0 + BitVec.ofNat 32 oMsg ∧ s'.gpr .r3 = BitVec.ofNat 32 (32 * 1) :=
  WP.mono (mArgs_ok h.env.ctx.r7) fun _ ⟨o, a0, a1, a2, a3⟩ =>
    ⟨⟨h.keep hp (xs := []) (W := []) (o.x _ _) (by simp) rfl, by rw [o.mem]; exact hg⟩, a0, a1, a2, a3⟩

theorem dM2_ok {s : State} {g : Poly} (h : DD s₀ s ∧ PolyIs s.mem ((lay s₀).A 0 (oPoly 9)) g)
    (a0 : s.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 (oPoly 9)) (a1 : s.gpr .r1 = BitVec.ofNat 32 1)
    (a2 : s.gpr .r2 = (lay s₀).ptr 0 + BitVec.ofNat 32 oMsg) (a3 : s.gpr .r3 = BitVec.ofNat 32 (32 * 1)) :
    WP isa callCompress s fun s' => DD s₀ s' ∧ bytesAt s'.mem ((lay s₀).A 0 oMsg) 32 = compressEncode 1 g := by
  have hc := h.1.env.ctx
  exact compressL (lay_ok hp) a0 a1 a2 a3 (by decide) (hc.sep00 (by offs) (by offs) (by offs)) (mem_rd_wr hc.buf0)
    hc.buf0 h.2 fun s' k p => ⟨h.1.keep hp (k.x []) (by simp) (by decide), p⟩

end

/-- `m'`. -/
abbrev MM (s₀ : State) : List Byte := VG.Proof.MlKem.decM (DK s₀) (CT s₀)

theorem decrypt_ok {s₀ s₁ : State} (hp : Pre s₀) (h₁ : DD s₀ s₁) :
    WP isa decrypt s₁ fun s => DD s₀ s ∧ bytesAt s.mem ((lay s₀).A 0 oMsg) 32 = MM s₀ := by
  refine WP.seq (WP.mono (dU_init (s₀ := s₀)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (wp_loop_ne (UInv s₀ s₁) (N := 3) (by decide) (fun j hj s h => decU_step hp h₁ hj h)
    (fun _ h => h) h₂) fun s₃ h₃ => ?_)
  have d₃ := dU_done hp h₁ h₃
  obtain ⟨hc₃, g4, hs₃, hr₃⟩ := dT_pre hp d₃
  refine WP.seq (WP.mono (decT_init (L := lay s₀) (i := 2) (o := 0)) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (decT_loop hc₃ g4 hs₃ hr₃ h₄) fun s₅ h₅ => ?_)
  obtain ⟨d₅, ŝ₅, û₅⟩ := dT_done hp d₃ h₃.u h₅
  refine WP.seq (WP.mono (dDot_ok hp d₅ ŝ₅ û₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (dArgs_ok hp h₆ (o := oAcc) (o' := oNtt) (by decide) (by decide)) fun s₇ ⟨h₇, a0, a1⟩ => ?_)
  refine WP.seq (WP.mono (dInv_ok hp h₇.1 a0 a1) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (dV1_ok hp h₈) fun s₉ ⟨h₉, b0, b1, b2, b3⟩ => ?_)
  refine WP.seq (WP.mono (dV2_ok hp h₉ b0 b1 b2 b3) fun s₁₀ ⟨h₁₀, v₁₀⟩ => ?_)
  refine WP.seq (WP.mono (dArgs_ok hp h₁₀ (o := oPoly 9) (o' := oAcc) (by decide) (by decide))
    fun s₁₁ ⟨h₁₁, c0, c1⟩ => ?_)
  have v₁₁ : PolyIs s₁₁.mem ((lay s₀).A 0 (oPoly 9)) (VG.Proof.MlKem.dcV (CT s₀)) := by rw [h₁₁.2]; exact v₁₀
  refine WP.seq (WP.mono (dV4_ok hp h₁₁.1 v₁₁ c0 c1) fun s₁₂ ⟨h₁₂, w₁₂⟩ => ?_)
  refine WP.seq (WP.mono (dM1_ok hp h₁₂ w₁₂) fun s₁₃ ⟨h₁₃, e0, e1, e2, e3⟩ => ?_)
  refine WP.mono (dM2_ok hp h₁₃ e0 e1 e2 e3) fun s ⟨h, m⟩ => ⟨h, m.trans ?_⟩
  show _ = kpkeDecrypt mlKem768 (VG.Proof.MlKem.dkPke (DK s₀)) (CT s₀)
  rw [VG.Proof.MlKem.kpkeDecrypt768]


/-! ## The hashes -/

/-- The buffer of each pointer register. -/
def didx : Reg → Nat
  | .r4 => 2 | _ => 0

theorem pieceD {s₀ s : State} (hp : Pre s₀) (h : DD s₀ s) {p : Piece} {w : Bool}
    (hb : p.base = .r4 ∨ p.base = .r7) (hw : w = true → p.base = .r7)
    (hoe : encodable (BitVec.ofNat 32 p.off) = true) (hle : encodable (BitVec.ofNat 32 p.len) = true)
    (hpos : 0 < p.len) (hlt : p.off + p.len < 2 ^ 32)
    (hsep : sepAll [32768, 8, 2400, 32] (didx p.base, p.off, p.len) kRegs = true) :
    PieceOk (lay s₀) didx s w p := by
  obtain ⟨w0, -, w2, -, -⟩ := buf_wr hp
  rw [← h.env.wr] at w0
  rw [← h.env.wr, ← h.env.rd] at w2
  refine ⟨?_, ?_, hoe, hle, hpos, hlt, hsep, ?_⟩
  · rcases hb with e | e <;> rw [e] <;> decide
  · rcases hb with e | e <;> rw [e]
    · exact h.r4
    · exact h.env.ctx.r7
  · cases w
    · simp only [Bool.false_eq_true, ite_false]
      rcases hb with e | e <;> rw [e]
      · exact w2
      · exact mem_rd_wr w0
    · simp only [ite_true]
      rw [hw rfl]; exact w0

section
variable (s₀ : State)

/-- `h`, `z` and `ek` of `dk`. -/
abbrev hH : List Byte := VG.Proof.MlKem.dkH (DK s₀)
abbrev zZ : List Byte := VG.Proof.MlKem.dkZ (DK s₀)
abbrev eK : List Byte := VG.Proof.MlKem.dkEk (DK s₀)

/-- `K'` and `r'`, the outputs of `G(m' ‖ h)`, and `K̄ = J(z ‖ c)`. -/
abbrev K1 : List Byte := (G (MM s₀ ++ hH s₀)).1
abbrev R1 : List Byte := (G (MM s₀ ++ hH s₀)).2
abbrev KB : List Byte := J (zZ s₀ ++ CT s₀)

end

theorem dk_slice {s₀ s : State} (h : DD s₀ s) {k : Nat} (hk : k + 32 ≤ 2400) :
    bytesAt s.mem ((lay s₀).A 2 k) 32 = ((DK s₀).drop k).take 32 := by
  have dk : bytesAt s.mem ((lay s₀).A 2 0) 2400 = DK s₀ := h.env.dk
  rw [← dk, bytesAt_slice _ _ hk, add_ofNat_add, Nat.zero_add]

theorem hashG_ok {s₀ s : State} (hp : Pre s₀) (h : DD s₀ s) (hm : bytesAt s.mem ((lay s₀).A 0 oMsg) 32 = MM s₀) :
    WP isa (hash 72 0x06 [⟨.r7, oMsg, 32⟩, ⟨.r4, 2336, 32⟩] [⟨.r7, oG, 64⟩]) s fun s' =>
      DD s₀ s' ∧ Frame ((lay s₀).RL (kRegs ++ [(0, oG, 64)])) s.mem s'.mem ∧
      bytesAt s'.mem ((lay s₀).A 0 oG) 32 = K1 s₀ ∧ bytesAt s'.mem ((lay s₀).A 0 oSigma) 32 = R1 s₀ := by
  have hin : ∀ p ∈ [(⟨.r7, oMsg, 32⟩ : Piece), ⟨.r4, 2336, 32⟩], PieceOk (lay s₀) didx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact pieceD hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact pieceD hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout : ∀ p ∈ [(⟨.r7, oG, 64⟩ : Piece)], PieceOk (lay s₀) didx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceD hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hin' : (List.map ((lay s₀).pb didx s.mem) [⟨.r7, oMsg, 32⟩, ⟨.r4, 2336, 32⟩]).flatten = MM s₀ ++ hH s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀).A 0 oMsg) 32 ++ bytesAt s.mem ((lay s₀).A 2 2336) 32 = _
    rw [hm, dk_slice h (by decide)]; rfl
  refine WP.mono (hash_ok VG.Proof.MlKem.rate72 (by decide) (by decide) (by decide) h.env.ctx (List.cons_ne_nil _ _)
    hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨?_, k'.frame, ?_⟩
  · exact h.keep hp (k'.x []) (by simp) (by decide)
  · have e1 := o'.1
    rw [hin'] at e1
    have e2 : bytesAt s'.mem ((lay s₀).A 0 oG) 64 = (G (MM s₀ ++ hH s₀)).1 ++ (G (MM s₀ ++ hH s₀)).2 :=
      e1.trans (G_split _)
    rw [show (64 : Nat) = 32 + 32 from rfl, bytesAt_add] at e2
    have l1 : (bytesAt s'.mem ((lay s₀).A 0 oG) 32).length = (G (MM s₀ ++ hH s₀)).1.length := by
      rw [bytesAt_length, VG.Proof.MlKem.G_fst_length]
    obtain ⟨r1, r2⟩ := List.append_inj e2 l1
    refine ⟨r1, ?_⟩
    show bytesAt s'.mem (State.addr ((lay s₀).ptr 0) + BitVec.ofNat 64 (888 + 32)) 32 = _
    rw [← add_ofNat_add]; exact r2

theorem hashJ_ok {s₀ s : State} (hp : Pre s₀) (h : DD s₀ s) :
    WP isa (hash 136 0x1f [⟨.r4, 2368, 32⟩, ⟨.r7, oCin, 1088⟩] [⟨.r7, oKbar, 32⟩]) s fun s' =>
      DD s₀ s' ∧ Frame ((lay s₀).RL (kRegs ++ [(0, oKbar, 32)])) s.mem s'.mem ∧
      bytesAt s'.mem ((lay s₀).A 0 oKbar) 32 = KB s₀ := by
  have hin : ∀ p ∈ [(⟨.r4, 2368, 32⟩ : Piece), ⟨.r7, oCin, 1088⟩], PieceOk (lay s₀) didx s false p := by
    intro p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact pieceD hp h (.inl rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact pieceD hp h (.inr rfl) (by simp) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout : ∀ p ∈ [(⟨.r7, oKbar, 32⟩ : Piece)], PieceOk (lay s₀) didx s true p := by
    intro p hp'; rw [List.mem_singleton] at hp'; subst hp'
    exact pieceD hp h (.inr rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hin' : (List.map ((lay s₀).pb didx s.mem) [⟨.r4, 2368, 32⟩, ⟨.r7, oCin, 1088⟩]).flatten =
      zZ s₀ ++ CT s₀ := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    show bytesAt s.mem ((lay s₀).A 2 2368) 32 ++ bytesAt s.mem ((lay s₀).A 0 oCin) 1088 = _
    rw [dk_slice h (by decide), h.c]; rfl
  refine WP.mono (hash_ok VG.Proof.MlKem.rate136 (by decide) (by decide) (by decide) h.env.ctx (List.cons_ne_nil _ _)
    hin hout (List.pairwise_singleton _ _)) fun s' ⟨k', o'⟩ => ⟨h.keep hp (k'.x []) (by simp) (by decide), k'.frame, ?_⟩
  have e1 := o'.1
  rw [hin'] at e1
  refine e1.trans ?_
  show _ = J (zZ s₀ ++ CT s₀)
  rw [VG.Proof.MlKem.J_eq]; rfl


/-! ## The re-encryption -/

theorem ptrs_ok {s : State} :
    WP isa (.block [ptrTo .r4 .r4 1152, ptrTo .r5 .r7 oMsg, ptrTo .r8 .r7 oCt]) s fun s' =>
      KeptX [.r4, .r5, .r8] [] s s' ∧ s'.gpr .r4 = s.gpr .r4 + BitVec.ofNat 32 1152 ∧
      s'.gpr .r5 = s.gpr .r7 + BitVec.ofNat 32 oMsg ∧ s'.gpr .r8 = s.gpr .r7 + BitVec.ofNat 32 oCt ∧
      s'.mem = s.mem := by
  have e1 : encodable (BitVec.ofNat 32 1152) = true := by decide
  have e2 : encodable (BitVec.ofNat 32 oMsg) = true := by decide
  have e3 : encodable (BitVec.ofNat 32 oCt) = true := by decide
  run_block [ptrTo, e1, e2, e3]
  refine ⟨⟨fun r _ _ hx => ?_, rfl, rfl, rfl, Frame.refl _ _⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  show (if r = .r8 then _ else if r = .r5 then _ else if r = .r4 then _ else s.gpr r) = s.gpr r
  rw [ite_eq_right hx.2.2, ite_eq_right hx.2.1, ite_eq_right hx.1]

/-- Before the re-encryption. -/
structure DP (s₀ s : State) : Prop where
  env : DEnv s₀ s
  r4 : s.gpr .r4 = (lay s₀).ptr 2 + BitVec.ofNat 32 1152
  r5 : s.gpr .r5 = (lay s₀).ptr 0 + BitVec.ofNat 32 oMsg
  r6 : s.gpr .r6 = (lay s₀).ptr 0 + BitVec.ofNat 32 oCin
  r8 : s.gpr .r8 = (lay s₀).ptr 0 + BitVec.ofNat 32 oCt
  c : bytesAt s.mem ((lay s₀).A 0 oCin) 1088 = CT s₀
  m : bytesAt s.mem ((lay s₀).A 0 oMsg) 32 = MM s₀
  k1 : bytesAt s.mem ((lay s₀).A 0 oG) 32 = K1 s₀
  r1 : bytesAt s.mem ((lay s₀).A 0 oSigma) 32 = R1 s₀
  kb : bytesAt s.mem ((lay s₀).A 0 oKbar) 32 = KB s₀

theorem ptrs_dp {s₀ s : State} (hp : Pre s₀) (h : DD s₀ s) (hm : bytesAt s.mem ((lay s₀).A 0 oMsg) 32 = MM s₀)
    (hk : bytesAt s.mem ((lay s₀).A 0 oG) 32 = K1 s₀) (hr : bytesAt s.mem ((lay s₀).A 0 oSigma) 32 = R1 s₀)
    (hb : bytesAt s.mem ((lay s₀).A 0 oKbar) 32 = KB s₀) :
    WP isa (.block [ptrTo .r4 .r4 1152, ptrTo .r5 .r7 oMsg, ptrTo .r8 .r7 oCt]) s (DP s₀) :=
  WP.mono ptrs_ok fun _ ⟨k, g4, g5, g8, m⟩ =>
    ⟨h.env.keep hp (W := []) k (by simp) rfl, by rw [g4, h.r4]; rfl, by rw [g5, h.env.ctx.r7],
      by rw [k.cs .r6 (by decide) (by decide) (by simp), h.r6], by rw [g8, h.env.ctx.r7],
      by rw [m]; exact h.c, by rw [m]; exact hm, by rw [m]; exact hk, by rw [m]; exact hr, by rw [m]; exact hb⟩

/-- The buffers of `encrypt`: `ek` in `dk`, `m'` and `c'` in `scratch`. -/
abbrev db : EB := ⟨2, 1152, 0, oMsg, 0, oCt⟩

theorem encPre {s₀ s : State} (hp : Pre s₀) (h : DP s₀ s) : EncPre (lay s₀) db s := by
  obtain ⟨w0, -, w2, -, -⟩ := buf_wr hp
  exact ⟨h.env.ctx, h.r4, h.r5, h.r8, by ddecide, by ddecide, by ddecide, by rw [h.env.rd, h.env.wr]; exact w2,
    by rw [h.env.rd, h.env.wr]; exact mem_rd_wr w0, by rw [h.env.wr]; exact w0⟩

theorem encW_ok : (encW db).all okW = true ∧
    [((0 : Nat), oCin, (1088 : Nat)), (0, oG, 32), (0, oKbar, 32)].all
      (fun w => sepAll [32768, 8, 2400, 32] w (encW db)) = true := by
  decide

/-- `ρ` of `dk`. -/
abbrev ρD (s₀ : State) : List Byte := ekRho mlKem768 (eK s₀)

/-- `c'`. -/
abbrev C2 (s₀ : State) : List Byte := VG.Proof.MlKem.ct768 (aEnc (ρD s₀) (R1 s₀)) (eK s₀) (MM s₀) (R1 s₀)

/-- After the re-encryption. -/
structure DQ (s₀ s : State) : Prop where
  env : DEnv s₀ s
  r6 : s.gpr .r6 = (lay s₀).ptr 0 + BitVec.ofNat 32 oCin
  r11 : s.gpr .r11 = if okEnc (ρD s₀) 3 then 1 else 0
  c : bytesAt s.mem ((lay s₀).A 0 oCin) 1088 = CT s₀
  c2 : bytesAt s.mem ((lay s₀).A 0 oCt) 1088 = C2 s₀
  k1 : bytesAt s.mem ((lay s₀).A 0 oG) 32 = K1 s₀
  kb : bytesAt s.mem ((lay s₀).A 0 oKbar) 32 = KB s₀

theorem rhoE_eq {s₀ s : State} (h : DP s₀ s) : ρE (lay s₀) db s = ρD s₀ := by
  show ekRho mlKem768 (bytesAt s.mem ((lay s₀).A 2 1152) 1184) = _
  have dk : bytesAt s.mem ((lay s₀).A 2 0) 2400 = DK s₀ := h.env.dk
  rw [show (lay s₀).A 2 1152 = (lay s₀).A 2 0 + BitVec.ofNat 64 1152 by rw [add_ofNat_add],
    ← bytesAt_slice _ _ (by decide : 1152 + 1184 ≤ 2400), dk]
  rfl

theorem reenc_ok {s₀ s : State} (hp : Pre s₀) (h : DP s₀ s) : WP isa encrypt s (DQ s₀) := by
  have hL := lay_ok hp
  have eρ : ρE (lay s₀) db s = ρD s₀ := rhoE_eq h
  have e1 : ekB (lay s₀) db s = eK s₀ := by
    show bytesAt s.mem ((lay s₀).A 2 1152) 1184 = _
    have dk : bytesAt s.mem ((lay s₀).A 2 0) 2400 = DK s₀ := h.env.dk
    rw [show (lay s₀).A 2 1152 = (lay s₀).A 2 0 + BitVec.ofNat 64 1152 by rw [add_ofNat_add],
      ← bytesAt_slice _ _ (by decide : 1152 + 1184 ≤ 2400), dk]
    rfl
  have e2 : mB (lay s₀) db s = MM s₀ := h.m
  have er : rB (lay s₀) s = R1 s₀ := h.r1
  obtain ⟨c1, c2⟩ := encW_ok
  have sep : ∀ {o l : Nat}, ((0 : Nat), o, l) ∈ [((0 : Nat), oCin, (1088 : Nat)), (0, oG, 32), (0, oKbar, 32)] →
      sepAll (lay s₀).sizes (0, o, l) (encW db) = true := fun hm => List.all_eq_true.mp c2 _ hm
  refine WP.mono (encrypt_ok (encPre hp h)) fun s' ⟨K, r11, ct⟩ =>
    ⟨h.env.keep hp K (by simp) c1, by rw [K.cs .r6 (by decide) (by decide) (by simp), h.r6], ?_,
      (Lay.bytes_keep hL K.frame (sep (by simp)) (by decide)).trans h.c, ?_,
      (Lay.bytes_keep hL K.frame (sep (by simp)) (by decide)).trans h.k1,
      (Lay.bytes_keep hL K.frame (sep (by simp)) (by decide)).trans h.kb⟩
  · rw [r11]; show (if okEnc (ρE (lay s₀) db s) 3 = true then _ else _) = _; rw [eρ]
  · rw [e1, e2] at ct
    show _ = VG.Proof.MlKem.ct768 (aEnc (ρD s₀) (R1 s₀)) (eK s₀) (MM s₀) (R1 s₀)
    rw [← eρ, ← er]; exact ct


/-! ## The comparison and the selection -/

theorem covers2 {L : Lay} {s : State} (hc : Ctx L s) {o o' l l' : Nat} (h : o + l ≤ 32768) (h' : o' + l' ≤ 32768) :
    Covers [L.R 0 o l, L.R 0 o' l'] (s.rd ++ s.wr) := fun a n ⟨r, hr, hcn⟩ => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact mem_rd_wr' (hc.cs h _ _ ⟨_, List.mem_singleton_self _, hcn⟩)
  · exact mem_rd_wr' (hc.cs h' _ _ ⟨_, List.mem_singleton_self _, hcn⟩)

/-- After the comparison. -/
structure DR (s₀ s : State) : Prop where
  q : DQ s₀ s
  lt : (s.gpr .r12).toNat < 256
  eq : s.gpr .r12 = 0 ↔ CT s₀ = C2 s₀

theorem kept_of {s s' : State} {x : Reg} {W : List Region} (cs : ∀ r ∈ preserved, r ≠ x → s'.gpr r = s.gpr r)
    (sp : s'.sp = s.sp) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (fr : Frame W s.mem s'.mem) : KeptX [x] W s s' :=
  ⟨fun r hr _ hx => cs r hr fun e => hx (by rw [e]; exact List.mem_singleton_self _), sp, rd, wr, fr⟩

theorem cmp_ok {s₀ s : State} (hp : Pre s₀) (h : DQ s₀ s) : WP isa compare s (DR s₀) := by
  have hc := h.env.ctx
  refine WP.mono (compare_ok (P := (lay s₀).ptr 0) hc.r7 h.r6 (hc.fitO (by decide) (by decide))
    (hc.fitO (by decide) (by decide))
    (by rw [hc.addr (by decide), hc.addr (by decide)]; exact covers2 hc (by decide) (by decide)))
    fun s' ⟨cs, m, rd, wr, sp, lt, eq⟩ => ?_
  have k : KeptX [.r9] ((lay s₀).RL []) s s' := kept_of cs sp rd wr (by rw [m]; exact Frame.refl _ _)
  refine ⟨⟨h.env.keep hp k (by decide) rfl, by rw [cs .r6 (by decide) (by decide), h.r6],
    by rw [cs .r11 (by decide) (by decide), h.r11], by rw [m]; exact h.c, by rw [m]; exact h.c2,
    by rw [m]; exact h.k1, by rw [m]; exact h.kb⟩, lt, ?_⟩
  rw [eq, hc.addr (by decide), hc.addr (by decide)]
  show bytesAt s.mem ((lay s₀).A 0 oCin) 1088 = bytesAt s.mem ((lay s₀).A 0 oCt) 1088 ↔ _
  rw [h.c, h.c2]

/-- After the mask. -/
structure DS (s₀ s : State) : Prop where
  q : DQ s₀ s
  r0 : s.gpr .r0 = (lay s₀).ptr 0 + BitVec.ofNat 32 oG
  r1 : s.gpr .r1 = (lay s₀).ptr 0 + BitVec.ofNat 32 oKbar
  r2 : s.gpr .r2 = pKey s₀
  r9 : s.gpr .r9 = BitVec.ofNat 32 32
  r12 : s.gpr .r12 = if decide (CT s₀ = C2 s₀) then BitVec.allOnes 32 else 0

theorem mask_ok {s₀ s : State} (hp : Pre s₀) (h : DR s₀ s) : WP isa (.block selSetup) s (DS s₀) := by
  have hc := h.q.env.ctx
  refine WP.mono (selSetup_ok (P := (lay s₀).ptr 0) (K := pKey s₀) hc.r7 h.lt
    (by rw [hc.addr (by decide)]; exact h.q.env.key)
    (by rw [hc.addr (by decide)]; exact mem_rd_wr' (hc.cs (o := 876) (l := 4) (by decide) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)))
    fun s' ⟨g12, g0, g1, g2, g9, cs, m, rd, wr, sp⟩ => ?_
  have k : KeptX [.r9] ((lay s₀).RL []) s s' := kept_of cs sp rd wr (by rw [m]; exact Frame.refl _ _)
  refine ⟨⟨h.q.env.keep hp k (by decide) rfl, by rw [cs .r6 (by decide) (by decide), h.q.r6],
    by rw [cs .r11 (by decide) (by decide), h.q.r11], by rw [m]; exact h.q.c, by rw [m]; exact h.q.c2,
    by rw [m]; exact h.q.k1, by rw [m]; exact h.q.kb⟩, g0, g1, g2, g9, ?_⟩
  rw [g12]
  simp only [h.eq, decide_eq_true_eq]

theorem sel_ok {s₀ s : State} (hp : Pre s₀) (h : DS s₀ s) :
    WP isa (.loop (.block selBody) .ne) s fun s' => DEnv s₀ s' ∧
      s'.gpr .r11 = (if okEnc (ρD s₀) 3 then 1 else 0) ∧
      bytesAt s'.mem (State.addr (pKey s₀)) 32 = if CT s₀ = C2 s₀ then K1 s₀ else KB s₀ := by
  have hL := lay_ok hp
  have hc := h.q.env.ctx
  obtain ⟨-, w3, -, -, -⟩ := buf_wr hp
  have eZ : (⟨State.addr (pKey s₀), 32⟩ : Region) = (lay s₀).R 3 0 32 := by simp only [Lay.R, add_ofNat_zero]; rfl
  have dZ : ∀ o, sepB (lay s₀).sizes (0, o, 32) (3, 0, 32) = true → o + 32 ≤ 32768 →
      (⟨State.addr ((lay s₀).ptr 0 + BitVec.ofNat 32 o), 32⟩ : Region).Disjoint ⟨State.addr (pKey s₀), 32⟩ :=
    fun o hs ho => by rw [hc.addr (by omega), eZ]; exact Lay.disj hL hs
  refine WP.mono (select_ok (e := decide (CT s₀ = C2 s₀)) (hc.fitO (by decide) (by decide))
    (hc.fitO (by decide) (by decide)) hp.f_key (dZ _ (by ddecide) (by decide)) (dZ _ (by ddecide) (by decide))
    (by rw [hc.addr (by decide), hc.addr (by decide)]; exact covers2 hc (by decide) (by decide))
    (by rw [eZ, h.q.env.wr]; exact Lay.covers w3 (by simp only [Lay.size, lay_sizes]; decide)) h.r0 h.r1 h.r2 h.r9 h.r12)
    fun s' ⟨cs, rd, wr, sp, fr, b⟩ => ⟨?_, ?_, ?_⟩
  · have k : KeptX [.r9, .r10] ((lay s₀).RL [(3, 0, 32)]) s s' :=
      ⟨fun r hr _ hx => cs r hr (fun e => hx (by rw [e]; simp)) (fun e => hx (by rw [e]; simp)), sp, rd, wr,
        by rw [show (lay s₀).RL [(3, 0, 32)] = [⟨State.addr (pKey s₀), 32⟩] by rw [eZ]; rfl]; exact fr⟩
    exact h.q.env.keep hp k (by decide) (by decide)
  · rw [cs .r11 (by decide) (by decide) (by decide), h.q.r11]
  · rw [b, hc.addr (by decide), hc.addr (by decide), h.q.k1, h.q.kb]
    by_cases e : CT s₀ = C2 s₀ <;> simp [e]


/-! ## The whole function -/

theorem dd_of {s₀ s₂ s₃ : State} (hp : Pre s₀) (h₂ : DEnv s₀ s₂) (g4 : s₂.gpr .r4 = pDk s₀)
    (c₂ : bytesAt s₂.mem ((lay s₀).A 0 oCin) 1088 = CT s₀)
    (h₃ : KeptX [.r6] [] s₂ s₃ ∧ s₃.gpr .r6 = s₂.gpr .r7 + BitVec.ofNat 32 oCin ∧ s₃.mem = s₂.mem) : DD s₀ s₃ :=
  ⟨h₂.keep hp (W := []) h₃.1 (by decide) rfl, by rw [h₃.1.cs .r4 (by decide) (by decide) (by decide), g4],
    by rw [h₃.2.1, h₂.ctx.r7], by rw [h₃.2.2]; exact c₂⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa decaps s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      s.gpr .r0 = (if okEnc (ρD s₀) 3 then 1 else 0) ∧
      bytesAt s.mem (State.addr (pKey s₀)) 32 = if CT s₀ = C2 s₀ then K1 s₀ else KB s₀ := by
  have hL := lay_ok hp
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨h₁, g4, g6, c₁⟩ => ?_)
  refine WP.seq (WP.mono (copyC_ok hp h₁ g6 c₁) fun s₂ ⟨h₂, g4₂, c₂⟩ => ?_)
  refine WP.seq (WP.mono ptr6_ok fun s₃ h₃ => ?_)
  have d₃ := dd_of hp h₂ (by rw [g4₂, g4]) c₂ h₃
  refine WP.seq (WP.mono (decrypt_ok hp d₃) fun s₄ ⟨d₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (hashG_ok hp d₄ m₄) fun s₅ ⟨d₅, f₅, k₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hashJ_ok hp d₅) fun s₆ ⟨d₆, f₆, kb₆⟩ => ?_)
  have m₆ := (Lay.bytes_keep hL f₆ (by ddecide) (by decide)).trans
    ((Lay.bytes_keep hL f₅ (by ddecide) (by decide)).trans m₄)
  have k₆ := (Lay.bytes_keep hL f₆ (by ddecide) (by decide)).trans k₅
  have r₆ := (Lay.bytes_keep hL f₆ (by ddecide) (by decide)).trans r₅
  refine WP.seq (WP.mono (ptrs_dp hp d₆ m₆ k₆ r₆ kb₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (reenc_ok hp h₇) fun s₈ h₈ => ?_)
  refine WP.seq (WP.mono (cmp_ok hp h₈) fun s₉ h₉ => ?_)
  refine WP.seq (WP.mono (mask_ok hp h₉) fun s₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (sel_ok hp h₁₀) fun s₁₁ ⟨h₁₁, r11, key⟩ => ?_)
  exact WP.mono (topEnd_ok h₁₁.ctx h₁₁.sav h₁₁.savlr) fun s ⟨pr, r0, m', sp'⟩ =>
    ⟨pr, sp'.trans h₁₁.sp, by rw [r0, r11], by rw [m']; exact key⟩

end VG.Proof.MlKem.Arm.Decaps
