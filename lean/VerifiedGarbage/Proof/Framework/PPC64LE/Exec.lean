import Mathlib.Tactic.IntervalCases
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.Block

/-!
# PPC64LE: instruction-level rewrite lemmas for symbolic execution

Untrusted: everything here is checked by Lean.

The registers are 64 bits and `add`, `subf` and the logical instructions act
on all of them, so 32-bit values are tracked by the low word of a register,
`s.read .w r` (`(s.gpr r).setWidth 32`); `lo32_add` and friends push the
low word through the 64-bit operations.
-/

namespace VG.PPC64LE

theorem addr_eq {s : State} {bytes : Nat} {n : Reg} {off : Nat} (hn : n ≠ .r0)
    (ho : off < 2 ^ 15 ∧ (bytes = 8 → off % 4 = 0)) :
    addr s bytes n off = some (s.gpr n + BitVec.ofNat 64 off) := by
  unfold addr; exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hn, ho⟩)

theorem addrX_eq {s : State} {a b : Reg} (ha : a ≠ .r0) : addrX s a b = some (s.gpr a + s.gpr b) := by
  unfold addrX; exact ite_eq_left_of_eq_true _ _ (eq_true ha)

theorem exec_load_w {s : State} {t n : Reg} {off : Nat} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4) :
    exec (.load .w t n off) s =
      some (s.write t ((s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64)) := by
  simp only [exec, addr_eq (bytes := 4) hn ⟨ho, fun h => absurd h (by decide)⟩, Option.bind_some,
    State.load, Size.bytes, h, ite_true, Option.map_some, Mem.readW]
  rfl

theorem exec_load_d {s : State} {t n : Reg} {off : Nat} (hn : n ≠ .r0)
    (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.load .d t n off) s = some (s.write t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, addr_eq (bytes := 8) hn ⟨ho.1, fun _ => ho.2⟩, Option.bind_some,
    State.load, Size.bytes, h, ite_true, Option.map_some, Mem.readW]

theorem exec_store_w {s : State} {t n : Reg} {off : Nat} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) :
    exec (.store .w t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth 32) } := by
  simp only [exec, addr_eq (bytes := 4) hn ⟨ho, fun h => absurd h (by decide)⟩, Option.bind_some,
    State.store, Size.bytes, h, ite_true, Mem.writeW]
  rfl

theorem exec_store_d {s : State} {t n : Reg} {off : Nat} (hn : n ≠ .r0)
    (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.store .d t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) } := by
  simp only [exec, addr_eq (bytes := 8) hn ⟨ho.1, fun _ => ho.2⟩, Option.bind_some,
    State.store, Size.bytes, h, ite_true, Mem.writeW]

theorem exec_lbz {s : State} {t n : Reg} {off : Nat} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.lbz t n off) s =
      some (s.write t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 64)) := by
  simp only [exec, addr_eq (bytes := 1) hn ⟨ho, fun h => absurd h (by decide)⟩, Option.bind_some, State.load, h,
    ite_true, Option.map_some]

theorem exec_stb {s : State} {t n : Reg} {off : Nat} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.stb t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.gpr t).setWidth 8) } := by
  simp only [exec, addr_eq (bytes := 1) hn ⟨ho, fun h => absurd h (by decide)⟩, Option.bind_some, State.store, h,
    ite_true]

theorem exec_loadRev_w {s : State} {t a b : Reg} (ha : a ≠ .r0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr a + s.gpr b) 4) :
    exec (.loadRev .w t a b) s =
      some (s.write t ((rev32 (s.mem.readW (s.gpr a + s.gpr b) 32)).setWidth 64)) := by
  simp only [exec, addrX_eq ha, Option.bind_some, State.load, h, ite_true, Option.map_some,
    Mem.readW]
  rfl

theorem exec_loadRev_d {s : State} {t a b : Reg} (ha : a ≠ .r0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr a + s.gpr b) 8) :
    exec (.loadRev .d t a b) s = some (s.write t (rev64 (s.mem.readW (s.gpr a + s.gpr b) 64))) := by
  simp only [exec, addrX_eq ha, Option.bind_some, State.load, h, ite_true, Option.map_some,
    Mem.readW]
  rfl

theorem exec_storeRev_w {s : State} {t a b : Reg} (ha : a ≠ .r0)
    (h : InRegions s.wr (s.gpr a + s.gpr b) 4) :
    exec (.storeRev .w t a b) s =
      some { s with mem := s.mem.writeW (s.gpr a + s.gpr b) (rev32 ((s.gpr t).setWidth 32)) } := by
  simp only [exec, addrX_eq ha, Option.bind_some, State.store, h, ite_true, Mem.writeW,
    State.read, Size.bits]
  rfl

theorem exec_storeRev_d {s : State} {t a b : Reg} (ha : a ≠ .r0)
    (h : InRegions s.wr (s.gpr a + s.gpr b) 8) :
    exec (.storeRev .d t a b) s =
      some { s with mem := s.mem.writeW (s.gpr a + s.gpr b) (rev64 (s.gpr t)) } := by
  simp only [exec, addrX_eq ha, Option.bind_some, State.store, h, ite_true, Mem.writeW]
  rfl

theorem exec_add {s : State} {d n m : Reg} :
    exec (.add d n m) s = some (s.write d (s.gpr n + s.gpr m)) := rfl

theorem exec_sub {s : State} {d n m : Reg} :
    exec (.sub d n m) s = some (s.write d (s.gpr n - s.gpr m)) := rfl

theorem exec_logic {op : LogicOp} {s : State} {d n m : Reg} :
    exec (.logic op d n m) s = some (s.write d (match op with
      | .and => s.gpr n &&& s.gpr m | .or => s.gpr n ||| s.gpr m
      | .xor => s.gpr n ^^^ s.gpr m)) := rfl

theorem exec_addi {s : State} {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15) :
    exec (.addi d n imm) s = some (s.write d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp [exec, hn, show imm < 32768 from h]

theorem exec_subi {s : State} {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15) :
    exec (.subi d n imm) s = some (s.write d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp [exec, hn, show imm ≤ 32768 from h]

theorem exec_li {s : State} {d : Reg} {imm : Nat} (h : imm < 2 ^ 15) :
    exec (.li d imm) s = some (s.write d (BitVec.ofNat 64 imm)) := by
  simp [exec, show imm < 32768 from h]

theorem exec_lis {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.lis d imm) s = some (s.write d ((imm ++ (0 : BitVec 16)).signExtend 64)) := rfl

theorem exec_ori {s : State} {d n : Reg} {imm : BitVec 16} :
    exec (.ori d n imm) s = some (s.write d (s.gpr n ||| imm.setWidth 64)) := rfl

theorem exec_oris {s : State} {d n : Reg} {imm : BitVec 16} :
    exec (.oris d n imm) s = some (s.write d (s.gpr n ||| imm.setWidth 64 <<< 16)) := rfl

theorem exec_rotr_w {s : State} {d n : Reg} {sh : Nat} (h : sh < 32) :
    exec (.rotr .w d n sh) s = some (s.write d (((s.gpr n).setWidth 32).rotateRight sh |>.setWidth 64)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_rotr_d {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.rotr .d d n sh) s = some (s.write d ((s.gpr n).rotateRight sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_lsr_w {s : State} {d n : Reg} {sh : Nat} (h : sh < 32) :
    exec (.lsr .w d n sh) s = some (s.write d (((s.gpr n).setWidth 32 >>> sh).setWidth 64)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_lsr_d {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsr .d d n sh) s = some (s.write d (s.gpr n >>> sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_lsl {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl d n sh) s = some (s.write d (s.gpr n <<< sh)) := by
  simp [exec, h]

theorem exec_mflr {s : State} {d : Reg} : exec (.mflr d) s = some (s.write d s.lr) := rfl

theorem exec_mtlr {s : State} {r : Reg} : exec (.mtlr r) s = some { s with lr := s.gpr r } := rfl

/-! ## Low words -/

theorem lo32_add (x y : BitVec 64) : (x + y).setWidth 32 = x.setWidth 32 + y.setWidth 32 :=
  BitVec.setWidth_add x y (by decide)

theorem lo32_sub (x y : BitVec 64) : (x - y).setWidth 32 = x.setWidth 32 - y.setWidth 32 := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, lo32_add, BitVec.setWidth_neg_of_le (by decide)]

theorem lo32_ext (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  simp

/-- `lis` of the high half then `ori` of the low half leave the word in the
low 32 bits. -/
theorem lis_ori (x : BitVec 32) :
    (((x.extractLsb' 16 16 ++ (0 : BitVec 16)).signExtend 64 |||
      (x.extractLsb' 0 16).setWidth 64)).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

/-- `lis_ori`, with the low word taken of each half, as `simp` leaves it. -/
theorem lis_ori' (x : BitVec 32) :
    ((x.extractLsb' 16 16 ++ (0 : BitVec 16)).signExtend 64).setWidth 32 |||
      (x.extractLsb' 0 16).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem rev32_readW (m : Mem) (a : Addr) :
    rev32 (m.readW a 32) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) : BitVec 32) :=
  byteRev32_readW m a

/-- A 64-bit byte-reversed load reads the eight bytes big-endian. -/
theorem rev64_readW (m : Mem) (a : Addr) :
    rev64 (m.readW a 64) = (m a ++ m (a + 1) ++ m (a + 1 + 1) ++ m (a + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1) ++ m (a + 1 + 1 + 1 + 1 + 1 + 1) ++
      m (a + 1 + 1 + 1 + 1 + 1 + 1 + 1) : BitVec 64) :=
  byteRev64_readW m a

end VG.PPC64LE

namespace VG.PPC64LE

theorem exec_sp {i : Instr} {s s' : State} (h : exec i s = some s') : s'.sp = s.sp := by
  cases i with
  | loadRev sz =>
    cases sz <;> simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h <;>
    obtain ⟨_, _, _, _, rfl⟩ := h <;> rfl
  | storeRev sz =>
    cases sz <;> simp only [exec, Option.bind_eq_some_iff, State.store] at h <;>
    (obtain ⟨_, _, h⟩ := h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
     subst h; rfl)
  | _ =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, State.write, State.load,
      State.store] at h
    (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl)
    | (obtain ⟨_, _, h⟩ := h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h;
       subst h; rfl)

theorem execBlock_sp {is : List Instr} {s s' : State} {t : List Leak}
    (h : VG.execBlock isa is s = some (s', t)) : s'.sp = s.sp := by
  induction is generalizing s t with
  | nil => simp only [VG.execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | cons i is ih =>
    simp only [VG.execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, _, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, -⟩ := he'
      rw [ih h]; exact exec_sp he

theorem push_sp {i : Instr} {s s₁ : State} (h : push i s = some s₁) : s₁.sp = s.sp - 48 := by
  cases i <;> simp only [push, reduceCtorEq] at h
  split at h <;> cases h; rfl

theorem pop_sp {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') :
    s₂.sp = s₁.sp ∧ s'.sp = s₂.sp + 48 := by
  cases j <;> simp only [pop, reduceCtorEq] at h
  split at h <;> cases h
  rename_i hc; exact ⟨hc.1, rfl⟩

/-- No modelled instruction changes `sp`, and frames restore it. -/
theorem Exec.sp {c : Prog isa} {s s' : State} {t : List Leak} (h : VG.Exec isa c s t s') :
    s'.sp = s.sp := by
  induction h with
  | block h => exact execBlock_sp h
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | call hc _ hr ih =>
    simp only [isa, call, ret, Option.some.injEq] at hc hr
    subst hc; split at hr <;> cases hr; exact ih
  | frame hp _ hq ih =>
    obtain ⟨h₁, h₂⟩ := pop_sp hq
    rw [h₂, ih, push_sp hp, BitVec.sub_add_cancel]

/-- Whether an instruction writes the link register. -/
def Instr.writesLr : Instr → Bool
  | .mtlr _ => true
  | _ => false

theorem exec_lr {i : Instr} {s s' : State} (h : exec i s = some s') (hi : i.writesLr = false) :
    s'.lr = s.lr := by
  cases i with
  | mtlr => simp [Instr.writesLr] at hi
  | loadRev sz =>
    cases sz <;> simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h <;>
    obtain ⟨_, _, _, _, rfl⟩ := h <;> rfl
  | storeRev sz =>
    cases sz <;> simp only [exec, Option.bind_eq_some_iff, State.store] at h <;>
    (obtain ⟨_, _, h⟩ := h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
     subst h; rfl)
  | _ =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, State.write, State.load,
      State.store] at h
    (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl)
    | (obtain ⟨_, _, h⟩ := h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h;
       subst h; rfl)

theorem execBlock_lr {is : List Instr} {s s' : State} {t : List Leak}
    (h : VG.execBlock isa is s = some (s', t)) (hi : is.all (fun i => !i.writesLr) = true) :
    s'.lr = s.lr := by
  induction is generalizing s t with
  | nil => simp only [VG.execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
    simp only [VG.execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, _, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, -⟩ := he'
      rw [ih h hi.2]; exact exec_lr he hi.1

/-- Code without calls or frames that never writes the link register leaves it
unchanged. -/
theorem Exec.lr {c : Prog isa} {s s' : State} {t : List Leak} (h : VG.Exec isa c s t s')
    (hc : c.noCalls = true) (hi : (instrs c).all (fun i => !i.writesLr) = true) : s'.lr = s.lr := by
  induction h with
  | block h => exact execBlock_lr h hi
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Bool.and_eq_true, instrs, List.all_append] at hc hi
    exact (ih₂ hc.2 hi.2).trans (ih₁ hc.1 hi.1)
  | iteT _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true, instrs, List.all_append] at hc hi
    exact ih hc.1 hi.1
  | iteF _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true, instrs, List.all_append] at hc hi
    exact ih hc.2 hi.2
  | loopExit _ _ ih => exact ih hc hi
  | loopNext _ _ _ ih₁ ih₂ => exact (ih₂ hc hi).trans (ih₁ hc hi)
  | call => simp [Code.noCalls] at hc
  | frame => simp [Code.noCalls] at hc

/-! Symbolic execution of a block, one instruction at a time (see `runStep`).
These are deliberately not proved by `rfl`: `simp` would use an `rfl` lemma
as a definitional unfolding, which the kernel then re-checks by unfolding the
structural recursion of `runBlock` over the whole remaining block, at every
instruction. -/

theorem runBlock_nil {s : State} : runBlock isa ([] : List Instr) s = some s := by
  rw [runBlock]

theorem runBlock_cons {i : Instr} {is : List Instr} {s : State} :
    runBlock isa (i :: is : List Instr) s = runStep isa (exec i s) is := by
  rw [runBlock]; rfl

theorem runStep_some {s : State} {is : List Instr} :
    runStep isa (some s : Option State) is = runBlock isa is s := by
  rw [runStep]; rfl

end VG.PPC64LE
