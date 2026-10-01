import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Layout

/-! Short symbolic executions for the complete verifier's call arguments. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (stk shaScratch)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey (ea_stk add_add sx32 zx32 ne_cs)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def InitArgs (L : Lay) (t : State) : Prop := t.gpr .rdi = L.scr

theorem initArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block initArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ InitArgs L t' := by
  have hin := hc.inFr (d := 144) (by omega) (by omega)
  refine WP.of_runBlock ⟨t.setReg .rdi L.scr, ?_, ?_⟩
  · simp only [initArgs, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, hc.ea_fr, hin, ite_true, Option.map_some, hc.pScr]
  exact ⟨hc.regs rfl rfl rfl rfl fun r hr => RegUpd.gpr_setReg_of_ne _ _ (ne_cs hr (by decide)), rfl,
    RegUpd.gpr_setReg_self _ _ _⟩

def UpdArgs (L : Lay) (count : BitVec 64) (p : Addr) (n : BitVec 64) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = count ∧ t.gpr .rdx = p ∧ t.gpr .rcx = n ∧
    t.gpr .r8 = L.scr + BitVec.ofNat 64 192

theorem prefixArgs_ok {t : State} (hc : Ctx L g mx m₀ t) (source count : Nat)
    (hs : source + 8 ≤ 168) (hcount : count < 2 ^ 32) (p : Addr)
    (hp : t.mem.readW (L.B + BitVec.ofNat 64 (16 + source)) 64 = p) :
    WP isa (.block (prefixArgs source count)) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      UpdArgs L (BitVec.ofNat 64 count) p 32 t' := by
  have h144 := hc.inFr (d := 144) (by omega) (by omega)
  have hsrc := hc.inFr (d := 16 + source) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [prefixArgs, scrPtr, shaScratch, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.load64,
    State.setReg32, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h144, hsrc, Option.some.injEq, exists_eq_left', hc.pScr, hp, UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, zx32 hcount,
    trivial, rfl, by rw [sx32 (by omega)]⟩

theorem messageArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block messageArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      UpdArgs L 64 L.msg L.len t' := by
  have h144 := hc.inFr (d := 144) (by omega) (by omega)
  have h160 := hc.inFr (d := 160) (by omega) (by omega)
  have h168 := hc.inFr (d := 168) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [messageArgs, scrPtr, shaScratch, fScratch, fMessage, fLength,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, readSrc32, State.load64, State.setReg32, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h144, h160, h168,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pMsg, hc.pLen, UpdArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl,
    trivial, trivial, by rw [sx32 (by omega)]⟩

def FinArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.scr ∧ t.gpr .rsi = L.len + 64 ∧ t.gpr .rdx = L.B + BitVec.ofNat 64 80 ∧
    t.gpr .rcx = L.scr + BitVec.ofNat 64 192

theorem finalizeArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block finalizeArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ FinArgs L t' := by
  have h144 := hc.inFr (d := 144) (by omega) (by omega)
  have h160 := hc.inFr (d := 160) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [finalizeArgs, scrPtr, shaScratch, fScratch, fLength,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h144, h160, Option.some.injEq, exists_eq_left', hc.pScr, hc.pLen, FinArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, rfl,
    by rw [show (64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 64 from rfl, add_add],
    by rw [sx32 (by omega)]⟩

end VG.Proof.Ed25519.X86_64.VerifyMessage
