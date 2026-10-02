import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Copy
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb`'s saved registers

`absorb` saves the six callee-saved registers it uses at `scratch + 2176`,
where the functions it calls do not write, and restores them at the end.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.Stream.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat readW_writeW_other)

/-- The memory after saving the registers at `S + 2176`. -/
def absSavedMem (s : State) (S : Addr) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (S + BitVec.ofNat 64 d) (s.gpr r)) s.mem

theorem absSaved_read (s : State) (S : Addr) :
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2176) 64 = s.gpr .rbx ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2184) 64 = s.gpr .rbp ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2192) 64 = s.gpr .r12 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2200) 64 = s.gpr .r13 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2208) 64 = s.gpr .r14 ∧
    (absSavedMem s S).readW (S + BitVec.ofNat 64 2216) 64 = s.gpr .r15 := by
  simp only [absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide),
      readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_self64]

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2176 ≤ d) (h₂ : d + 8 ≤ 2224) :
    (⟨b + BitVec.ofNat 64 2176, 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2176) + BitVec.ofNat 64 (d - 2176) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem absSavedMem_frame (s : State) (S : Addr) :
    Frame [⟨S + BitVec.ofNat 64 2176, 48⟩] s.mem (absSavedMem s S) := by
  simp only [absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide)))

theorem save_ok (s : State) {S : Addr} (hS : s.gpr .r9 = S)
    (hw : ∀ d, 2176 ≤ d → d + 8 ≤ 2224 → InRegions s.wr (S + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa save s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r13 = s.gpr .rcx ∧
      s'.gpr .r14 = s.gpr .r8 ∧ s'.gpr .r15 = S ∧ s'.gpr .rdx = s.gpr .rdx ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .rdx == 0) ∧
      s'.mem = absSavedMem s S ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [save, saved, sOff, List.map, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea, offset_nat, hS, Nat.reduceAdd,
      hw 2176 (by decide) (by decide), hw 2184 (by decide) (by decide), hw 2192 (by decide) (by decide),
      hw 2200 (by decide) (by decide), hw 2208 (by decide) (by decide), hw 2216 (by decide) (by decide),
      ite_true, Option.map_some, execAlu, Option.bind_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false,
    BitVec.and_self, hS]
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩
  simp only [absSavedMem, saved, sOff, List.foldl, Nat.reduceAdd]

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .r15 = B)
    (hr : ∀ d, 2176 ≤ d → d + 8 ≤ 2224 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      s'.gpr .rbx = s.mem.readW (B + BitVec.ofNat 64 2176) 64 ∧
      s'.gpr .rbp = s.mem.readW (B + BitVec.ofNat 64 2184) 64 ∧
      s'.gpr .r12 = s.mem.readW (B + BitVec.ofNat 64 2192) 64 ∧
      s'.gpr .r13 = s.mem.readW (B + BitVec.ofNat 64 2200) 64 ∧
      s'.gpr .r14 = s.mem.readW (B + BitVec.ofNat 64 2208) 64 ∧
      s'.gpr .r15 = s.mem.readW (B + BitVec.ofNat 64 2216) 64 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp (config := {decide := true}) only [restore, saved, sOff, List.map, runBlock_cons, runStep_some,
      runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat, gpr_setReg, mem_setReg,
      rd_setReg, wr_setReg, ite_true, ite_false, Option.map_some, hb, Nat.reduceAdd,
      hr 2176 (by decide) (by decide), hr 2184 (by decide) (by decide), hr 2192 (by decide) (by decide),
      hr 2200 (by decide) (by decide), hr 2208 (by decide) (by decide), hr 2216 (by decide) (by decide)]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, mem_setReg, ite_true, ite_false]

end VG.Proof.CmacAes.Stream.X86_64
