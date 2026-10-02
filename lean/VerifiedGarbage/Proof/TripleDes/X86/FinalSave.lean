import VerifiedGarbage.Proof.TripleDes.X86.FinalPermutation
import VerifiedGarbage.Proof.TripleDes.X86.RoundStep

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86

def finalMem (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 6) (s.gpr .eax)).writeW
    (wordAddr (s.gpr .ebp) 7) (s.gpr .ebx)

theorem finalStores_ok (s : State) (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa [.store (memOp .ebp 24) .eax, .store (memOp .ebp 28) .ebx] s = some s' ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = finalMem s := by
  have h6 := hok.slotIn 6 (by decide)
  have h7 := hok.slotIn 7 (by decide)
  simp only [wordAddr, addr, sboxCfg] at h6 h7
  refine ⟨{s with mem := finalMem s}, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.ea,
      memOp, h6, h7, ite_true]
    rfl, rfl, rfl, rfl, rfl⟩

structure FinalSavePost (x : BitVec 64) (s s' : State) : Prop where
  lo : s'.mem.readW (wordAddr (s.gpr .ebp) 6) 32 = x.setWidth 32
  hi : s'.mem.readW (wordAddr (s.gpr .ebp) 7) 32 = (x >>> 32).setWidth 32
  bp : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [workRegion s] s.mem s'.mem

theorem finalSave_ok (s : State) (hok : Ok sboxCfg s) :
    WP isa (.block finalSave) s (FinalSavePost
      (Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .esi ++ s.gpr .edi)) s) := by
  rw [finalSave, WP.block_append_iff]
  obtain ⟨s₁, run₁, lo₁, hi₁, rd₁, wr₁, sp₁, mem₁, regs₁⟩ := fp_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have bp₁ := regs₁ .ebp (by decide +kernel)
  obtain ⟨s₂, run₂, gpr₂, rd₂, wr₂, mem₂⟩ := finalStores_ok s₁ (hok.congr bp₁ bp₁ rd₁ wr₁)
  have hsep : Mem.Sep (wordAddr (s.gpr .ebp) 6) 4 (wordAddr (s.gpr .ebp) 7) 4 := by
    rw [wordAddr, wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega),
      addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
    exact Offset.sep _ (by decide) (by decide) (by decide)
  have hm : s₂.mem = (s.mem.writeW (wordAddr (s.gpr .ebp) 6) (s₁.gpr .eax)).writeW
      (wordAddr (s.gpr .ebp) 7) (s₁.gpr .ebx) := by rw [mem₂, finalMem, bp₁, mem₁]
  refine WP.of_runBlock ⟨s₂, run₂, ⟨?_, ?_, by rw [gpr₂]; exact bp₁,
    by rw [gpr₂]; exact sp₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  · rw [hm, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32, lo₁]
    rfl
  · rw [hm, Mem.readW_writeW_self32, hi₁]
    rfl
  · have h6 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 6) 4 := by
      rw [wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
      exact Offset.contains _ (by decide) (by decide) (by decide)
    have h7 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 7) 4 := by
      rw [wordAddr, addr_eq (by have h := hok.fit; change (s.gpr .ebp).toNat + 512 ≤ 2^32 at h; omega)]
      exact Offset.contains _ (by decide) (by decide) (by decide)
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ h6).writeW
      (List.mem_singleton_self _) _ h7

end VG.Proof.TripleDes.X86
