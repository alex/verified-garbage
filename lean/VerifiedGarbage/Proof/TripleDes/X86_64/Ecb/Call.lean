import VerifiedGarbage.Proof.TripleDes.X86_64.StrongBlock
import VerifiedGarbage.Impl.TripleDes.X86_64.Ecb
import VerifiedGarbage.Proof.Framework.X86_64.Call

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def kept : List Reg := [.rdi, .rsi, .rdx, .rbp, .rsp]

theorem block_noSp (d : Direction) : NoSp (block d) := by
  have h : ((block d).allInstrs fun i => !Taint.clobbers i .rsp) = true := by
    cases d
    · change (encryptBlock.allInstrs _) = true
      lit_decide
    · change (decryptBlock.allInstrs _) = true
      lit_decide
  intro i hi
  rw [Code.allInstrs_eq] at h
  simpa using List.all_eq_true.mp h i hi

theorem blockCall_eq (d : Direction) : Impl.TripleDes.X86_64.Ecb.blockCall d =
    .call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
      (block d) := by cases d <;> rfl

theorem block_depth (d : Direction) : (block d).depth = 0 := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨s.gpr .rdi, 384⟩, ⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 512⟩] s.wr
  keyScratch : (Region.mk (s.gpr .rdi) 384).Disjoint ⟨s.gpr .rdx, 512⟩
  dataScratch : (Region.mk (s.gpr .rsi) 8).Disjoint ⟨s.gpr .rdx, 512⟩
  stackKey : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdi, 384⟩
  stackData : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rsi, 8⟩
  stackScratch : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rdx, 512⟩

structure CallPost (d : Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 512⟩, below (s.gpr .rsp) 8] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (s.gpr .rsi) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d
      (Spec.TripleDes.blockAt s.mem (s.gpr .rsi))

theorem call_ok (d : Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.X86_64.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := strongBlockContract d) (strongBlock_correct d)
    (block_noSp d) (by rw [block_depth]; decide)
    (rd := [⟨s.gpr .rdi, 384⟩]) (wr := [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 512⟩]) ?_ hp.reads hp.writes ?_
  · simp only [strongBlockContract, blockContract, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.stackData, hp.stackScratch⟩
  · intro s' rd wr callee frame _ ⟨s₂, mem₂, regs₂, out₂⟩
    refine ⟨?_, callee, rd, wr, ?_, ?_⟩
    · intro r hr
      by_cases hsp : r = .rsp
      · subst r
        exact callee .rsp (by decide)
      · have hkeep : ∀ q ∈ kept, q ∈ savedRegs ++ [Reg.rdi] ∨ q ∈ [Reg.rsi, .rdx, .rsp] := by decide
        have hreg : s₂.gpr r = (s.callEntry.withRegions
            [⟨s.gpr .rdi, 384⟩] [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 512⟩]).gpr r := by
          rcases hkeep r hr with h | h
          · exact out₂.saved r h
          · exact out₂.regs r h
        rw [State.withRegions_gpr, State.callEntry_gpr _ hsp] at hreg
        exact (regs₂ r hsp).symm.trans hreg
    · rw [block_depth] at frame
      exact frame
    · have stackFrame : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem :=
        (Frame.refl _ _).writeW List.mem_cons_self _ (below_call _ (by decide) (by decide))
      have key := VG.Proof.TripleDes.scheduleAt_eq_of_frame (s.gpr .rdi) stackFrame
        (by simpa only [List.mem_singleton, forall_eq] using hp.stackKey.symm)
      have input := VG.Proof.TripleDes.blockAt_eq_of_frame (s.gpr .rsi) stackFrame
        (by simpa only [List.mem_singleton, forall_eq] using hp.stackData.symm)
      have result := out₂.result
      simp only [State.withRegions_gpr, State.withRegions_mem,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), key, input, mem₂] at result
      exact result

end VG.Proof.TripleDes.X86_64.Ecb
