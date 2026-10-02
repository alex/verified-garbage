import VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock
import VerifiedGarbage.Impl.TripleDes.X86.Ecb
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.Rc2.X86.Cbc (callWithGpr)

def kept : List Reg := [.ebx, .esi, .edi, .ebp, .esp]

def blockCode (d : Spec.TripleDes.Direction) : Prog isa :=
  match d with | .encrypt => encryptBlock | .decrypt => decryptBlock

theorem block_nosp (d : Spec.TripleDes.Direction) : NoSp (blockCode d) := by
  apply NoSp.of_all
  cases d
  · change encryptBlock.allInstrs _ = true
    lit_decide
  · change decryptBlock.allInstrs _ = true
    lit_decide

theorem block_stack (d : Spec.TripleDes.Direction) : stackUse (blockCode d) = 0 := by
  cases d <;> simp only [blockCode, encryptBlock, decryptBlock, block, blockBody, pass, stackUse,
    Nat.max_self]

theorem blockCall_eq (d : Spec.TripleDes.Direction) : Impl.TripleDes.X86.Ecb.blockCall d =
    .frame (.push [.ebp, .esi, .ebx])
      (.call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
        (blockCode d)) (.pop .eax 3) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨addr32 (s.gpr .ebx), 384⟩, ⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩] s.wr
  keyScratch : (Region.mk (addr32 (s.gpr .ebx)) 384).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩
  dataScratch : (Region.mk (addr32 (s.gpr .esi)) 8).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩
  keyFit : (s.gpr .ebx).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .esi).toNat + 8 ≤ 2 ^ 32
  bufFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32
  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .ebx), 384⟩
  stackData : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .esi), 8⟩
  stackBuf : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩, below (s.gpr .esp) 16] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (addr32 (s.gpr .esi)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx))) d (Spec.TripleDes.blockAt s.mem (addr32 (s.gpr .esi)))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.X86.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  let rs : List Reg := [.ebp, .esi, .ebx]
  have hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  have a0 : arg sE 0 = s.gpr .ebx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a1 : arg sE 1 = s.gpr .esi := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a2 : arg sE 2 = s.gpr .ebp := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by rw [callEntry_esp']; rfl
  have b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  have r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64, 4⟩ (below (s.gpr .esp) 16) :=
    Region.sub_prefix (by decide)
  have hcode : blockCode d = block d := by cases d <;> rfl
  refine callWithGpr (c := blockCode d) (k := blockContract d)
    (by rw [hcode]; exact block_correct d) (block_nosp d) (by decide) hrs
    (by rw [block_stack]; exact hp.stackLo) (rd := [⟨addr32 (s.gpr .ebx), 384⟩, ⟨argAddr sE 0, 12⟩])
    (wr := [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩]) ⟨?_, ?_, ?_⟩ ?_
  · change (blockContract d).pre (sE.withRegions _ _)
    simp only [blockContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.stackData.sub_left b12,
      hp.stackBuf.sub_left b12, hp.stackData.sub_left r4, hp.stackBuf.sub_left r4,
      hp.keyFit, hp.dataFit, hp.bufFit, ?_⟩
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  · intro s' rd wr cs frame ⟨s₂, mem₂, gpr₂, post⟩
    rw [block_stack] at frame
    change (blockContract d).post (sE.withRegions _ _) s₂ at post
    simp only [blockContract, State.withRegions_mem, arg_withRegions,
      a0, a1, mem₂] at post
    have stackFrame := callEntry_frame fit hrs
    change Frame [below (s.gpr .esp) 16] s.mem sE.mem at stackFrame
    refine ⟨?_, cs, rd, wr, frame, ?_⟩
    · intro r hr
      have fact : ∀ r ∈ kept, r ∈ calleeSaved := by decide
      exact cs r (fact r hr)
    · rw [post,
        VG.Proof.TripleDes.scheduleAt_eq_of_frame (p := addr32 (s.gpr .ebx)) stackFrame
          (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackKey.symm),
        VG.Proof.TripleDes.blockAt_eq_of_frame (p := addr32 (s.gpr .esi)) stackFrame
          (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackData.symm)]

end VG.Proof.TripleDes.X86.Ecb
