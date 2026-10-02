import VerifiedGarbage.Proof.TripleDes.Arm.VerifiedBlock
import VerifiedGarbage.Impl.TripleDes.Arm.Ecb
import VerifiedGarbage.Proof.Framework.Arm.Call

namespace VG.Proof.TripleDes.Arm.Ecb
open VG VG.Arm VG.Impl.TripleDes.Arm

def kept : List Reg := [.r0, .r1, .r2, .r3]
def savedAcrossCall : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

def callContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { blockContract d with
    post := fun s s' => (blockContract d).post s s' ∧ ∀ r ∈ kept, s'.gpr r = s.gpr r }

theorem block_correct' (d : Spec.TripleDes.Direction) (s : State) (hs : (callContract d).pre s) :
    ∃ t s', Exec isa (block d) s t s' ∧ abiPreserved s s' ∧ (callContract d).post s s' := by
  have hp := headPre_of_contract d s hs
  have writes : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    intro t ht
    have fit := hs.2.2.2.2.2.1
    rw [addr_add (by omega_using [fit, ht]), hs.2.1]
    exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp,
      Offset.contains_base _ (by omega_using [ht]) (by omega_using [ht])⟩
  obtain ⟨t, s', he, post⟩ := block_ok (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0)))
    (s.gpr .r0) d s hp writes
  refine ⟨t, s', he, ⟨?_, post.sp⟩, post.result, ?_⟩
  · intro r hr
    have covered : ∀ r ∈ preserved, r ∈ savedRegs := by decide
    exact post.saved r (covered r hr)
  · intro r hr
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact post.pointer
    · exact post.regs .r1 (by decide)
    · exact post.regs .r2 (by decide)
    · exact post.regs .r3 (by decide)

theorem blockCall_eq (d : Spec.TripleDes.Direction) : Impl.TripleDes.Arm.Ecb.blockCall d =
    .call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
      (block d) := by cases d <;> rfl

structure CallPre (s : State) : Prop where
  reads : Covers [⟨State.addr (s.gpr .r0), 384⟩, ⟨State.addr (s.gpr .r1), 8⟩,
    ⟨State.addr (s.gpr .r2), 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] s.wr
  keyScratch : (Region.mk (State.addr (s.gpr .r0)) 384).Disjoint ⟨State.addr (s.gpr .r2), 512⟩
  dataScratch : (Region.mk (State.addr (s.gpr .r1)) 8).Disjoint ⟨State.addr (s.gpr .r2), 512⟩
  keyFit : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  scratchFit : (s.gpr .r2).toNat + 512 ≤ 2 ^ 32

structure CallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ savedAcrossCall, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (State.addr (s.gpr .r1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (State.addr (s.gpr .r0))) d
      (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)))

theorem call_ok (d : Spec.TripleDes.Direction) (s : State) (hp : CallPre s) :
    WP isa (Impl.TripleDes.Arm.Ecb.blockCall d) s (CallPost d s) := by
  rw [blockCall_eq]
  refine WP.call (k := callContract d) (block_correct' d)
    (rd := [⟨State.addr (s.gpr .r0), 384⟩])
    (wr := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩])
    ?_ hp.reads hp.writes ?_ (by cases d <;> rfl)
  · simp only [callContract, blockContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs)]
    exact ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.keyFit, hp.dataFit, hp.scratchFit⟩
  · intro s' rd wr sp frame callee regs out
    have sep : ∀ r ∈ kept, r ∉ linkRegs := by decide
    have saved : ∀ r ∈ savedAcrossCall, r ∈ preserved ∧ r ≠ .lr := by decide
    refine ⟨?_, fun r hr => callee r (saved r hr).1 (saved r hr).2, rd, wr, frame, ?_⟩
    · intro r hr
      have h := out.2 r hr
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (sep r hr)] at h
      exact h
    · have h := out.1
      change Spec.TripleDes.blockAt s'.mem _ = blockResult _ d _ at h
      simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
        State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs)] at h
      exact h

end VG.Proof.TripleDes.Arm.Ecb
