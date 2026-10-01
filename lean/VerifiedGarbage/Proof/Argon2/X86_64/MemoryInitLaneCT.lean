import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitBlockCT
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLane

/-! # The two leading blocks of a lane have a public execution trace -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

structure LaneReady (memory : Addr) (bytes d : Nat) (s : State) : Prop where
  space : Space s memory bytes
  destination : s.gpr .r14 = memory + BitVec.ofNat 64 d

def RelatedLane (memory : Addr) (bytes d : Nat) (s t : State) : Prop :=
  LaneReady memory bytes d s ∧ LaneReady memory bytes d t ∧ AgreeSaved s t

theorem BlockDone.laneReady {s t : State} {column : Nat} {memory : Addr} {bytes d : Nat}
    (h : BlockDone s t column) (ready : LaneReady memory bytes d s) :
    LaneReady memory bytes d t :=
  ⟨ready.space.same h.wr (h.regs .rbp (by decide)) (h.regs .rbx (by decide))
    (h.regs .rsp (by decide)), (h.regs .r14 (by decide)).trans ready.destination⟩

theorem block_lane_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs calleeSaved)
      (.block (blockArgs column)) hint).isSome = true)
    (memory : Addr) (bytes d : Nat) (bound : d + 1024 ≤ bytes) :
    RelCT isa (RelatedLane memory bytes d) (block name (HPrime.hash v) column)
      (RelatedLane memory bytes d) := by
  have h := ((block_rel v name column ct).mono
    (P' := RelatedLane memory bytes d) (fun _ _ hp =>
      ⟨hp.1.space.blockReady hp.1.destination bound,
        hp.2.1.space.blockReady hp.2.1.destination bound, hp.2.2⟩)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨block_ok v name s column (hp.1.space.blockReady hp.1.destination bound),
        block_ok v name t column (hp.2.1.space.blockReady hp.2.1.destination bound)⟩)
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ha.laneReady hp.1, hb.laneReady hp.2.1, pub⟩)

theorem advance_rel : RelCT isa AgreeSaved
    (.block [.alu .add .r14 (.imm 1024)]) AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) calleeSaved
  taint_decide

theorem advance_lane_rel (memory : Addr) (bytes d : Nat) :
    RelCT isa (RelatedLane memory bytes d) (.block [.alu .add .r14 (.imm 1024)])
      (RelatedLane memory bytes (d + 1024)) := by
  have h := (advance_rel.mono (P' := RelatedLane memory bytes d)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s t _ => ⟨advance_ok s, advance_ok t⟩)
  have ready {s t : State} (h : Advanced s t) (hs : LaneReady memory bytes d s) :
      LaneReady memory bytes (d + 1024) t := by
    refine ⟨hs.space.same h.wr (h.other .rbp (by decide))
      (h.other .rbx (by decide)) (h.other .rsp (by decide)), ?_⟩
    rw [h.destination, hs.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ready ha hp.1, ready hb hp.2.1, pub⟩)

theorem laneEnd_rel : RelCT isa AgreeSaved
    (.block [.alu .add .r14 (.reg .r13), .alu .sub .r14 (.imm 1024),
      .alu .add .r12 (.imm 1), .alu .sub .r15 (.imm 1)]) AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs calleeSaved)
    (fun _ _ h => Taint.agree_ofRegs h) calleeSaved
  taint_decide

theorem lane_rel (v : Proof.Blake2.X86_64.Backend) (name : String)
    (memory : Addr) (bytes d : Nat) (bound : d + 2048 ≤ bytes) :
    RelCT isa (RelatedLane memory bytes d) (lane name (HPrime.hash v)) AgreeSaved := by
  exact (block_lane_rel v name 0 ⟨_, by taint_decide⟩ memory bytes d (by omega)).seq
    ((advance_lane_rel memory bytes d).seq
    ((block_lane_rel v name 1 ⟨_, by taint_decide⟩ memory bytes (d + 1024) (by omega)).seq
      (laneEnd_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h))))

end VG.Proof.Argon2.X86_64.MemoryInit
