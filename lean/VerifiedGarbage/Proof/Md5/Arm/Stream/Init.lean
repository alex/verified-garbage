import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Md5.Arm.Compress
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Impl.Md5.Arm.Stream
import VerifiedGarbage.Proof.Md5.StateMem

/-!
# Streaming MD5 on ARMv7: `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Md5.Arm.Stream

open VG VG.Arm VG.Impl.Md5.Arm.Stream
open VG.Proof.Md5.Arm (contains_offset)
open VG.Proof.MdStream.Arm (WP.cons wp_str)
open VG.Spec.Md5 (stateAt H0)

/-- The three instructions storing the 32-bit word `x` at `[r0 + off]`. -/
def word (x : BitVec 32) (off : Nat) : List Instr :=
  [.movw .r12 (x.extractLsb' 0 16), .movt .r12 (x.extractLsb' 16 16), .str .r12 .r0 off]

theorem init_eq : init = .block (word H0[0] 0 ++ word H0[1] 4 ++ word H0[2] 8 ++ word H0[3] 12) := rfl

theorem word_ok {x : BitVec 32} {off : Nat} (ho : off < 4096) {rest : List Instr}
    {s : State} {Q : State → Prop} (hfit : (s.gpr .r0).toNat + off < 2 ^ 32)
    (hout : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (State.addr (s.gpr .r0) + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word x off ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine WP.cons rfl (WP.cons rfl ?_)
  refine wp_str ho (by simp only [State.setReg]; exact addr_add hfit) hout fun s' u => ?_
  refine k s' (fun r hr => by rw [u.gpr]; simp [State.setReg, hr]) u.rd u.wr u.sp ?_
  rw [u.mem]
  simp only [State.setReg, ite_true, movw_movt]

theorem init_correct {s₀ : State} (hp : Proof.Md5.initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Md5.initArm.post s₀ s' := by
  obtain ⟨-, hwr, hfit⟩ := hp
  have o : ∀ k, k < 4 → InRegions s₀.wr (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨⟨State.addr (s₀.gpr .r0), 80⟩, by simp [hwr], contains_offset (by omega) (by omega)⟩
  rw [init_eq, ← List.append_nil (_ ++ word H0[3] 12)]
  simp only [List.append_assoc]
  refine word_ok (by decide) (by omega) (o 0 (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr .r0 = s₀.gpr .r0 := g1 _ (by decide)
  refine word_ok (by decide) (by rw [k1]; omega) (by rw [wr1, k1]; exact o 1 (by omega))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr .r0 = s₀.gpr .r0 := by rw [g2 _ (by decide), k1]
  refine word_ok (by decide) (by rw [k2]; omega) (by rw [wr2, wr1, k2]; exact o 2 (by omega))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr .r0 = s₀.gpr .r0 := by rw [g3 _ (by decide), k2]
  have w3 : s3.wr = s₀.wr := by rw [wr3, wr2, wr1]
  refine word_ok (by decide) (by rw [k3]; omega) (by rw [w3, k3]; exact o 3 (by omega))
    fun s4 g4 _ _ sp4 m4 => WP.block_nil ?_
  have k4 : ∀ r, r ≠ .r12 → s4.gpr r = s₀.gpr r := fun r h => by
    rw [g4 r h, g3 r h, g2 r h, g1 r h]
  have hm : s4.mem = Proof.Md5.StateMem.writeState s₀.mem (State.addr (s₀.gpr .r0)) H0 := by
    rw [m4, m3, m2, m1, k3, k2, k1]
    rfl
  refine ⟨⟨fun r hr => k4 r ?_, by rw [sp4, sp3, sp2, sp1]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · show Spec.Md5.Repr s4.mem (State.addr (s₀.gpr .r0)) []
    rw [hm]
    exact Proof.Md5.Stream.repr_nil (Proof.Md5.StateMem.stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 80⟩]

theorem init_verified : Verified Arm.target init Proof.Md5.initArm := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, by decide⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0]) (fun _ _ _ _ hp => ?_) (by taint_decide)
    exact Taint.agree_ofRegs fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp

end VG.Proof.Md5.Arm.Stream
