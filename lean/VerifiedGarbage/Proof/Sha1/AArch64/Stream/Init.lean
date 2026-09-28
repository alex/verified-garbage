import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Common

/-!
# Streaming SHA-1 on AArch64: `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha1.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha1.AArch64.Stream
open VG.Proof.Sha1.AArch64 (writeState stateAt_writeState contains_offset)
open VG.Spec.Sha1 (stateAt H0)

/-- The three instructions storing the 32-bit word `x` at `[x0 + off]`. -/
def word (x : BitVec 32) (off : Nat) : List Instr :=
  [.movz .w .x9 (x.extractLsb' 0 16) 0, .movk .w .x9 (x.extractLsb' 16 16) 1, .str .w .x9 .x0 off]

theorem init_eq : init = .block (word H0[0] 0 ++ word H0[1] 4 ++ word H0[2] 8 ++ word H0[3] 12 ++
    word H0[4] 16) := rfl

/-- `movz` of the low half then `movk` of the high half, then a 32-bit store. -/
theorem movzk (x : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (x.extractLsb' 0 16))) &&& (65535 : BitVec 32) |||
        BitVec.setWidth 32 (x.extractLsb' 16 16) <<< 16)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

theorem word_ok {x : BitVec 32} {off : Nat} (ho : off % 4 = 0 ∧ off < 16384) {rest : List Instr}
    {s : State} {Q : State → Prop} (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 off) 4)
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word x off ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine WP.cons exec_movz_w (WP.cons exec_movk_w (WP.cons (exec_str_w ho ?_) (k _ ?_ rfl rfl rfl ?_)))
  · simpa [State.write] using hout
  · intro r hr; simp [State.write, hr]
  · simp only [State.write, ite_true]
    congr 1
    exact movzk x

theorem init_correct {s₀ : State} (hp : Proof.Sha1.initAArch64.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha1.initAArch64.post s₀ s' := by
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ k, k < 5 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 :=
    fun k hk => ⟨⟨s₀.gpr .x0, 84⟩, by simp [hwr], contains_offset (by omega) (by omega)⟩
  rw [init_eq, ← List.append_nil (_ ++ word H0[4] 16)]
  simp only [List.append_assoc]
  refine word_ok (by decide) (o 0 (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  refine word_ok (by decide) (by rw [wr1, g1 _ (by decide)]; exact o 1 (by omega))
    fun s2 g2 _ wr2 sp2 m2 => ?_
  refine word_ok (by decide) (by rw [wr2, wr1, g2 _ (by decide), g1 _ (by decide)]; exact o 2 (by omega))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have w3 : s3.wr = s₀.wr := by rw [wr3, wr2, wr1]
  have k3 : s3.gpr .x0 = s₀.gpr .x0 := by rw [g3 _ (by decide), g2 _ (by decide), g1 _ (by decide)]
  refine word_ok (by decide) (by rw [w3, k3]; exact o 3 (by omega)) fun s4 g4 _ wr4 sp4 m4 => ?_
  have k4 : ∀ r, r ≠ .x9 → s4.gpr r = s₀.gpr r := fun r h => by rw [g4 r h, g3 r h, g2 r h, g1 r h]
  have w4 : s4.wr = s₀.wr := by rw [wr4, wr3, wr2, wr1]
  refine word_ok (by decide) (by rw [w4, k4 _ (by decide)]; exact o 4 (by omega))
    fun s5 g5 _ _ sp5 m5 => WP.block_nil ?_
  have k5 : ∀ r, r ≠ .x9 → s5.gpr r = s₀.gpr r := fun r h => by rw [g5 r h, k4 r h]
  have hm : s5.mem = writeState s₀.mem (s₀.gpr .x0) H0 := by
    rw [m5, m4, m3, m2, m1]
    simp only [k4 _ (show Reg.x0 ≠ .x9 by decide),
      g3 _ (show Reg.x0 ≠ .x9 by decide), g2 _ (show Reg.x0 ≠ .x9 by decide),
      g1 _ (show Reg.x0 ≠ .x9 by decide)]
    rfl
  refine ⟨⟨fun r hr => k5 r ?_, by rw [sp5, sp4, sp3, sp2, sp1]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · show Spec.Sha1.Repr s5.mem (s₀.gpr .x0) []
    rw [hm]
    exact Proof.Sha1.Stream.repr_nil (stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 84⟩]

theorem init_verified : Verified AArch64.target init Proof.Sha1.initAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    refine ⟨h.2, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1

end VG.Proof.Sha1.AArch64.Stream
