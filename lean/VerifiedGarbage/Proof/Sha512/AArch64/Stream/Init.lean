import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Common

/-!
# Streaming SHA-512 on AArch64: `init`

Untrusted: everything here is checked by Lean. One proof for every initial
hash value `iv`.
-/

namespace VG.Proof.Sha512.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha512.AArch64.Stream
open VG.Impl.Sha512.AArch64 (movImm64)
open VG.Proof.Sha512.AArch64 (writeState stateAt_writeState contains_offset)
open VG.Spec.Sha512 (HashValue stateAt)

/-- The five instructions storing the 64-bit word `x` at `[x0 + off]`. -/
def word (x : BitVec 64) (off : Nat) : List Instr := movImm64 .x9 x ++ [.str .x .x9 .x0 off]

theorem init_eq (iv : HashValue) : init iv = .block (word iv[0] 0 ++ word iv[1] 8 ++ word iv[2] 16 ++
    word iv[3] 24 ++ word iv[4] 32 ++ word iv[5] 40 ++ word iv[6] 48 ++ word iv[7] 56) := rfl

theorem word_ok {x : BitVec 64} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768) {rest : List Instr}
    {s : State} {Q : State → Prop} (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 off) 8)
    (k : ∀ s', (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 off) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word x off ++ rest)) s Q := by
  simp only [word, movImm64, List.cons_append, List.nil_append]
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl
    (WP.cons (exec_str_x ho ?_) (k _ ?_ rfl rfl rfl ?_)))))
  · simpa [State.write] using hout
  · intro r hr; simp [State.write, hr]
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    congr 1
    exact movz_movk64' x

theorem init_correct {s₀ : State} (iv : HashValue) (hp : (Proof.Sha512.initAArch64 iv).pre s₀) :
    WP isa (init iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha512.initAArch64 iv).post s₀ s' := by
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ k, k < 8 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k hk => ⟨⟨s₀.gpr .x0, 192⟩, by simp [hwr], contains_offset (by omega) (by omega)⟩
  rw [init_eq, ← List.append_nil (_ ++ word iv[7] 56)]
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
    fun s5 g5 _ wr5 sp5 m5 => ?_
  refine word_ok (by decide) (by rw [wr5, w4, g5 _ (by decide), k4 _ (by decide)]; exact o 5 (by omega))
    fun s6 g6 _ wr6 sp6 m6 => ?_
  have w6 : s6.wr = s₀.wr := by rw [wr6, wr5, w4]
  have k6 : s6.gpr .x0 = s₀.gpr .x0 := by rw [g6 _ (by decide), g5 _ (by decide), k4 _ (by decide)]
  refine word_ok (by decide) (by rw [w6, k6]; exact o 6 (by omega)) fun s7 g7 _ wr7 sp7 m7 => ?_
  have w7 : s7.wr = s₀.wr := by rw [wr7, w6]
  have k7 : s7.gpr .x0 = s₀.gpr .x0 := by rw [g7 _ (by decide), k6]
  refine word_ok (by decide) (by rw [w7, k7]; exact o 7 (by omega)) fun s8 g8 _ _ sp8 m8 =>
    WP.block_nil ?_
  have k8 : ∀ r, r ≠ .x9 → s8.gpr r = s₀.gpr r := fun r h => by
    rw [g8 r h, g7 r h, g6 r h, g5 r h, k4 r h]
  have hm : s8.mem = writeState s₀.mem (s₀.gpr .x0) iv := by
    rw [m8, m7, m6, m5, m4, m3, m2, m1]
    simp only [g7 _ (show Reg.x0 ≠ .x9 by decide), g6 _ (show Reg.x0 ≠ .x9 by decide),
      g5 _ (show Reg.x0 ≠ .x9 by decide), k4 _ (show Reg.x0 ≠ .x9 by decide),
      g3 _ (show Reg.x0 ≠ .x9 by decide), g2 _ (show Reg.x0 ≠ .x9 by decide),
      g1 _ (show Reg.x0 ≠ .x9 by decide)]
    rfl
  refine ⟨⟨fun r hr => k8 r ?_, by rw [sp8, sp7, sp6, sp5, sp4, sp3, sp2, sp1]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · show Spec.Sha512.Repr iv s8.mem (s₀.gpr .x0) []
    rw [hm]
    exact Proof.Sha512.Stream.repr_nil (stateAt_writeState _ _ _)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 192⟩]

/-- The hint for `init 0`, which is also one for `init iv`. -/
abbrev initHint : VG.Taint.Hint taint.T := VG.Taint.hintOf taint (Taint.ofRegs [.x0]) (init 0)

/-- The taint check never looks at an immediate, so its result on `init iv`
is its result on `init 0`, which is decided. -/
theorem init_check (iv : HashValue) :
    (taint.check (Taint.ofRegs [.x0]) (init iv) initHint).isSome = true := by
  have h : (taint.check (Taint.ofRegs [.x0]) (init 0) initHint).isSome = true := by taint_decide
  rw [show taint.check (Taint.ofRegs [.x0]) (init iv) initHint =
    taint.check (Taint.ofRegs [.x0]) (init 0) initHint from rfl]
  exact h

theorem init_verified (iv : HashValue) :
    Verified AArch64.target (init iv) (Proof.Sha512.initAArch64 iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct iv hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0]) ?_ (init_check iv)
    intro s₁ s₂ _ _ h
    refine ⟨h.2, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h.1

end VG.Proof.Sha512.AArch64.Stream
