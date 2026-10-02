import VerifiedGarbage.Proof.AesGcm.Arm.Entry

/-!
# AES-GCM on ARMv7: stack arguments read after other code

Untrusted: everything here is checked by Lean. `ArgsKeep n s₀ s`: the stack
pointer, the permissions and the first `n` stack arguments of `s` are those
of `s₀`; code that writes only regions apart from the arguments keeps it
(`ArgsKeep.frame`), and `ldr rX, [sp, #4i]` then loads argument `i` of `s₀`
(`ArgsKeep.read`).
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm

theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp only [stackArgAddr, Nat.mul_zero, add_ofNat_zero]

theorem args_sp {s s' : State} (h : s'.sp = s.sp) (n : Nat) : args s' n = args s n := by
  simp only [args, stackArgAddr, h]

/-- The stack below `sp` is apart from the stack arguments. -/
theorem below_args (s : State) {n : Nat} (hf : s.sp.toNat + 4 * n ≤ 2 ^ 32) : (below s.sp).Disjoint (args s n) := by
  simp only [args, argAddr_zero]
  exact (Offset.base_disjoint_below (State.addr s.sp) (n := 8) (k := 4 * n) (by omega)).symm

/-- The low word of a 64-bit length gives it modulo 16. -/
theorem low_mod16 {hi lo : BitVec 32} {L : Nat} (h : hi ++ lo = BitVec.ofNat 64 L) : lo.toNat % 16 = L % 16 := by
  have e := congrArg BitVec.toNat h
  rw [Proof.Gcm.toNat_append, BitVec.toNat_ofNat] at e
  have : L % 2 ^ 64 % 16 = L % 16 := Nat.mod_mod_of_dvd _ (by decide)
  omega

structure ArgsKeep (n : Nat) (s₀ s : State) : Prop where
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  arg : ∀ i < n, stackArg s i = stackArg s₀ i

theorem ArgsKeep.refl (n : Nat) (s : State) : ArgsKeep n s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem ArgsKeep.of_eq {n : Nat} {s₀ s s' : State} (h : ArgsKeep n s₀ s) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgsKeep n s₀ s' :=
  ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, fun i hi => by
    rw [← h.arg i hi]; simp only [stackArg, stackArgAddr, hm, hsp]⟩

theorem ArgsKeep.frame {n : Nat} {s₀ s s' : State} (h : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    {rs : List Region} (hfr : Frame rs s.mem s'.mem) (hd : ∀ r ∈ rs, (args s₀ n).Disjoint r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : ArgsKeep n s₀ s' := by
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, fun i hi => ?_⟩
  rw [← h.arg i hi]
  exact arg_frame hsp (by rw [h.sp]; exact hf) hfr (fun r hr => by rw [args_sp h.sp]; exact hd r hr) hi

theorem ArgsKeep.trans {n : Nat} {s₀ s s' : State} (h : ArgsKeep n s₀ s) (h' : ArgsKeep n s s') : ArgsKeep n s₀ s' :=
  ⟨h'.sp.trans h.sp, h'.rd.trans h.rd, h'.wr.trans h.wr, fun i hi => (h'.arg i hi).trans (h.arg i hi)⟩

theorem ArgsKeep.read {n : Nat} {s₀ s : State} (h : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args s₀ n ∈ s₀.rd) {i : Nat} (hi : i < n) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 32 = stackArg s₀ i :=
  ⟨arg_in hi (by rw [h.sp]; exact hf) (by rw [h.rd, args_sp h.sp]; exact hin), h.arg i hi⟩

/-- `ArgsKeep.read`, at a literal offset. -/
theorem ArgsKeep.at {n : Nat} {s₀ s : State} (h : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args s₀ n ∈ s₀.rd) (i : Nat) {off : Nat} (hi : i < n) (hoff : 4 * i = off) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4 ∧
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32 = stackArg s₀ i := by
  subst hoff; exact h.read hf hin hi

end VG.Proof.AesGcm.Arm
