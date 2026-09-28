import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Gcm.X86_64.Product
import VerifiedGarbage.Proof.Gcm.X86_64.Reduce
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-!
# GHASH on x86-64: running the other parts of the code

Untrusted: everything here is checked by Lean. What each straight-line
part of `Impl.Gcm.X86_64.ghash` other than `product` does, one symbolic
execution each.
-/

namespace VG.Proof.Gcm.X86_64

open VG VG.X86_64 VG.Impl.Gcm.X86_64 VG.Proof.Gcm.X86_64.Ctmul

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- `s'` differs from `s` at most in the registers `clob`, the flags and memory. -/
def Regs (clob : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.regs {c : List Reg} {s s' : State} (h : Keeps c s s') : Regs c s s' := ⟨h.1, h.2.2⟩

theorem Regs.trans {c : List Reg} {s₁ s₂ s₃ : State} (h₁ : Regs c s₁ s₂) (h₂ : Regs c s₂ s₃) :
    Regs c s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem Regs.mono {c c' : List Reg} {s s' : State} (h : Regs c s s') (hc : ∀ r ∈ c, r ∈ c') :
    Regs c' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hc r h'), h.2⟩

/-- The registers `load` changes. -/
abbrev loadClob : List Reg := [W0, .rax, AL]

set_option simprocs false in
theorem load_ok (s : State)
    (hy0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (hy8 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (hx0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (hx8 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (wy8 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (wm : InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((240 : Nat) : Int)) 8) :
    WP isa (.block load) s fun s' =>
      s'.gpr W0 = bswap64 (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ^^^
        bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ∧
      s'.mem = (s.mem.writeW (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int))
          (bswap64 (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) ^^^
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64))).writeW
        (s.gpr .r8 + BitVec.ofInt 64 ((240 : Nat) : Int))
          ((bswap64 (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64) ^^^
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64)) ^^^
          (bswap64 (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ^^^
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64))) ∧
      Regs loadClob s s' := by
  apply WP.of_runBlock
  simp only [load, W0, AL, slotM]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.load64, State.store64, State.setReg, arithFlags, State.setFlags,
    hy0, hy8, hx0, hx8, wy8, wm, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, by trivial, by trivial⟩
  simp only [loadClob, W0, AL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, r2, r3⟩ := hr
  simp only [r1, r2, r3, ite_false]

set_option simprocs false in
theorem keepA_ok (s : State) (wy0 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8) :
    WP isa (.block keepA) s fun s' =>
      s'.gpr W0 = s.gpr PH ∧
      s'.mem = s.mem.writeW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) (s.gpr PL) ∧
      Regs [W0] s s' := by
  apply WP.of_runBlock
  simp only [keepA, W0, PH, PL]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, ea_at, State.store64, State.setReg, wy0, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

set_option simprocs false in
theorem keepB_ok (s : State)
    (hy0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (wy0 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (wy8 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (ww : InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((248 : Nat) : Int)) 8) :
    WP isa (.block keepB) s fun s' =>
      s'.mem = ((s.mem.writeW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int))
          ((s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 ^^^ s.gpr PH) ^^^ s.gpr W0)).writeW
          (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int))
          ((s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 ^^^ s.gpr PH) ^^^ s.gpr PL)).writeW
        (s.gpr .r8 + BitVec.ofInt 64 ((248 : Nat) : Int)) (s.gpr PL) ∧
      Regs [.rax, AL] s s' := by
  apply WP.of_runBlock
  simp only [keepB, W0, AL, PH, PL, slotW]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.load64, State.store64, State.setReg, arithFlags, State.setFlags,
    hy0, wy0, wy8, ww, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, fun r hr => ?_, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

set_option simprocs false in
theorem keepM_ok (s : State)
    (hy0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (hy8 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8)
    (hw : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofInt 64 ((248 : Nat) : Int)) 8) :
    WP isa (.block keepM) s fun s' =>
      s'.gpr AL = s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64 ^^^ s.gpr PH ∧
      s'.gpr AH = s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64 ^^^ s.gpr PL ∧
      s'.gpr PL = s.mem.readW (s.gpr .r8 + BitVec.ofInt 64 ((248 : Nat) : Int)) 64 ∧
      Keeps [AL, AH, PL] s s' := by
  apply WP.of_runBlock
  simp only [keepM, AL, AH, PH, PL, slotW]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.load64, State.setReg, arithFlags, State.setFlags,
    hy0, hy8, hw, ite_true, ite_false, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, by trivial, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, r2, r3⟩ := hr
  simp only [r1, r2, r3, ite_false]

theorem rot_mask (w : BitVec 64) {s : Nat} (hs : 0 < s) (hs' : s < 64) (c : BitVec 32)
    (hc : c.signExtend 64 = BitVec.ofNat 64 (2 ^ s - 1)) :
    (w &&& c.signExtend 64).rotateRight s = w <<< (64 - s) := by
  rw [hc]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, Nat.mod_eq_of_lt hs']
  have hm : ∀ j, (BitVec.ofNat 64 (2 ^ s - 1)).getLsbD j = decide (j < s) := by
    intro j
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases hj : j < s
    · simp [hj, show j < 64 by omega]
    · simp [hj]
  by_cases h : i < 64 - s
  · rw [ite_eq_left h, BitVec.getLsbD_and, hm, decide_eq_false (by omega), Bool.and_false]
    simp [h, hi]
  · rw [ite_eq_right h, BitVec.getLsbD_and, hm, decide_eq_true (show i - (64 - s) < s by omega)]
    simp [h, hi]

set_option simprocs false in
theorem fold_ok (w lo hi : Reg) (h1 : w ≠ .rax) (h2 : lo ≠ .rax) (h3 : hi ≠ .rax) (h4 : w ≠ lo)
    (h5 : w ≠ hi) (h6 : lo ≠ hi) (s : State) :
    WP isa (.block (fold w lo hi)) s fun s' =>
      s'.gpr lo = foldLo (s.gpr lo) (s.gpr w) ∧ s'.gpr hi = foldHi (s.gpr hi) (s.gpr w) ∧
      Keeps [.rax, lo, hi] s s' := by
  apply WP.of_runBlock
  have n1 : w = .rax ↔ False := iff_false_intro h1
  have n2 : lo = .rax ↔ False := iff_false_intro h2
  have n3 : hi = .rax ↔ False := iff_false_intro h3
  have n4 : w = lo ↔ False := iff_false_intro h4
  have n5 : w = hi ↔ False := iff_false_intro h5
  have n6 : lo = hi ↔ False := iff_false_intro h6
  have n7 : hi = lo ↔ False := iff_false_intro (Ne.symm h6)
  simp (config := {decide := true}) only [fold, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, isa, State.setReg, arithFlags, State.setFlags, n1, n2, n3, n4, n5,
    n6, n7, ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [rot_mask _ (s := 1) (by omega) (by omega) _ (by decide),
      rot_mask _ (s := 2) (by omega) (by omega) _ (by decide),
      rot_mask _ (s := 7) (by omega) (by omega) _ (by decide)]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3⟩ := hr
    simp only [r1, r2, r3, ite_false]

set_option simprocs false in
theorem store_ok (s : State)
    (wy0 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (wy8 : InRegions s.wr (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8) :
    WP isa (.block store) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .rsi + BitVec.ofInt 64 ((0 : Nat) : Int)) (bswap64 (s.gpr W0))).writeW
        (s.gpr .rsi + BitVec.ofInt 64 ((8 : Nat) : Int)) (bswap64 (s.gpr AL)) ∧
      s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧
      Regs [W0, AL, .rdi, .rcx] s s' := by
  apply WP.of_runBlock
  simp only [store, W0, AL]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.store64, State.setReg, arithFlags, State.setFlags, wy0, wy8,
    ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  refine ⟨by trivial, by rw [e16], by rw [e1], by rw [e1], fun r hr => ?_, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨r1, r2, r3, r4⟩ := hr
  simp only [r1, r2, r3, r4, ite_false]


/-! ## The set-up -/

theorem mask_xInv (a b : BitVec 64) (c : Bool) :
    (a ^^^ (xInvHigh &&& if c then BitVec.allOnes 64 else 0#64)) ++
      (b ^^^ ((if c then BitVec.allOnes 64 else 0#64) &&& BitVec.signExtend 64 (1 : BitVec 32))) =
      (a ++ b) ^^^ (if c then xInv else 0) := by
  cases c
  · simp only [Bool.false_eq_true, ite_false, BitVec.and_zero, BitVec.zero_and, BitVec.xor_zero]
    exact (BitVec.xor_zero (x := a ++ b)).symm
  · simp only [ite_true, BitVec.and_allOnes, BitVec.allOnes_and, xInv, ← BitVec.xor_append]
    rfl

set_option simprocs false in
theorem hInv_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 8) :
    WP isa (.block hInv) s fun s' =>
      s'.gpr AL ++ s'.gpr AH =
        ((bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ++
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64)) <<< 1) ^^^
          (if (bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 64) ++
            bswap64 (s.mem.readW (s.gpr .rdi + BitVec.ofInt 64 ((8 : Nat) : Int)) 64)).getMsbD 0
          then xInv else 0) ∧
      s'.gpr PH = s'.gpr AL ^^^ s'.gpr AH ∧ Keeps [AL, AH, .rax, PL, PH] s s' := by
  apply WP.of_runBlock
  simp only [hInv, AL, AH, PL, PH]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, ea_at, State.load64, State.setReg, arithFlags, State.setFlags, h0, h8,
    ite_true, ite_false, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by trivial, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · rw [sbb_self, shl1_cf, mask_xInv, shl1, BitVec.msb_eq_getMsbD_zero]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨r1, r2, r3, r4, r5⟩ := hr
    simp only [r1, r2, r3, r4, r5, ite_false]

theorem tblReg_ne (q : Nat) : tblReg q ≠ .rax := by unfold tblReg; split <;> decide

set_option simprocs false in
theorem entry_ok (u : Nat) (s : State)
    (hw : InRegions s.wr (s.gpr .r8 + BitVec.ofInt 64 ((off u : Nat) : Int)) 8) :
    WP isa (.block (entry u)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r8 + BitVec.ofInt 64 ((off u : Nat) : Int))
        (s.gpr (tblReg (u / 8)) &&& half (u % 8 / 2) (u % 2)) ∧ Regs [.rax] s s' := by
  have hn : tblReg (u / 8) = .rax ↔ False := iff_false_intro (tblReg_ne _)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [entry, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, readSrc, isa, ea_at, State.store64, State.setReg, arithFlags, State.setFlags, hw, hn,
    ite_true, ite_false, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [BitVec.and_comm], fun r hr => ?_, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

set_option simprocs false in
theorem tail_ok (s : State) :
    WP isa (.block [.mov .rdi (.reg .rdx), .alu .test .rcx (.reg .rcx)]) s fun s' =>
      s'.gpr .rdi = s.gpr .rdx ∧ s'.zf = some (s.gpr .rcx &&& s.gpr .rcx == 0) ∧
      Keeps [.rdi] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [hr, ite_false]

end VG.Proof.Gcm.X86_64
