import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClearMemory
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions

/-! # Zeroing the Argon2 matrix, independently of its initial contents -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

theorem decrement_ok (s : State) :
    WP isa (.block (Impl.Argon2.AArch64.Instructions.subi .x8 1)) s fun t =>
      t.gpr .x8 = s.gpr .x8 - 1 ∧ t.gpr .x15 = s.gpr .x8 - 1 ∧
      Divide.Keeps [.x8, .x12, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.subi,
    Impl.Argon2.AArch64.Instructions.sub, Impl.Argon2.AArch64.Instructions.imm,
    Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    show 1 < 65536 from by decide, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, show (1#16).setWidth 64 = 1#64 from rfl,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, sub_value, Bool.toNat_true,
    BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem clearWord_ok (s : State) (hw : InRegions s.wr (s.gpr .x22) 8) :
    WP isa (.block clearWord) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x22) (s.gpr .x3) ∧
      t.gpr .x22 = s.gpr .x22 + 8 ∧ t.gpr .x8 = s.gpr .x8 - 1 ∧
      t.gpr .x15 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x8 → r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [clearWord, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [WP.block_append_iff]
  have hw' : InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 0) 8 := by
    simpa only [BitVec.add_zero] using hw
  refine (Instructions.store_ok s .x22 .x3 0 (by decide) (by decide) hw').mono ?_
  rintro a ⟨memA, regsA, rdA, wrA, spA⟩
  rw [WP.block_append_iff]
  refine (Instructions.addi_ok a .x22 8 (by decide) (by decide) (by decide)).mono ?_
  rintro b ⟨dst, kb⟩
  refine (decrement_ok b).mono ?_
  rintro t ⟨count, flag, kt⟩
  have countB : b.gpr .x8 = s.gpr .x8 := (kb.regs _ (by decide)).trans (congrFun regsA _)
  refine ⟨?_, ?_, count.trans (congrArg (· - 1) countB),
    flag.trans (congrArg (· - 1) countB), ?_, kt.rd.trans (kb.rd.trans rdA),
    kt.wr.trans (kb.wr.trans wrA), kt.sp.trans (kb.sp.trans spA)⟩
  · rw [kt.mem, kb.mem, memA]
    rw [BitVec.add_zero]
  · rw [kt.regs .x22 (by decide), dst, regsA]
    rfl
  · intro r h1 h2 h3 h4
    exact (kt.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h3,h4⟩)).trans
      ((kb.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h2,h3,h4⟩)).trans
        (congrFun regsA r))

structure ClearI (s₀ : State) (p : Addr) (n j : Nat) (s : State) : Prop where
  bound : j ≤ n
  destination : s.gpr .x22 = p + BitVec.ofNat 64 (8 * j)
  count : s.gpr .x8 = BitVec.ofNat 64 (n - j)
  zero : s.gpr .x3 = 0
  other : ∀ r, r ≠ .x8 → r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = clearMem s₀.mem p j

theorem clearLoop_ok (s₀ : State) (p : Addr) (n : Nat) (lo : 1 ≤ n)
    (bound : 8 * n < 2 ^ 64) (dst : s₀.gpr .x22 = p)
    (count : s₀.gpr .x8 = BitVec.ofNat 64 n) (zero : s₀.gpr .x3 = 0)
    (write : ∀ j < n, InRegions s₀.wr (p + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (.loop (.block clearWord) (.nonzero .x .x15)) s₀ (ClearI s₀ p n n) := by
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ ClearI s₀ p n j s)
    ?_ n s₀ ⟨0, by omega, lo, by omega, by simpa using dst, by simpa only [Nat.sub_zero] using count,
      zero, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rintro k s ⟨j, rfl, hj, h⟩
  have hw : InRegions s.wr (s.gpr .x22) 8 := by
    rw [h.wr, h.destination]; exact write j hj
  refine (clearWord_ok s hw).mono ?_
  rintro t ⟨memT, dstT, countT, zfT, otherT, rdT, wrT, spT⟩
  have nextCount : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : ClearI s₀ p n (j + 1) t := by
    refine ⟨by omega, ?_, ?_, (otherT _ (by decide) (by decide) (by decide) (by decide)).trans h.zero,
      fun r h1 h2 h3 h4 => (otherT r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4),
      rdT.trans h.rd, wrT.trans h.wr, spT.trans h.sp, ?_⟩
    · rw [dstT, h.destination, BitVec.add_assoc, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 2
    · rw [countT, h.count, nextCount]
    · rw [memT, h.mem, h.destination, h.zero]; rfl
  have eqzero : BitVec.ofNat 64 (n - (j + 1)) = 0 ↔ n - (j + 1) = 0 := by
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  have flag : eval (.nonzero .x .x15) t = some (decide (n - (j + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, zfT, h.count, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
    exact not_congr eqzero
  by_cases done : j + 1 = n
  · refine .inl ⟨?_, done ▸ next⟩
    simpa only [show n - (j + 1) = 0 by omega, ne_eq, not_true_eq_false, decide_false] using flag
  · refine .inr ⟨?_, n - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    change eval (.nonzero .x .x15) t = some true
    rw [flag]
    exact congrArg some (decide_eq_true (by omega : n - (j + 1) ≠ 0))

end VG.Proof.Argon2.AArch64.MemoryInit
