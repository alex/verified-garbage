import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy

/-! # Zeroing the Argon2 matrix, independently of its initial contents -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

def clearMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | n + 1 => (clearMem m p n).writeW (p + BitVec.ofNat 64 (8 * n)) (0 : BitVec 64)

theorem clearMem_frame (m : Mem) (p : Addr) (n : Nat) (bound : 8 * n < 2 ^ 64) :
    Frame [⟨p, 8 * n⟩] m (clearMem m p n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    have smaller : Frame [⟨p, 8 * (n + 1)⟩] m (clearMem m p n) :=
      (ih (by omega)).sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
    exact smaller.writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains_base _ (by omega) (by omega))

theorem clearMem_word (m : Mem) (p : Addr) (n j : Nat)
    (bound : 8 * n < 2 ^ 64) (hj : j < n) :
    (clearMem m p n).readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [clearMem]
    by_cases eq : j = n
    · subst j; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact ih (by omega) (by omega)
      · exact Offset.sep p (by omega) (by omega) (by omega)

theorem clearWord_ok (s : State) (hw : InRegions s.wr (s.gpr .r14) 8) :
    WP isa (.block clearWord) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r14) (s.gpr .rcx) ∧
      t.gpr .r14 = s.gpr .r14 + 8 ∧ t.gpr .rax = s.gpr .rax - 1 ∧
      t.zf = some (s.gpr .rax - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [clearWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.store64, execAlu, HPrime.ea_at, BitVec.add_zero,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    show (BitVec.signExtend 64 (8 : BitVec 32)) = 8 from rfl,
    show (BitVec.signExtend 64 (1 : BitVec 32)) = 1 from rfl,
    hw, reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial,
    fun r h1 h2 => by simp only [h1, h2, ite_false], trivial, trivial⟩

structure ClearI (s₀ : State) (p : Addr) (n j : Nat) (s : State) : Prop where
  bound : j ≤ n
  destination : s.gpr .r14 = p + BitVec.ofNat 64 (8 * j)
  count : s.gpr .rax = BitVec.ofNat 64 (n - j)
  zero : s.gpr .rcx = 0
  other : ∀ r, r ≠ .rax → r ≠ .r14 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = clearMem s₀.mem p j

theorem clearLoop_ok (s₀ : State) (p : Addr) (n : Nat) (lo : 1 ≤ n)
    (bound : 8 * n < 2 ^ 64) (dst : s₀.gpr .r14 = p)
    (count : s₀.gpr .rax = BitVec.ofNat 64 n) (zero : s₀.gpr .rcx = 0)
    (write : ∀ j < n, InRegions s₀.wr (p + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (.loop (.block clearWord) .ne) s₀ (ClearI s₀ p n n) := by
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ ClearI s₀ p n j s)
    ?_ n s₀ ⟨0, by omega, lo, by omega, by simpa using dst, by simpa only [Nat.sub_zero] using count,
      zero, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k s ⟨j, rfl, hj, h⟩
  have hw : InRegions s.wr (s.gpr .r14) 8 := by
    rw [h.wr, h.destination]; exact write j hj
  refine (clearWord_ok s hw).mono ?_
  rintro t ⟨memT, dstT, countT, zfT, otherT, rdT, wrT⟩
  have nextCount : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : ClearI s₀ p n (j + 1) t := by
    refine ⟨by omega, ?_, ?_, (otherT _ (by decide) (by decide)).trans h.zero,
      fun r h1 h2 => (otherT r h1 h2).trans (h.other r h1 h2),
      rdT.trans h.rd, wrT.trans h.wr, ?_⟩
    · rw [dstT, h.destination, BitVec.add_assoc, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 2
    · rw [countT, h.count, nextCount]
    · rw [memT, h.mem, h.destination, h.zero]; rfl
  have zf : t.zf = some (decide (n - (j + 1) = 0)) := by
    rw [zfT, h.count, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  by_cases done : j + 1 = n
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, zf, show n - (j + 1) = 0 by omega, decide_true,
      Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, n - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    simp only [eval, zf, show n - (j + 1) ≠ 0 by omega, decide_false,
      Option.map_some, Bool.not_false]

end VG.Proof.Argon2.X86_64.MemoryInit
