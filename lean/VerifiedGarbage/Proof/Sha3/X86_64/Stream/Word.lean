import VerifiedGarbage.Proof.Sha3.X86_64.Permute
import VerifiedGarbage.Impl.Sha3.X86_64.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge on x86-64: the test for a lane at a time

`wordTest` sets ZF only if the position is at a lane and at least 8 bytes are
left (`wordTest_ok`), so that `absorb` and `squeeze` can then move a lane at
once.
-/

namespace VG.Proof.Sha3.X86_64

open VG VG.X86_64
open VG.Impl.Sha3.X86_64.Stream (wordTest)
open VG.Spec.Sha3 (rates stateAt bytesAt)
open VG.Proof.Sha3 (xorAt byteOf_xorAt byteOf_stateAt writeW64_byte bytesAt_succ)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_or {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_shr {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  have e : exec (.shift .shr d n) s = some ((s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
      (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
      (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) := by
    simp only [exec, execShift, h₁, h₂, and_self, ite_true]
  exact WP.cons e (k _ (Upd.withFlags _ _ _ _ _ _ _))

end

theorem sx8 : BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 := by decide

/-- Every rate is a whole number of lanes. -/
theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `wordTest`, from `r12` = `pos` and `r14` = `n`: it changes only `r10`,
`r11` and the flags, and sets ZF only if `pos` is a multiple of 8 and
`n ≥ 8`. -/
theorem wordTest_ok {s : State} {pos n : Nat} (h12 : s.gpr .r12 = BitVec.ofNat 64 pos)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    WP isa (.block wordTest) s fun s' => (∀ r, r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∃ b, s'.zf = some b ∧ (b = true → pos % 8 = 0 ∧ 8 ≤ n) := by
  unfold wordTest
  refine wp_mov fun s₁ u₁ => wp_mov32i fun s₂ u₂ => wp_and fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_subi fun s₅ u₅ _ => wp_shr (by decide) (by decide) fun s₆ u₆ => wp_or fun s₇ u₇ =>
      wp_test fun s₈ g₈ m₈ rd₈ wr₈ z₈ => wp_nil ?_
  refine ⟨fun r h1 h2 => by
      rw [g₈, u₇.other r h1, u₆.other r h2, u₅.other r h2, u₄.other r h2, u₃.other r h1, u₂.other r h2,
        u₁.other r h1],
    by rw [m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], _, z₈, fun hb => ?_⟩
  have h0 : s₇.gpr .r10 = 0 := by simpa using hb
  rw [u₇.gpr, u₆.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
    u₂.other _ (by decide), u₂.gpr, u₁.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide), h12, h14, sx8] at h0
  have h0' := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
    BitVec.toNat_ofNat, BitVec.toNat_setWidth] at h0'
  simp only [show BitVec.toNat (7 : BitVec 32) = 2 ^ 3 - 1 from rfl,
    show (2 ^ 3 - 1) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, show BitVec.toNat (0 : BitVec 64) = 0 from rfl,
    Nat.or_eq_zero_iff] at h0'
  omega

/-- The bytes `c … c + n - 1` follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m p c n, bytesAt_succ, List.append_assoc,
      BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A lane of a state in memory written: its 8 bytes XORed with `bs`. -/
theorem stateAt_write_lane {m : Mem} {p : Addr} {j : Nat} (hj : j + 8 ≤ 200) {v : BitVec 64}
    {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (p + BitVec.ofNat 64 (j + d)) ^^^ bs.getD d 0) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) v) p = xorAt (stateAt m p) j bs :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi, hbs]
    by_cases c : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left c, show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1],
        writeW64_byte _ _ _ (by omega), hv _ (by omega), Nat.add_sub_cancel' c.1,
        show p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) = p + BitVec.ofNat 64 i by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1]]
    · rw [ite_eq_right c, Mem.writeW, Mem.write_apply]
      rw [Offset.sub_toNat' _ (by omega) (by omega)]
      split <;> omega

end VG.Proof.Sha3.X86_64
