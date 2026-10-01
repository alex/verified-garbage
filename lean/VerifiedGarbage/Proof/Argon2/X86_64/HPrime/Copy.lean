import VerifiedGarbage.Impl.Argon2.X86_64.HPrime
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.HPrime

/-! # H′: copying digest bytes -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem ea_at (s : State) (r : Reg) (d : Nat) :
    s.ea (at_ r d) = s.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, BitVec.ofInt_natCast]

theorem copyByte_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 1)
    (hw : InRegions s.wr (s.gpr .r14) 1) :
    WP isa (.block copyByte) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r14) (s.mem (s.gpr .rdx)) ∧
      t.gpr .rdx = s.gpr .rdx + 1 ∧ t.gpr .r14 = s.gpr .r14 + 1 ∧
      t.gpr .rax = s.gpr .rax - 1 ∧ t.zf = some (s.gpr .rax - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r14 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [copyByte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load8, State.store8, execAlu, ea_at, BitVec.add_zero,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    show (BitVec.signExtend 64 (1 : BitVec 32)) = 1 from rfl,
    hr, hw, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  exact ⟨trivial, trivial, trivial, trivial, trivial,
    fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], trivial, trivial⟩

open VG.WriteBytes
open VG.Spec.Blake2 (bytesAt)

/-- The prefix already copied, with every other register preserved. -/
structure CopyI (s₀ : State) (src dst : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ k
  source : s.gpr .rdx = src + BitVec.ofNat 64 j
  destination : s.gpr .r14 = dst + BitVec.ofNat 64 j
  count : s.gpr .rax = BitVec.ofNat 64 (k - j)
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r14 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem copyLoop_ok (s₀ : State) (src dst : Addr) (k : Nat)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 64)
    (hs : s₀.gpr .rdx = src) (hd : s₀.gpr .r14 = dst)
    (hn : s₀.gpr .rax = BitVec.ofNat 64 k)
    (hr : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < k, InRegions s₀.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : Region.Disjoint ⟨src, k⟩ ⟨dst, k⟩) :
    WP isa (.loop (.block copyByte) .ne) s₀ (CopyI s₀ src dst k k) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = k - j ∧ j < k ∧ CopyI s₀ src dst k j s)
    ?_ k s₀ ⟨0, by omega, hk, by omega, by simpa using hs, by simpa using hd,
      by simpa using hn, fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hlen : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  have htake : ((bytesAt s₀.mem src k).take j).length = j := by
    rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
  have hb : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    apply (writeBytes_frame s₀.mem dst _ (R := ⟨dst, k⟩)
      (by simpa only [BitVec.add_zero, htake] using
        (Offset.contains_base dst (k := k) (d := 0) (n := j) (by omega) (by decide)))).bytes
        (R := ⟨src, k⟩) _ (show k ≤ 2 ^ 64 by omega) hj
    simpa using hsep
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 1 := by
    rw [h.rd, h.wr, h.source]; exact hr j hj
  have hw' : InRegions s.wr (s.gpr .r14) 1 := by
    rw [h.wr, h.destination]; exact hw j hj
  refine (copyByte_ok s hr' hw').mono ?_
  rintro t ⟨hm, hs', hd', hn', hz, ho, hrd, hwr⟩
  have hc : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 1 ≤ k - j)]
    congr 1
  have hi : CopyI s₀ src dst k (j + 1) t := by
    refine ⟨by omega, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, hrd.trans h.rd, hwr.trans h.wr, ?_⟩
    · rw [hs', h.source, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hd', h.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hn', h.count, hc]
    · exact (ho r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4)
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega
      rw [hm, h.source, h.destination, hb, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [htake]; omega), htake]
      refine congrArg (fun b => (writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)).writeW
        (dst + BitVec.ofNat 64 j) b) ?_
      simp only [bytesAt, List.getElem_map, List.getElem_range]
  have hz' : t.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz, h.count, hc]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k - (j + 1) < 2 ^ 64), show (0 : BitVec 64).toNat = 0 from rfl] using ht
    · intro he; rw [he]; rfl
  by_cases he : j + 1 = k
  · refine .inl ⟨?_, he ▸ hi⟩
    simp only [eval, hz', show k - (j + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hi⟩
    simp only [eval, hz', show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]

end VG.Proof.Argon2.X86_64.HPrime
