import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarWord
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Bytes

/-!
# Scalar reduction: the eight-word loop

The invariant is the value modulo L of the already consumed top words of the
little-endian input. The body writes no memory.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

/-- The input from word `k` up: that word, and `2^64` times the words above it. -/
theorem words_step (m : Mem) (p : Addr) (k : Nat) (hk : k < 8) :
    decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat +
        2 ^ 64 * decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * (k + 1))) (64 - 8 * (k + 1))) := by
  have e : 64 - 8 * k = 8 + (64 - 8 * (k + 1)) := by omega
  have hs : bytesAt m (p + BitVec.ofNat 64 (8 * k)) (8 + (64 - 8 * (k + 1))) =
      bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8 ++
        bytesAt m (p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8) (64 - 8 * (k + 1)) :=
    Proof.X25519.bytesAt_add m _ 8 _
  have hw : decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat := by
    rw [decodeLE_eq]; exact Proof.X25519.leNum_bytesAt_64 m _
  have ha : p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  rw [e, hs, decodeLE_append, bytesAt_length, hw, ha]
  rfl

def wordRead : List Instr :=
  [.alu .sub .rbx (.imm 8), .mov .rax (.mem { base := .rsi, index := some .rbx })]

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .rbx = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block wordRead) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .rax = s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64 ∧
      Keeps [.rbx, .rax] s t := by
  have hn : s.gpr .rbx - (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl,
      show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.ea, State.load64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hn, ite_true, ite_false, reduceCtorEq,
    BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl,
    BitVec.add_zero, hr, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h.1, h.2, ite_false], rfl, rfl, rfl⟩

theorem scalar_test_zero : ∀ n < 64,
    (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem scalarTest_ok (s : State) (n : Nat) (hn : n < 64)
    (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf = some (decide (n = 0)) ∧ scalarValue t = scalarValue s ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb,
    scalar_test_zero n hn]
  exact ⟨trivial, rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The registers the loop changes. -/
def scalarBodyClob : List Reg := .rbx :: foldClob

theorem scalarWord_ok (s : State) (k : Nat) (hk : k < 8)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8)
    (hv : scalarValue s < L) :
    WP isa (.block scalarWord) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (8 * k) ∧ t.zf = some (decide (k = 0)) ∧
      scalarValue t = (scalarValue s * 2 ^ 64 +
        (s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64).toNat) % L ∧
      Keeps scalarBodyClob s t := by
  rw [show scalarWord = wordRead ++ (wordFold ++ (scalarSubtract ++ (scalarSelect ++
      ([.alu .test .rbx (.reg .rbx)] : List Instr)))) by
    simp only [scalarWord, wordRead, List.append_assoc, List.cons_append, List.nil_append],
    WP.block_append_iff]
  refine WP.mono (wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : scalarValue a = scalarValue s := by
    simp only [scalarValue, ka.1 .r8 (by decide), ka.1 .r9 (by decide),
      ka.1 .r10 (by decide), ka.1 .r11 (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (wordFold_ok a (av ▸ hv)) fun b ⟨b2, bm, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSubtract_ok b) fun c ⟨cc, cu, csaved, kc⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSelect_ok c _ cc) fun d ⟨dv, kd⟩ => ?_
  have hb' : d.gpr .rbx = BitVec.ofNat 64 (8 * k) := by
    rw [kd.1 .rbx (by decide), kc.1 .rbx (by decide), kb.1 .rbx (by decide)]; exact ab
  refine WP.mono (scalarTest_ok d (8 * k) (by omega) hb') fun t ⟨tz, tv, kt⟩ => ?_
  have he := select_remainder (scalarValue b) (scalarValue c) b2 cu
  have k1 : Keeps scalarBodyClob s a := ka.mono (by simp [scalarBodyClob, foldClob])
  have k2 : Keeps scalarBodyClob a b := kb.mono (by simp [scalarBodyClob, foldClob])
  have k3 : Keeps scalarBodyClob b c := kc.mono (by simp [scalarBodyClob, foldClob])
  have k4 : Keeps scalarBodyClob c d := kd.mono (by simp [scalarBodyClob, foldClob])
  have k5 : Keeps scalarBodyClob d t := kt.mono (by simp)
  refine ⟨(kt.1 .rbx (by decide)).trans hb', by rw [tz]; simp, ?_,
    k1.trans (k2.trans (k3.trans (k4.trans k5)))⟩
  simp only [decide_eq_true_eq] at dv
  rw [tv, dv, csaved, he, bm, av, ax]

theorem mod_step (a w : Nat) : (a % L * 2 ^ 64 + w) % L = (w + 2 ^ 64 * a) % L := by
  have hd := Nat.mod_add_div a L
  generalize a % L = r at hd ⊢
  generalize a / L = q at hd
  subst hd
  rw [← Nat.add_mul_mod_self_left (r * 2 ^ 64 + w) L (q * 2 ^ 64)]
  congr 1
  rw [Nat.mul_add, Nat.add_comm w, Nat.add_assoc, Nat.add_comm w, ← Nat.add_assoc, Nat.mul_comm (2 ^ 64) r,
    Nat.mul_left_comm (2 ^ 64) L q, Nat.mul_comm (2 ^ 64) q, ← Nat.mul_assoc]

structure ScalarInv (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 8
  counter : s.gpr .rbx = BitVec.ofNat 64 (8 * n)
  value : scalarValue s =
    decodeLE (bytesAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (8 * n)) (64 - 8 * n)) % L
  keeps : Keeps scalarBodyClob s₀ s

theorem scalarLoop_ok (s₀ : State) (hb : s₀.gpr .rbx = 64) (hz : scalarValue s₀ = 0)
    (hr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.loop (.block scalarWord) .ne) s₀ fun t =>
      scalarValue t = decodeLE (bytesAt s₀.mem (s₀.gpr .rsi) 64) % L ∧
      Keeps scalarBodyClob s₀ t := by
  apply WP.loop (ScalarInv s₀) (n := 8)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 8 := by have := hi.bound; omega
    have hp : s.gpr .rsi = s₀.gpr .rsi := hi.keeps.1 .rsi (by decide)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.keeps.2.2.1, hi.keeps.2.2.2, hp]; exact hr k hk
    have hv : scalarValue s < L := by rw [hi.value]; exact Nat.mod_lt _ order_pos
    refine WP.mono (scalarWord_ok s k hk hi.counter hread hv) fun t ⟨htb, htz, htv, htk⟩ => ?_
    have kt := hi.keeps.trans htk
    have vt : scalarValue t =
        decodeLE (bytesAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) % L := by
      rw [htv, hi.value, hp, hi.keeps.2.1, words_step _ _ k hk, Nat.succ_eq_add_one, mod_step]
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, htz, decide_true, Option.map_some, Bool.not_true], ?_, kt⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, htz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, htb, vt, kt⟩⟩
  · refine ⟨by decide, by decide, hb, ?_, fun _ _ => rfl, rfl, rfl, rfl⟩
    rw [hz]
    rfl

end VG.Proof.Ed25519.X86_64
