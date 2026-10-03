import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarWord
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-! Merged from `Proof.Ed25519.AArch64.ScalarLoop`. -/
section
/-!
# Scalar reduction: the eight-word loop

The invariant is the value modulo L of the already consumed top words of the
little-endian input. The body writes no memory.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Spec.Ed25519 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

def wordRead : List Instr :=
  [.subImm .x .x19 .x19 8, .add .x .x9 .x1 .x19, .ldr .x .x3 .x9 0]

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .x19 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block wordRead) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .x3 = s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64 ∧
      Keeps [.x19, .x9, .x3] s t := by
  have hn : s.gpr .x19 - BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    Size.bytes, show (8 : Nat) < 4096 from by decide, show (0 : Nat) % 8 = 0 from rfl,
    show (0 : Nat) < 4096 * 8 from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hn, BitVec.add_zero, BitVec.setWidth_eq, hr,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, ⟨fun r h => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2.1, h.2.2, ite_false]

/-- The registers the loop changes. -/
def scalarBodyClob : List Reg :=
  [.x19, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17,
    .x21, .x22, .x23, .x24]

theorem scalarWord_ok (s : State) (k : Nat)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8)
    (hv : scalarValue s < L) (hz : s.gpr .x10 = 0) :
    WP isa (.block scalarWord) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (8 * k) ∧
      scalarValue t = (scalarValue s * 2 ^ 64 +
        (s.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 64).toNat) % L ∧
      Keeps scalarBodyClob s t := by
  rw [show scalarWord = wordRead ++ (wordFold ++ (scalarSubtract ++ scalarSelect)) by
    simp only [scalarWord, wordRead, List.append_assoc, List.cons_append, List.nil_append],
    WP.block_append_iff]
  refine WP.mono (wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : scalarValue a = scalarValue s := by
    simp only [scalarValue, ka.gpr .x4 (by decide), ka.gpr .x5 (by decide),
      ka.gpr .x6 (by decide), ka.gpr .x7 (by decide)]
  have az : a.gpr .x10 = 0 := (ka.gpr .x10 (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (wordFold_ok a (av ▸ hv) az) fun b ⟨b2, bm, kb⟩ => ?_
  have bz : b.gpr .x10 = 0 := (kb.gpr .x10 (by decide)).trans az
  rw [WP.block_append_iff]
  refine WP.mono (scalarSubtract_ok b bz) fun c ⟨cc, cu, csaved, kc⟩ => ?_
  have cz : c.gpr .x10 = 0 := (kc.gpr .x10 (by decide)).trans bz
  refine WP.mono (scalarSelect_ok c cz) fun t ⟨tv, kt⟩ => ?_
  have he := select_remainder (scalarValue b) (scalarValue c) b2 cu
  refine ⟨?_, ?_, (((ka.mono (by decide)).trans (kb.mono (by decide))).trans
    (kc.mono (by decide))).trans (kt.mono (by decide))⟩
  · rw [kt.gpr .x19 (by decide), kc.gpr .x19 (by decide), kb.gpr .x19 (by decide)]
    exact ab
  · rw [cc, csaved] at tv
    have hs : scalarValue t = if L ≤ scalarValue b then scalarValue c else scalarValue b := by
      by_cases h : L ≤ scalarValue b <;> simpa only [h, decide_true, decide_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] using tv
    rw [hs, he, bm, av, ax]

theorem scalar_counter_test : ∀ n < 8,
    (BitVec.ofNat 64 (8 * n) != 0) = decide (n ≠ 0) := by decide

structure ScalarInv (s₀ : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 8
  counter : s.gpr .x19 = BitVec.ofNat 64 (8 * n)
  value : scalarValue s =
    decodeLE (bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * n)) (64 - 8 * n)) % L
  keeps : Keeps scalarBodyClob s₀ s

theorem scalarLoop_ok (s₀ : State) (hb : s₀.gpr .x19 = 64) (hz : scalarValue s₀ = 0)
    (hr : ∀ k < 8, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8)
    (hz0 : s₀.gpr .x10 = 0) :
    WP isa (.loop (.block scalarWord) (.nonzero .x .x19)) s₀ fun t =>
      scalarValue t = decodeLE (bytesAt s₀.mem (s₀.gpr .x1) 64) % L ∧
      Keeps scalarBodyClob s₀ t := by
  apply WP.loop (ScalarInv s₀) (n := 8)
  · intro n s hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
    have hk : k < 8 := by have := hi.bound; omega
    have hp : s.gpr .x1 = s₀.gpr .x1 := hi.keeps.gpr .x1 (by decide)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.keeps.rd, hi.keeps.wr, hp]; exact hr k hk
    have hv : scalarValue s < L := by rw [hi.value]; exact Nat.mod_lt _ order_pos
    have hzs := (hi.keeps.gpr .x10 (by decide)).trans hz0
    refine WP.mono (scalarWord_ok s k hi.counter hread hv hzs) fun t ⟨htb, htv, htk⟩ => ?_
    have kt := hi.keeps.trans htk
    have vt : scalarValue t =
        decodeLE (bytesAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) % L := by
      rw [htv, hi.value, hp, hi.keeps.mem, words_step _ _ k hk, Nat.succ_eq_add_one, mod_step]
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, read_x, htb, scalar_counter_test 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], ?_, kt⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, read_x, htb, scalar_counter_test k hk, decide_eq_true hk0],
        k, by omega, ⟨by omega, by omega, htb, vt, kt⟩⟩
  · refine ⟨by decide, by decide, hb, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
    rw [hz]
    rfl

end VG.Proof.Ed25519.AArch64
end

/-! Scalar reducer saves, restores, and output stores. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- The six used callee-saved registers occupy scratch bytes 0–47. -/
def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ rd ∈ saved, word m base rd.2 = g rd.1

theorem scalarSave_ok {s : State} {base : Addr} (hc : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block scalarSave) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 0 48 s.mem t.mem ∧ Saved base s.gpr t.mem := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [scalarSave, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.store, read_x, hc, BitVec.setWidth_eq,
    Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega), w 32 (by omega), w 40 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, True.intro, True.intro, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _
  · change word _ base rd.2 = s.gpr rd.1
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    simp only [write64_eq_writeW]
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [word_writeW_sep, word_writeW_self]

theorem scalarRestore_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block scalarRestore) s fun t =>
      (∀ rd ∈ saved, t.gpr rd.1 = g rd.1) ∧ Keeps [.x19, .x20, .x21, .x22, .x23, .x24] s t := by
  have hr : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [scalarRestore, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, hb, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self,
    hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega), hr 32 (by omega), hr 40 (by omega),
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun rd hrd => ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have e := hsv rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, word, Mem.readW,
        BitVec.setWidth_eq] using e
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

theorem scalarOut_ok {s : State} {q : Addr} (hq : s.gpr .x0 = q) (hw : (⟨q, 32⟩ : Region) ∈ s.wr) :
    WP isa (.block [.str .x .x4 .x0 0, .str .x .x5 .x0 8, .str .x .x6 .x0 16, .str .x .x7 .x0 24]) s
      fun t => t = { s with mem := st4 s.mem q 0 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) } := by
  have w : ∀ d, d + 8 ≤ 32 → InRegions s.wr (off q d) 8 :=
    fun d hd => ⟨_, hw, Offset.contains_base q hd (by omega)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.store, read_x,
    hq, BitVec.setWidth_eq, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true,
    w 0 (by omega), w 8 (by omega), w 16 (by omega), w 24 (by omega),
    Option.bind_some, Option.some.injEq, exists_eq_left']
  rfl

theorem scalarInit_ok (s : State) :
    WP isa (.block scalarInit) s fun t =>
      t.gpr .x19 = 64 ∧ scalarValue t = 0 ∧ t.gpr .x10 = 0 ∧
      Keeps [.x4, .x5, .x6, .x7, .x10, .x19] s t := by
  apply WP.of_runBlock
  simp only [scalarInit, zero4, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide,
    scalarValue, RegUpd.gpr_write, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
    hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
