import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarStep

/-!
# Scalar reduction: consume a byte

Untrusted. The eight bit steps have one proof by list induction. The
input byte remains in rbp while the arithmetic changes only its own limbs.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open VG.Spec.Ed25519 (L)

theorem scalarBits_ok (js : List Nat) (hj : ∀ j ∈ js, j < 8) (s : State)
    (hr : scalarValue s < L) :
    WP isa (.block (js.flatMap scalarBit)) s fun t =>
      scalarValue t = js.foldl (fun v j => (2 * v + ((s.gpr .rbp).getLsbD j).toNat) % L)
        (scalarValue s) ∧ Keeps scalarClob s t := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (scalarBit_ok s j (hj j (by simp)) hr) fun t ⟨ht, kt⟩ => ?_
    have htL : scalarValue t < L := by rw [ht]; exact Nat.mod_lt _ order_pos
    refine WP.mono (ih (fun i hi => hj i (List.mem_cons_of_mem _ hi)) t htL)
      fun u ⟨hu, ku⟩ => ?_
    refine ⟨?_, kt.trans ku⟩
    rw [hu, kt.1 .rbp (by decide), ht]
    rfl

theorem scalarEight_ok (s : State) (hr : scalarValue s < L) (hb : (s.gpr .rbp).toNat < 256) :
    WP isa (.block ((List.range 8).reverse.flatMap scalarBit)) s fun t =>
      scalarValue t = (256 * scalarValue s + (s.gpr .rbp).toNat) % L ∧
      Keeps scalarClob s t := by
  refine WP.mono (scalarBits_ok _ (by intro j hj; simpa only [List.mem_reverse, List.mem_range] using hj)
    s hr) fun t ⟨ht, kt⟩ => ?_
  change scalarValue t = consumeBits (s.gpr .rbp) 8 (scalarValue s) at ht
  rw [consumeBits_eq _ _ _ hr, show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hb] at ht
  exact ⟨ht, kt⟩

def scalarRead : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rbp { base := .rsi, index := some .rbx }]

theorem scalarRead_ok (s : State) (n : Nat) (hb : s.gpr .rbx = BitVec.ofNat 64 (n + 1))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 n) 1) :
    WP isa (.block scalarRead) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧
      t.gpr .rbp = (s.mem (s.gpr .rsi + BitVec.ofNat 64 n)).setWidth 64 ∧
      Keeps [.rbx, .rbp] s t := by
  have hn : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 n := by
    rw [hb, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [scalarRead, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.ea, State.load8, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
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

def scalarBodyClob : List Reg := .rbx :: .rbp :: scalarClob

theorem scalarByte_ok (s : State) (n : Nat) (hn : n < 64)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (n + 1))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 n) 1)
    (hv : scalarValue s < L) :
    WP isa (.block scalarByte) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧
      scalarValue t = (256 * scalarValue s + (s.mem (s.gpr .rsi + BitVec.ofNat 64 n)).toNat) % L ∧
      Keeps scalarBodyClob s t := by
  rw [show scalarByte = scalarRead ++ ((List.range 8).reverse.flatMap scalarBit ++
      ([.alu .test .rbx (.reg .rbx)] : List Instr)) by
    simp only [scalarByte, scalarRead, List.append_assoc], WP.block_append_iff]
  refine WP.mono (scalarRead_ok s n hb hr) fun t ⟨hb1, hp1, kt⟩ => ?_
  have hv1 : scalarValue t = scalarValue s := by
    simp only [scalarValue, kt.1 .r8 (by decide), kt.1 .r9 (by decide),
      kt.1 .r10 (by decide), kt.1 .r11 (by decide)]
  have hp2 : (t.gpr .rbp).toNat = (s.mem (s.gpr .rsi + BitVec.ofNat 64 n)).toNat := by
    rw [hp1, BitVec.toNat_setWidth_of_le (by decide)]
  rw [WP.block_append_iff]
  refine WP.mono (scalarEight_ok t (hv1 ▸ hv) (by rw [hp2]; exact BitVec.isLt _))
    fun u ⟨hu, ku⟩ => ?_
  refine WP.mono (scalarTest_ok u n hn ((ku.1 .rbx (by decide)).trans hb1))
    fun v ⟨hz, hv2, kv⟩ => ?_
  have k1 : Keeps scalarBodyClob s t := kt.mono (by simp [scalarBodyClob])
  have k2 : Keeps scalarBodyClob t u := ku.mono (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  have k3 : Keeps scalarBodyClob u v := kv.mono (by simp)
  refine ⟨(kv.1 .rbx (by decide)).trans ((ku.1 .rbx (by decide)).trans hb1), hz, ?_,
    k1.trans (k2.trans k3)⟩
  rw [hv2, hu, hp2, hv1]

end VG.Proof.Ed25519.X86_64
