import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarStep
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem

/-! Untrusted: consume one input byte in eight fixed scalar bit steps. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Spec.Ed25519 (L)

theorem scalarBits_ok (js : List Nat) (hj : ∀ j ∈ js, j < 8) (s : State)
    (hr : scalarValue s < L) (hz : s.gpr .x10 = 0) (h1 : s.gpr .x11 = 1) :
    WP isa (.block (js.flatMap scalarBit)) s fun t =>
      scalarValue t = js.foldl (fun v j => (2 * v + ((s.gpr .x20).getLsbD j).toNat) % L)
        (scalarValue s) ∧ Keeps scalarClob s t := by
  induction js generalizing s with
  | nil => exact WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | cons j js ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (scalarBit_ok s j (hj j (by simp)) hr hz h1) fun t ⟨ht, kt⟩ => ?_
    have htL : scalarValue t < L := by rw [ht]; exact Nat.mod_lt _ order_pos
    refine WP.mono (ih (fun i hi => hj i (List.mem_cons_of_mem _ hi)) t htL
      ((kt.gpr .x10 (by decide)).trans hz) ((kt.gpr .x11 (by decide)).trans h1))
      fun u ⟨hu, ku⟩ => ?_
    refine ⟨?_, kt.trans ku⟩
    rw [hu, kt.gpr .x20 (by decide), ht]
    rfl

theorem scalarEight_ok (s : State) (hr : scalarValue s < L) (hb : (s.gpr .x20).toNat < 256)
    (hz : s.gpr .x10 = 0) (h1 : s.gpr .x11 = 1) :
    WP isa (.block ((List.range 8).reverse.flatMap scalarBit)) s fun t =>
      scalarValue t = (256 * scalarValue s + (s.gpr .x20).toNat) % L ∧
      Keeps scalarClob s t := by
  refine WP.mono (scalarBits_ok _ (by intro j hj; simpa only [List.mem_reverse, List.mem_range] using hj)
    s hr hz h1) fun t ⟨ht, kt⟩ => ?_
  change scalarValue t = consumeBits (s.gpr .x20) 8 (scalarValue s) at ht
  rw [consumeBits_eq _ _ _ hr, show 2 ^ 8 = 256 from rfl, Nat.mod_eq_of_lt hb] at ht
  exact ⟨ht, kt⟩

def scalarRead : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x9 .x1 .x19, .ldrb .x20 .x9 0]

theorem scalarRead_ok (s : State) (n : Nat) (hb : s.gpr .x19 = BitVec.ofNat 64 (n + 1))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 n) 1) :
    WP isa (.block scalarRead) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧
      t.gpr .x20 = (s.mem (s.gpr .x1 + BitVec.ofNat 64 n)).setWidth 64 ∧
      Keeps [.x19, .x9, .x20] s t := by
  have hn : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 n := by
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [scalarRead, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    show (1 : Nat) < 4096 from by decide, show (0 : Nat) < 4096 * 1 from by decide,
    show (0 : Nat) % 1 = 0 from rfl, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hn, BitVec.add_zero, BitVec.setWidth_eq, hr, read_byte,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · exact BitVec.setWidth_setWidth (by decide)
  · intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RegUpd.gpr_write, h.1, h.2.1, h.2.2, ite_false]

def scalarBodyClob : List Reg := .x19 :: .x20 :: .x9 :: scalarClob

theorem scalarByte_ok (s : State) (n : Nat)
    (hb : s.gpr .x19 = BitVec.ofNat 64 (n + 1))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 n) 1)
    (hv : scalarValue s < L) (hz : s.gpr .x10 = 0) (h1 : s.gpr .x11 = 1) :
    WP isa (.block scalarByte) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧
      scalarValue t = (256 * scalarValue s + (s.mem (s.gpr .x1 + BitVec.ofNat 64 n)).toNat) % L ∧
      Keeps scalarBodyClob s t := by
  rw [show scalarByte = scalarRead ++ (List.range 8).reverse.flatMap scalarBit from rfl,
    WP.block_append_iff]
  refine WP.mono (scalarRead_ok s n hb hr) fun t ⟨hb1, hp1, kt⟩ => ?_
  have hv1 : scalarValue t = scalarValue s := by
    simp only [scalarValue, kt.gpr .x4 (by decide), kt.gpr .x5 (by decide),
      kt.gpr .x6 (by decide), kt.gpr .x7 (by decide)]
  have hp2 : (t.gpr .x20).toNat = (s.mem (s.gpr .x1 + BitVec.ofNat 64 n)).toNat := by
    rw [hp1, BitVec.toNat_setWidth_of_le (by decide)]
  refine WP.mono (scalarEight_ok t (hv1 ▸ hv) (by rw [hp2]; exact BitVec.isLt _)
    ((kt.gpr .x10 (by decide)).trans hz) ((kt.gpr .x11 (by decide)).trans h1))
    fun u ⟨hu, ku⟩ => ?_
  refine ⟨(ku.gpr .x19 (by decide)).trans hb1, ?_,
    (kt.mono (by decide)).trans (ku.mono (by decide))⟩
  rw [hu, hp2, hv1]

end VG.Proof.Ed25519.AArch64
