import VerifiedGarbage.Impl.Ed25519.X86.RecoverSign
import VerifiedGarbage.Proof.Ed25519.X86.FieldCheck
import VerifiedGarbage.Proof.Ed25519.X86.PointEncodeSign

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def signWord (b : Bool) : BitVec 32 := BitVec.ofNat 32 b.toNat

theorem parity_eq (w : BitVec 32) (b : Bool) :
    ((w &&& 1) ^^^ signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have he : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 32 by omega)]
  rw [he]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (b : Bool) (hb : s.gpr .esi = signWord b) :
    WP isa (.block recoverParity) s fun t => FieldKeep x s t ∧ t.mem = s.mem ∧
      t.zf = some ((fe s.mem x 64 % 2 == 1) == b) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_andi fun c hc' => Wp.wp_xor fun d hd => Wp.wp_test fun t ht zt => WP.block_nil ?_
  have kk := (updKeep ha).trans ((updKeep hc').trans (updKeep hd))
  have kt : Keep s t := kk.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩
  have mt : t.mem = s.mem := by rw [ht.mem, hd.mem, hc'.mem, ha.mem]
  refine ⟨FieldKeep.of_mem kt mt, mt, ?_⟩
  rw [zt, BitVec.and_self, hd.gpr, hc'.gpr, hc'.other .esi (by decide), ha.other .esi (by decide), hb, ha.gpr]
  rw [field_parity]
  exact congrArg some (parity_eq _ b)

theorem returnFlag_ok (s : State) (x : BitVec 32) (b : Bool) :
    WP isa (.block [.mov .eax (.imm (signWord b))]) s fun t =>
      FieldKeep x s t ∧ t.mem = s.mem ∧ t.gpr .eax = signWord b := by
  refine Wp.wp_movi fun t ht => WP.block_nil ⟨FieldKeep.of_mem (updKeep ht) ht.mem, ht.mem, ht.gpr⟩

end VG.Proof.Ed25519.X86
