import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody
import VerifiedGarbage.Impl.Ed25519.X86.BitsExpand

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

theorem scalar_store8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {o : Nat} {r : Reg8} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hout : InRegions s.wr a 1)
    (k : ∀ t, Wp.Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  change (s.gpr b + BitVec.ofNat 32 o).setWidth 64 = a at ha
  simp only [exec, State.store8, State.ea, ha, hout, ite_true]

theorem doubled_byte_bit (b : Byte) (j : Nat) :
    ((((b.setWidth 32 + b.setWidth 32) >>> (j + 1)) &&& 1).setWidth 8) =
      BitVec.ofNat 8 (b.toNat / 2 ^ j % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and]
  change (((b.setWidth 32 + b.setWidth 32) >>> (j + 1)).toNat &&& (2 ^ 1 - 1)) % 2 ^ 8 = _
  rw [Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by decide)]
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat + b.toNat) (b := 2 ^ 32) (by omega_using [hb]),
    show 2 ^ (j + 1) = 2 * 2 ^ j by rw [Nat.pow_succ'], ← Nat.div_div_eq_div_mul,
    show (b.toNat + b.toNat) / 2 = b.toNat by omega_using []]
  rfl

theorem expandScalarBit_ok {x p : BitVec 32} {s : State} (hc : Ctx x s) (hp : s.gpr .esi = p)
    {k : Nat} (hk : k < 512) (hr : InRegions (s.rd ++ s.wr) (addr p (k / 8)) 1) :
    WP isa (.block (expandScalarBit k)) s fun t => Keep s t ∧
      t.mem = s.mem.writeW (addr x (7168 + k))
        (BitVec.ofNat 8 ((s.mem (addr p (k / 8))).toNat / 2 ^ (k % 8) % 2)) := by
  refine scalar_ld8 (by rw [hp]) hr fun u₁ h₁ => ?_
  refine Wp.wp_add fun u₂ h₂ _ => Wp.wp_shr
    (by have h := Nat.mod_lt k (by decide : 0 < 8); omega_using [h]) fun u₃ h₃ _ => ?_
  refine Wp.wp_andi fun u₄ h₄ => ?_
  have k₄ := (updKeep h₁).trans ((updKeep h₂).trans ((updKeep h₃).trans (updKeep h₄)))
  have c₄ := k₄.ctx hc
  refine scalar_store8 (by rw [c₄.edi]) (c₄.inW (by omega_using [hk]) (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨k₄.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_⟩
  rw [ht.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  change s.mem.writeW _ ((u₄.gpr .eax).setWidth 8) = _
  rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr, doubled_byte_bit]

theorem bits_byte_write_self (m : Mem) (a : Addr) (v : Byte) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem bits_byte_write_ne (m : Mem) {x : BitVec 32} (v : Byte) {d e : Nat}
    (hd : x.toNat + d + 1 ≤ 2 ^ 32) (he : x.toNat + e + 1 ≤ 2 ^ 32) (h : d ≠ e) :
    (m.writeW (addr x e) v) (addr x d) = m (addr x d) := by
  have hdisj := sub_disj (x := x) (n := 1) (k := 1) hd he (by omega_using [h])
  exact Mem.write_apply fun h' => hdisj _ (Region.contains_self _ _) (by
    simp only [Region.Contains]; omega_using [h'])
end VG.Proof.Ed25519.X86
