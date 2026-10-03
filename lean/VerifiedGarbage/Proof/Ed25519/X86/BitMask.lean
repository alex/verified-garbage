import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBody

/-! Only public counters determine the address of a secret scalar bit. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem FieldKeep.word {x : BitVec 32} {s t : State} (h : FieldKeep x s t) (hc : Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 64) : wd t.mem x o = wd s.mem x o :=
  wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

theorem FieldKeep.bit {x : BitVec 32} {s t : State} (h : FieldKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (sub x (7168 + i) 1).Disjoint (sub x 64 864)) _ (Region.contains_self _ _)

theorem scalarBitMask_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (batch j : Nat) (hb : batch < 32) (hj : j < 16)
    (hbv : wd s.mem x 28 = BitVec.ofNat 32 batch) (hjv : s.gpr .esi = BitVec.ofNat 32 j)
    (bit : Bool) (hbit : s.mem (addr x (7168 + (16 * batch + j))) = BitVec.ofNat 8 bit.toNat) :
    WP isa (.block scalarBitMask) s fun t =>
      FieldKeep x s t ∧ t.mem = s.mem ∧ t.gpr .ecx = mask (!bit).toNat := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha =>
    Wp.wp_movi fun b hb' => wp_mul fun c hmul => ?_
  refine Wp.wp_add fun d hd _ => Wp.wp_add fun e he _ => ?_
  have pk : Keep s e := (updKeep ha).trans ((updKeep hb').trans (hmul.keep.trans
    ((updKeep hd).trans (updKeep he))))
  have pc : c.gpr .eax = BitVec.ofNat 32 (16 * batch) := by
    apply BitVec.eq_of_toNat_eq
    change v c .eax = _
    rw [hmul.eax]
    simp only [v, hb'.other .eax (by decide), ha.gpr, hb'.gpr]
    change (wd s.mem x 28).toNat * 16 % 2 ^ 32 = _
    rw [hbv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show batch < 2 ^ 32 by omega)]
    exact congrArg (fun n => n % 2 ^ 32) (Nat.mul_comm batch 16)
  have pe : addr (e.gpr .eax) 7168 = addr x (7168 + (16 * batch + j)) := by
    rw [he.gpr, hd.gpr, pc, hmul.other .esi (by decide) (by decide),
      hb'.other .esi (by decide), ha.other .esi (by decide), hjv,
      hd.other .edi (by decide), hmul.other .edi (by decide) (by decide),
      hb'.other .edi (by decide), ha.other .edi (by decide), hc.edi]
    rw [← BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 32 (16 * batch + j)) x, addr_plus,
      Nat.add_comm (16 * batch + j) 7168]
  refine scalar_ld8 pe ((pk.ctx hc).inRW (by omega) (by decide)) fun f hf =>
    Wp.wp_subi fun g hg _ _ => WP.block_nil ?_
  have km : g.mem = s.mem := by rw [hg.mem, hf.mem, he.mem, hd.mem, hmul.mem, hb'.mem, ha.mem]
  refine ⟨FieldKeep.of_mem (pk.trans ((updKeep hf).trans (updKeep hg))) km, km, ?_⟩
  rw [hg.gpr, hf.gpr, he.mem, hd.mem, hmul.mem, hb'.mem, ha.mem, hbit]
  cases bit <;> decide

end VG.Proof.Ed25519.X86
