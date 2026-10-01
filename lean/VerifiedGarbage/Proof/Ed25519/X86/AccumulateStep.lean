import VerifiedGarbage.Proof.Ed25519.X86.PointAccumulate

/-! Untrusted: descending bits follow the exact pointMul recursion. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def scalarBit (s n : Nat) : Bool := decide ((s / 2 ^ n) % 2 ≠ 0)

theorem scalarBit_nat (s n : Nat) : (scalarBit s n).toNat = (s / 2 ^ n) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ n) with h | h <;> simp only [scalarBit, h] <;> decide

theorem choose_after (s n : Nat) (p x y : Spec.Ed25519.Point)
    (hx : x = after s p (n + 1)) (hy : y = powerPoint p n) :
    (if scalarBit s n then Spec.Ed25519.pointAdd x y else x) = after s p n := by
  rw [hx, hy]
  have h := (after_step s p n).symm
  by_cases hz : (s / 2 ^ n) % 2 = 0
  · simpa only [scalarBit, hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ite_false, ite_true] using h
  · simpa only [scalarBit, hz, ne_eq, not_false_eq_true, decide_true, ite_true, ite_false] using h

theorem IKeep.word {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 64) : wd t.mem x o = wd s.mem x o :=
  wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

theorem IKeep.bit {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (sub x (7168 + i) 1).Disjoint (sub x 64 864)) _ (Region.contains_self _ _)

theorem accumulateBody_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (n batch scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hb : batch < 32)
    (hindex : wd s.mem x 28 = BitVec.ofNat 32 batch)
    (hcounter : s.gpr .esi = BitVec.ofNat 32 (n + 1))
    (hbit : s.mem (addr x (7168 + (16 * batch + n))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * batch + n)).toNat)
    (hd : env s.mem x 16 = Spec.Ed25519.d)
    (hp : point (env s.mem x) 0 1 2 3 = after scalar p (16 * batch + n + 1))
    (ht : tablePoint s.mem x (5120 + 128 * n) = powerPoint p (16 * batch + n)) :
    WP isa (.block accumulateBody) s fun t =>
      IKeep x s t ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      isa.eval .ne t = some (!decide (n = 0)) ∧
      point (env t.mem x) 0 1 2 3 = after scalar p (16 * batch + n) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  simp only [accumulateBody, List.append_assoc]
  rw [WP.block_append_iff]
  refine Wp.wp_subi fun u hu _ _ => WP.block_nil ?_
  have ku : IKeep x s u := IKeep.of_counter hu
  have bu : u.gpr .esi = BitVec.ofNat 32 n := by
    rw [hu.gpr, hcounter]
    exact (Wp.ofNat_pred (by omega)).trans (congrArg (BitVec.ofNat 32) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (pointAccumulate_ok (ku.ctx hc) batch n hb hn
    (by rw [hu.mem]; exact hindex) bu (scalarBit scalar (16 * batch + n))
    (by rw [hu.mem]; exact hbit) (by rw [hu.mem]; exact hd)) fun v ⟨kv, pv, dv⟩ => ?_
  have bv := kv.keep.esi.trans bu
  have vp : point (env v.mem x) 0 1 2 3 = after scalar p (16 * batch + n) :=
    pv.trans (choose_after scalar (16 * batch + n) p _ _
      ((congrArg (fun m => point (env m x) 0 1 2 3) hu.mem).trans hp)
      ((congrArg (fun m => tablePoint m x (5120 + 128 * n)) hu.mem).trans ht))
  refine Wp.wp_test fun t kt zt => WP.block_nil ?_
  have keep : Keep v t := ⟨by rw [kt.gpr], by rw [kt.gpr], by rw [kt.gpr], kt.rd, kt.wr⟩
  refine ⟨ku.trans ((IKeep.of_field kv).trans (IKeep.of_mem keep kt.mem)),
    (congrFun kt.gpr .esi).trans bv, ?_, ?_, ?_⟩
  · show t.zf.map (!·) = _
    rw [zt, BitVec.and_self, bv, Wp.ofNat_beq_zero (by omega)]; rfl
  · rw [kt.mem]; exact vp
  · rw [kt.mem]; exact dv

end VG.Proof.Ed25519.X86
