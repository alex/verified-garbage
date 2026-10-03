import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.Mul

/-! Exact multiplication uses the field multiplier's checked row loop,
but stops before folding the high 256 bits modulo the field prime. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarWideMul_ok {b : BitVec 32} {x y : Nat}
    (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC) {s : State}
    (hc : Ctx b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (scalarWideMul x y) s fun t =>
      Rest clob s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      (∀ k < 32, accw ACC t.mem (State.addr b) k < 65536) ∧
      val16 (accw ACC t.mem (State.addr b)) 32 = V s.mem (State.addr b) x * V s.mem (State.addr b) y := by
  unfold scalarWideMul
  refine WP.seq (WP.mono (mulPre_ok (by decide) (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.mono (Q := RowInv 4096 ACC b x y s 16) (WP.loop (M := isa)
    (fun n t => ∃ i, n = 16 - i ∧ i < 16 ∧ RowInv 4096 ACC b x y s i t) ?_ 16 s1
    ⟨0, rfl, by decide, h1⟩) fun t ht => ⟨ht.rest, ht.frame, ht.lt, ht.val⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (row_ok (by decide) hx hy hlx hly hi ht) fun u ⟨hu, hz⟩ => ?_
  by_cases h16 : i + 1 = 16
  · refine .inl ⟨by rw [eval_ne, hz]; simp [h16], ?_⟩
    rw [h16] at hu; exact hu
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega, 16 - (i + 1), by omega,
      i + 1, rfl, by omega, hu⟩

end VG.Proof.Ed25519.Arm
