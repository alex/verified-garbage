import VerifiedGarbage.Proof.Ed25519.Arm.VerifyHeaders

/-! Untrusted: branch only on the public point-decoding result. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem decodedThen_ok {s : State} {next : Prog isa} {P : State → Prop} (flag : Bool)
    (hv : s.gpr .r9 = BitVec.ofNat 32 flag.toNat)
    (hy : flag = true → ∀ u, Rest [] s u → u.mem = s.mem → WP isa next u P)
    (hn : flag = false → ∀ u, Rest [] s u → u.mem = s.mem → WP isa recoverInvalid u P) :
    WP isa (decodedThen next) s P := by
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun u hu hz => WP.block_nil ?_)
  have he : VG.Arm.eval .ne u = some flag := by
    rw [VG.Arm.eval, hz, hv]
    cases flag <;> rfl
  apply WP.ite flag he
  · intro h; exact hy h u (hu.rest []) hu.mem
  · intro h; exact hn h u (hu.rest []) hu.mem

end VG.Proof.Ed25519.Arm
