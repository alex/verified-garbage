import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Preserve

/-! Argument blocks composed with the signer's scalar and group calls. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarBaseName scalarBase_precomputed scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem reduce_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (out : Nat)
    (ho : out + 32 ≤ 128) {digest : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = digest) :
    WP isa (reduce out) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + out)) 32 = Spec.Ed25519.scalarReduce digest ∧
      Frame (reduceWr L out ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine WP.seq (WP.mono (reduceArgs_ok hc ho) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (reduce_call hL hu ha ho (hm ▸ hh)) fun w ⟨hw, h, hf⟩ => ⟨hw, h, hm ▸ hf⟩

theorem base_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) {scalar : List Byte}
    (hs : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 = scalar) :
    WP isa (callWith baseArgs (scalarBaseName fs) (scalarBase_precomputed fld)) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 = Spec.Ed25519.scalarBase scalar ∧
      Frame (baseWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine WP.seq (WP.mono (baseArgs_ok hc) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (base_ok hL hu ha (hm ▸ hs)) fun w ⟨hw, h, hf⟩ => ⟨hw, h, hm ▸ hf⟩

theorem mul_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.out + BitVec.ofNat 64 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 112) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32) ∧
      Frame (mulWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine WP.seq (WP.mono (mulArgs_ok hc) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (mul_call hL hu ha) fun w ⟨hw, h, hf⟩ => ⟨hw, hm ▸ h, hm ▸ hf⟩

end VG.Proof.Ed25519.X86_64.SignCached
