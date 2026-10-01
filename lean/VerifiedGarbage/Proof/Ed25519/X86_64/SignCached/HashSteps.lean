import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.HashFrame

/-! Hash calls with explicit preservation of the signer's other buffers. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem init_step (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa init t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr [] ∧ HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono (initArgs_ok hc) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (init_call hL hu ha) fun w ⟨hw, hr, hf⟩ => ⟨hw, hr, hm ▸ init_frame hf⟩

theorem update_step (v : Compress) (hL : L.Ok) {t : State} (_hc : Ctx L g mx m₀ t)
    {prev : List Byte} {p : Addr} {n : BitVec 64} {args : List Instr}
    (hi : Input L ⟨p, n.toNat⟩)
    (ha : WP isa (.block args) t fun u => Ctx L g mx m₀ u ∧ u.mem = t.mem ∧
      UpdArgs L (BitVec.ofNat 64 prev.length) p n u)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev) :
    WP isa (update v.callee v.suffix args) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t'.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt t.mem p n.toNat) ∧ HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono ha fun u ⟨hu, hm, hau⟩ => ?_)
  exact WP.mono (upd_call v hL hu hau hi rfl (hm ▸ hr)) fun w ⟨hw, hrw, hf⟩ =>
    ⟨hw, hm ▸ hrw, hm ▸ upd_frame hf⟩

theorem finalize_step (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    {message : List Byte} (prefixLen : Nat) (hp : prefixLen < 2 ^ 31) (withMessage : Bool)
    (hmess : message.length < 2 ^ 64)
    (hlen : (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen) =
      BitVec.ofNat 64 message.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr message) :
    WP isa (finalize v.callee v.suffix prefixLen withMessage) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Sha512.bytesAt t'.mem (L.B + BitVec.ofNat 64 144) 64 = Spec.Sha512.sha512 message ∧
      HashFrame L t.mem t'.mem := by
  refine WP.seq (WP.mono (finalizeArgs_ok hc prefixLen hp withMessage) fun u ⟨hu, hm, ha⟩ => ?_)
  exact WP.mono (fin_call v hL hu ha hmess hlen (hm ▸ hr)) fun w ⟨hw, hd, hf⟩ =>
    ⟨hw, hd, hm ▸ fin_frame hf⟩

end VG.Proof.Ed25519.X86_64.SignCached
