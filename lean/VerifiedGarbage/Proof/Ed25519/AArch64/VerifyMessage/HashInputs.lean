import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Hash

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.VerifyMessage
variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem prefix_step (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {source count : Nat} (hsource : source < 5)
    (hcount : count < 65536) {prev : List Byte} (hp : prev.length = count)
    (hd : Region.Disjoint ⟨L.value source,32⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨L.value source,32⟩ R)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix (prefixArgs source count)) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.value source) 32) := by
  apply update_ok backend hc hL ha (by simp)
    (by simp [Whole.valid]; omega) (by simp [known]; exact hsource) (by simp [preserved])
    (p := L.value source) (len := 32) (prev := prev) ?_ hd hi hr
  intro t hav
  have a0 := hav (.x0,.caller 4 0) (by simp)
  have a1 := hav (.x1,.const count) (by simp)
  have a2 := hav (.x2,.caller source 0) (by simp)
  have a3 := hav (.x3,.const 32) (by simp)
  have a4 := hav (.x4,.caller 4 192) (by simp)
  change t.gpr .x0 = L.scr + 0#64 at a0
  change t.gpr .x2 = L.value source + 0#64 at a2
  rw [BitVec.add_zero] at a0 a2
  exact ⟨a0, by rw [hp]; exact a1, a2, a3, a4⟩

theorem message_step (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {prev : List Byte} (hp : prev.length = 64)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix messageArgs) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem L.msg L.len.toNat) := by
  apply update_ok backend hc hL ha (by simp) (by simp [Whole.valid])
    (by simp [known]) (by decide) (p := L.msg) (len := L.len) (prev := prev) ?_
    (hL.sc _ (by simp [Lay.inputs])) ?_ hr
  · intro t hav
    have a0 := hav (.x0,.caller 4 0) (by simp)
    have a1 := hav (.x1,.const 64) (by simp)
    have a2 := hav (.x2,.caller 1 0) (by simp)
    have a3 := hav (.x3,.caller 2 0) (by simp)
    have a4 := hav (.x4,.caller 4 192) (by simp)
    change t.gpr .x0 = L.scr + 0#64 at a0
    change t.gpr .x2 = L.msg + 0#64 at a2
    change t.gpr .x3 = L.len + 0#64 at a3
    rw [BitVec.add_zero] at a0 a2 a3
    exact ⟨a0, by rw [hp]; exact a1, a2, a3, a4⟩
  · exact ⟨L.MSG, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by simp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
