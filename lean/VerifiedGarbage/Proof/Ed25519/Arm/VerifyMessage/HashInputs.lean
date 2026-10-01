import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.HashFrame

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
variable {L : Lay}

structure Input (L : Lay) (p n : BitVec 32) : Prop where
  cover : Whole.Within ⟨State.addr p, n.toNat⟩ L.FR ∨
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨State.addr p, n.toNat⟩ R
  scratch : Region.Disjoint ⟨State.addr p, n.toNat⟩ L.SCR
  args : Region.Disjoint ⟨State.addr p, n.toNat⟩ (slots L)
  fit : p.toNat + n.toNat ≤ 2 ^ 32

theorem input_self {r : Region} (hr : r ∈ L.inputs) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩

theorem input_slots (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) : r.Disjoint (slots L) :=
  (hL.ks _ hr).symm.sub_right (Region.sub_prefix (by decide))

theorem key_input (hL : L.Ok) : Input L L.pk 32 :=
  ⟨.inr (input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.np⟩

theorem message_input (hL : L.Ok) : Input L L.msg L.len :=
  ⟨.inr (input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.nm⟩

theorem signature_input (hL : L.Ok) : Input L L.sig 32 := by
  have sub : Region.Sub ⟨State.addr L.sig,32⟩ L.SIG := Region.sub_prefix (by decide)
  exact ⟨.inr ⟨L.SIG,by simp [Lay.inputs],0,by simp,by change 0+32≤64; decide⟩,
    (hL.sc _ (by simp [Lay.inputs])).sub_left sub,
    (input_slots hL (by simp [Lay.inputs])).sub_left sub,by have := hL.ns; change L.sig.toNat+32≤2^32; omega⟩

end VG.Proof.Ed25519.Arm.VerifyMessage
