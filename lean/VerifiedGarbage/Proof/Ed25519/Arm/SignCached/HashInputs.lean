import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.HashFrame

namespace VG.Proof.Ed25519.Arm.SignCached
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

theorem seed_input (hL : L.Ok) : Input L L.seed 32 :=
  ⟨.inr (input_self (r := L.SEED) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.ns⟩

theorem key_input (hL : L.Ok) : Input L L.pk 32 :=
  ⟨.inr (input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.np⟩

theorem message_input (hL : L.Ok) : Input L L.msg L.len :=
  ⟨.inr (input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs]),
    input_slots hL (by simp [Lay.inputs]), hL.nm⟩

theorem point_input (hL : L.Ok) : Input L L.out 32 :=
  ⟨.inr (output_covered (baseWithin L)), hL.oc.sub_left (baseWithin L).sub,
    (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (Region.sub_prefix (by decide)),
    by have := hL.no; change L.out.toNat + 32 ≤ 2 ^ 32; omega⟩

theorem prefix_input (hL : L.Ok) : Input L (L.E + 56) 32 := by
  have ae : State.addr (L.E + 56) = State.addr L.E + 56 := frame_addr hL (d := 56) (by decide)
  refine ⟨?_, ?_, ?_, frame_fit hL (d := 56) (by decide)⟩
  · rw [ae]
    exact .inl (fieldWithin L (by decide))
  · rw [ae]
    exact field_scr hL (by decide)
  · rw [ae]
    exact Offset.disjoint_base _ (by decide) (by decide)

end VG.Proof.Ed25519.Arm.SignCached
