import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Preserve
import VerifiedGarbage.Impl.Ed25519.Arm.SignCached
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem prune_ctx {t : State} (hc : Ctx L g m₀ s) (ht : PublicKey.Step s t)
    (hf : Frame [⟨State.addr L.E + 24, 32⟩] s.mem t.mem) : Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 24 + 32 ≤ 248))

theorem prefix_ctx {t : State} (hc : Ctx L g m₀ s) (ht : PrefixStep s t)
    (hf : Frame [⟨State.addr L.E + BitVec.ofNat 64 56, 32⟩] s.mem t.mem) : Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 56 + 32 ≤ 248))

theorem saveSecret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + 56) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : (⟨State.addr L.E, 248⟩ : Region) ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  have fit : L.E.toNat + 248 ≤ 2 ^ 32 := by have := hL.top; omega
  refine WP.mono (PublicKey.prune_ok hc.sp fit fr he) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := prune_ctx hc hu hf
  refine WP.mono (prefix_ok hcu.sp fit (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨prefix_ctx hcu ht hft, ?_, ?_⟩
  · have keep := single_frame_bytes (L := L) hft (d := 24) (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 = Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32 at keep
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (State.addr L.E + 24) 32
    change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr L.E + 24) 32) = Spec.Ed25519.prune expanded at hs
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := single_frame_bytes (L := L) (e := 24) (k := 32) hf (d := 216)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (State.addr L.E + 216) 32 = Spec.Ed25519.bytesAt s.mem (State.addr L.E + 216) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (184 : BitVec 64) + BitVec.ofNat 64 32 = (216 : BitVec 64) from rfl]

def expanded (L : Lay) (m : Mem) : List Byte := Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m (State.addr L.seed) 32)
def scalar (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (expanded L m))
def nonce (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
  ((expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m (State.addr L.msg) L.len.toNat))

structure SecretReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 24) 32 = scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (State.addr L.E + 56) 32 = (expanded L m).drop 32

end VG.Proof.Ed25519.Arm.SignCached
