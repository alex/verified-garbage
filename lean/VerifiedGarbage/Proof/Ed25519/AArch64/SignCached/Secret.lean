import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Preserve
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem prune_ctx {t : State} (hc : Ctx L g vec m₀ s) (ht : PublicKey.Step s t)
    (hf : Frame [⟨s.sp + 32, 32⟩] s.mem t.mem) : Ctx L g vec m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r _; rw [ht.v]
  · intro r hr; rw [List.mem_singleton.mp hr, hc.sp]
    exact .inl (Offset.sub_base _ (by decide : 32 + 32 ≤ 256))

theorem prefix_ctx {t : State} (hc : Ctx L g vec m₀ s) (ht : PrefixStep s t)
    (hf : Frame [⟨L.E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem) : Ctx L g vec m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.sp ?_ ?_ hf ?_
  · intro r hr _
    apply ht.regs <;> rintro rfl <;> simp [preserved] at hr
  · intro r _; rw [ht.vec]
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ (by decide : 64 + 32 ≤ 256))

theorem saveSecret_ok (hc : Ctx L g vec m₀ s) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E + 192) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 64) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : (⟨s.sp, 256⟩ : Region) ∈ s.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hd : Spec.Sha512.bytesAt s.mem (s.sp + 192) 64 = expanded := by rw [hc.sp]; exact he
  refine WP.mono (PublicKey.prune_ok fr hd) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := prune_ctx hc hu hf
  rw [hc.sp] at hf hs
  refine WP.mono (prefix_ok hcu.sp (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨prefix_ctx hcu ht hft, ?_, ?_⟩
  · have keep := single_frame_bytes (L := L) hft (d := 32) (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = Spec.Ed25519.bytesAt u.mem (L.E + 32) 32 at keep
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (L.E + 32) 32
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := single_frame_bytes (L := L) (e := 32) (k := 32) hf (d := 224)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (L.E + 224) 32 = Spec.Ed25519.bytesAt s.mem (L.E + 224) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (192 : BitVec 64) + BitVec.ofNat 64 32 = (224 : BitVec 64) from rfl]

def expanded (L : Lay) (m : Mem) : List Byte := Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m L.seed 32)
def scalar (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (expanded L m))
def nonce (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
  ((expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

structure SecretReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.E + 64) 32 = (expanded L m).drop 32

theorem secret_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (secretCode b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧ SecretReady L m₀ t := by
  refine WP.seq (WP.mono (hashSeed_ok b hc hL ha) fun u ⟨hu, _, hd⟩ => ?_)
  exact WP.mono (saveSecret_ok hu hd) fun t ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩

end VG.Proof.Ed25519.AArch64.SignCached
