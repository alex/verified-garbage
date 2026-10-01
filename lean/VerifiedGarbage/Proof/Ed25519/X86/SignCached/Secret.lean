import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Preserve
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.VerifyBytes

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem ctx_step {t : State} (hc : Ctx L g m₀ s) (ht : PublicKey.Step s t) {d n : Nat}
    (hf : Frame [⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩] s.mem t.mem) (hn : d + n ≤ 256) :
    Ctx L g m₀ t := by
  refine hc.of_frame ht.rd ht.wr ht.esp ?_ hf ?_
  · intro r hr _
    apply ht.regs
    rintro rfl; simp [calleeSaved] at hr
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact .inl (Offset.sub_base _ hn)

theorem saveSecret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) {expanded : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 192) 64 = expanded) :
    WP isa (.block saveSecret) s fun t => Ctx L g m₀ t ∧
      Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 64) 32 = expanded.drop 32 := by
  rw [saveSecret, WP.block_append_iff]
  have fr : Whole.FR L.E ∈ s.wr := by rw [hc.wr]; exact List.mem_cons_self
  have fit := (hashSpace hL).frameFit
  refine WP.mono (PublicKey.prune_ok hc.esp fit fr he) fun u ⟨hu, hf, hs⟩ => ?_
  have hcu := ctx_step hc hu (d := 32) (n := 32) hf (by decide)
  refine WP.mono (prefix_ok hcu.esp fit (by rw [hcu.wr]; exact List.mem_cons_self))
    fun t ⟨ht, hft, hp⟩ => ⟨ctx_step hcu ht (d := 64) (n := 32) hft (by decide), ?_, ?_⟩
  · rw [fp_addr hL (by decide)]
    have keep := single_frame_bytes (L := L) hft (d := 32) (n := 32) (e := 64) (k := 32)
      (by decide) (by decide) (by decide)
    rw [keep]
    have sc := Proof.Ed25519.bytesAt_encodeLE u.mem (L.E.setWidth 64 + 32) 32
    rw [hs] at sc
    exact sc
  · rw [hp]
    have keep := single_frame_bytes (L := L) hf (d := 224) (n := 32) (e := 32) (k := 32)
      (by decide) (by decide) (by decide)
    change Spec.Ed25519.bytesAt u.mem (L.E.setWidth 64 + (224 : BitVec 64)) 32 =
      Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + (224 : BitVec 64)) 32 at keep
    rw [keep, ← he, Proof.Ed25519.signatureBytes_drop]
    rw [BitVec.add_assoc, show (192 : BitVec 64) + BitVec.ofNat 64 32 = (224 : BitVec 64) from rfl]

def expanded (L : Lay) (m : Mem) : List Byte :=
  Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m (L.seed.setWidth 64) 32)
def scalar (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (expanded L m))
def nonce (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
    ((expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m (L.msg.setWidth 64) L.len.toNat))

structure SecretReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem ((fp L 32).setWidth 64) 32 = scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 64) 32 = (expanded L m).drop 32

theorem secret_ok (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (.seq hashSeed (.block saveSecret)) s fun t => Ctx L g m₀ t ∧ SecretReady L m₀ t := by
  refine WP.seq (WP.mono (hashSeed_ok hc hL ha) fun u ⟨hu, _, hd⟩ => ?_)
  exact WP.mono (saveSecret_ok hu hL hd) fun t ⟨ht, hs, hp⟩ => ⟨ht, hs, hp⟩

end VG.Proof.Ed25519.X86.SignCached
