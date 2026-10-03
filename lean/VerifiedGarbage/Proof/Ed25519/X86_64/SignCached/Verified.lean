import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Preserve
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Args
import VerifiedGarbage.Spec.Ed25519.CachedSign
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Body`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.Finish`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.Challenge`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.Nonce`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.Secret`. -/
section
/-! Expand the seed and save both the pruned scalar and the nonce prefix. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem saveSecret_ok {t : State} (hc : Ctx L g mx m₀ t) {expanded : List Byte}
    (he : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = expanded) :
    WP isa (.block saveSecret) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 =
        Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune expanded) ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 48) 32 = expanded.drop 32 := by
  rw [saveSecret, List.append_assoc, WP.block_append_iff]
  refine WP.mono (prune_ok hc he) fun u ⟨hu, hf, hs⟩ => ?_
  have hd : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 144) 64 = expanded :=
    (single_stk_bytes hf (by decide) (by decide) (by decide)).trans he
  refine WP.mono (prefix_ok hu) fun w ⟨hw, hfw, hp⟩ => ⟨hw, ?_, ?_⟩
  · rw [single_stk_bytes hfw (by decide : 16 + 32 ≤ 48 ∨ 48 + 32 ≤ 16) (by decide) (by decide)]
    rw [Proof.Ed25519.bytesAt_encodeLE u.mem, hs]
  · rw [hp, hd]

def expanded (L : Lay) (m : Mem) : List Byte :=
  Spec.Sha512.sha512 (Spec.Ed25519.bytesAt m L.seed 32)
def scalar (L : Lay) (m : Mem) : List Byte := Spec.Ed25519.encodeLE 32 (Spec.Ed25519.prune (expanded L m))
def nonce (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512
    ((expanded L m).drop 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

structure SecretReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m
  prefixBytes : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 48) 32 = (expanded L m).drop 32

theorem secret_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.seq (hashSeed v.callee v.suffix) (.block saveSecret)) t fun t' =>
      Ctx L g mx m₀ t' ∧ SecretReady L m₀ t' := by
  have he : Spec.Ed25519.bytesAt t.mem L.seed 32 = Spec.Ed25519.bytesAt m₀ L.seed 32 :=
    hc.input_bytes hL (r := L.SEED) (by simp [Lay.inputs]) (by decide : 32 ≤ 2 ^ 64)
  refine WP.seq (WP.mono (hashSeed_ok v hL hc) fun u ⟨hu, hd, _⟩ => ?_)
  rw [he] at hd
  exact WP.mono (saveSecret_ok hu hd) fun w ⟨hw, hs, hp⟩ => ⟨hw, hs, hp⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Calls`. -/
section
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
end

/-! Hash and reduce the deterministic nonce, then encode its base-point multiple. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarBaseName scalarBase_precomputed)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

structure NonceReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 = nonce L m
  point : Spec.Ed25519.bytesAt t.mem L.out 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

def nonceCode (fld : VG.Impl.Ed25519.X86_64.Arith) (fs : String) (v : Compress) : Prog isa :=
  .seq (hashNonce v.callee v.suffix) (.seq (reduce 64)
    (callWith baseArgs (scalarBaseName fs) (scalarBase_precomputed fld)))

theorem nonce_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hs : SecretReady L m₀ t) (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (nonceCode fld fs v) t fun t' => Ctx L g mx m₀ t' ∧ NonceReady L m₀ t' := by
  have hm : Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat = Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat :=
    hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (Nat.le_of_lt L.len.isLt)
  refine WP.seq (WP.mono (hashNonce_ok v hL hc (by omega)) fun u ⟨hu, hd, hf⟩ => ?_)
  rw [hs.prefixBytes, hm] at hd
  have hsu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m₀ :=
    (hash_stk_bytes hL hf (d := 16) (n := 32) (by decide) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (reduce_step hL hu 64 (by decide) hd) fun w ⟨hw, hn, hfw⟩ => ?_)
  change Spec.Ed25519.bytesAt w.mem (L.B + BitVec.ofNat 64 80) 32 = nonce L m₀ at hn
  have hsw : Spec.Ed25519.bytesAt w.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m₀ :=
    (reduce_stk_bytes hL hfw (d := 16) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hsu
  refine WP.mono (base_step hL hw hn) fun z ⟨hz, hp, hfz⟩ => ⟨hz, ?_, ?_, hp⟩
  · exact (base_stk_bytes hL hfz (d := 16) (n := 32) (by decide) (by decide)).trans hsw
  · exact (base_stk_bytes hL hfz (d := 80) (n := 32) (by decide) (by decide)).trans hn

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Bind the nonce point, cached public key and message into the signing challenge. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def challenge (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.scalarReduce (Spec.Sha512.sha512 (Spec.Ed25519.scalarBase (nonce L m) ++
    Spec.Ed25519.bytesAt m L.pk 32 ++ Spec.Ed25519.bytesAt m L.msg L.len.toNat))

structure ChallengeReady (L : Lay) (m : Mem) (t : State) : Prop extends NonceReady L m t where
  challenge : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 112) 32 = challenge L m

def challengeCode (v : Compress) : Prog isa := .seq (hashChallenge v.callee v.suffix) (reduce 96)

theorem challenge_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hs : NonceReady L m₀ t) (hlen : 64 + L.len.toNat < 2 ^ 64) :
    WP isa (challengeCode v) t fun t' => Ctx L g mx m₀ t' ∧ ChallengeReady L m₀ t' := by
  have hp : Spec.Ed25519.bytesAt t.mem L.pk 32 = Spec.Ed25519.bytesAt m₀ L.pk 32 :=
    hc.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by decide : 32 ≤ 2 ^ 64)
  have hm : Spec.Ed25519.bytesAt t.mem L.msg L.len.toNat = Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat :=
    hc.input_bytes hL (r := L.MSG) (by simp [Lay.inputs]) (Nat.le_of_lt L.len.isLt)
  refine WP.seq (WP.mono (hashChallenge_ok v hL hc hlen) fun u ⟨hu, hd, hf⟩ => ?_)
  rw [hs.point, hp, hm] at hd
  have hsu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 16) 32 = scalar L m₀ :=
    (hash_stk_bytes hL hf (d := 16) (n := 32) (by decide) (by decide)).trans hs.scalar
  have hnu : Spec.Ed25519.bytesAt u.mem (L.B + BitVec.ofNat 64 80) 32 = nonce L m₀ :=
    (hash_stk_bytes hL hf (d := 80) (n := 32) (by decide) (by decide)).trans hs.nonce
  have hpu : Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.scalarBase (nonce L m₀) :=
    ((stable_out hL).bytes hf (by decide : 32 ≤ 2 ^ 64)).trans hs.point
  refine WP.mono (reduce_step hL hu 96 (by decide) hd) fun w ⟨hw, hk, hfw⟩ =>
    ⟨hw, ⟨?_, ?_, ?_⟩, hk⟩
  · exact (reduce_stk_bytes hL hfw (d := 16) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hsu
  · exact (reduce_stk_bytes hL hfw (d := 80) (n := 32) (by decide) (by decide) (by decide) (by decide)).trans hnu
  · exact (reduce_out_bytes hL hfw (by decide)).trans hpu

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Complete the signature and clear the secret frame values. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def finishCode : Prog isa := .seq (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) (.block wipe)

theorem finish_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (hs : ChallengeReady L m₀ t)
    (hpk : Spec.Ed25519.bytesAt m₀ L.pk 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa finishCode t fun t' => Ctx L g mx m₀ t' ∧ Spec.Ed25519.bytesAt t'.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
  refine WP.seq (WP.mono (mul_step hL hc) fun u ⟨hu, ho, hf⟩ => ?_)
  rw [hs.nonce, hs.challenge, hs.scalar] at ho
  have hp := (mul_out_bytes hL hf).trans hs.point
  have hout : Spec.Ed25519.bytesAt u.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
    rw [Proof.Ed25519.signatureBytes_split, hp, ho]
    exact Proof.Ed25519.sign_pipeline _ _ _ hpk
  refine WP.mono (wipe_ok hu) fun w ⟨hw, hfw⟩ => ⟨hw, ?_⟩
  have he := frame_bytes hfw L.OUT (by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hL.ko.sub_left (Offset.sub_base L.B (d := 16) (n := 192) (by decide))).symm)
    (by decide : 64 ≤ 2 ^ 64)
  exact he.trans hout

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Complete RFC 8032 signing, including all three SHA-512 computations. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem body_ok (v : Compress) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hlen : 64 + L.len.toNat < 2 ^ 64)
    (hpk : Spec.Ed25519.bytesAt m₀ L.pk 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32)) :
    WP isa (body fld fs v.callee v.suffix) t fun t' => Ctx L g mx m₀ t' ∧ Spec.Ed25519.bytesAt t'.mem L.out 64 =
      Spec.Ed25519.sign (Spec.Ed25519.bytesAt m₀ L.seed 32) (Spec.Ed25519.bytesAt m₀ L.msg L.len.toNat) := by
  apply WP.assoc
  refine WP.seq (WP.mono (secret_ok v hL hc) fun u ⟨hu, hs⟩ => ?_)
  apply WP.assoc
  apply WP.assoc
  refine WP.seq (WP.mono (WP.assoc' (nonce_ok v hL hu hs hlen)) fun w ⟨hw, hn⟩ => ?_)
  apply WP.assoc
  exact WP.seq (WP.mono (challenge_ok v hL hw hn hlen) fun z ⟨hz, hk⟩ => finish_ok hL hz hk hpk)

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Entry`. -/
section
/-! Entry contract and stack frame of complete cached-key signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64

/-- The disjoint scratch allocation leaves room for the hash's 64-byte prefix. -/
theorem Lay.Ok.message_bound {L : Lay} (h : L.Ok) : 64 + L.len.toNat < 2 ^ 64 := by
  have hd := h.sc L.MSG (by simp [Lay.inputs])
  have nm := h.nm
  have nc := h.nc
  by_cases hz : L.len.toNat = 0
  · omega
  by_cases hp : L.msg ≤ L.scr
  · have hn : ¬ L.MSG.Contains L.scr 1 := fun hx => hd _ hx (by simp [Region.Contains])
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp] at hn
    have hp' : L.msg.toNat ≤ L.scr.toNat := hp
    omega
  · have hp' : L.scr ≤ L.msg := by
      change L.scr.toNat ≤ L.msg.toNat
      change ¬ L.msg.toNat ≤ L.scr.toNat at hp
      omega
    have hn : ¬ L.SCR.Contains L.msg 1 := fun hx => hd _ (by simp [Region.Contains]; omega) hx
    simp only [Region.Contains, BitVec.toNat_sub_of_le hp'] at hn
    have hp'' : L.scr.toNat ≤ L.msg.toNat := hp'
    omega

def signLocal : Contract isa where
  pre s := 264 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] ∧
    s.wr = [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .r9, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .rdi, 64⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdi, 64⟩ ∧
    (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rsi, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp - BitVec.ofNat 64 264, 264⟩ ⟨s.gpr .r9, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsp, 8⟩ ⟨s.gpr .r9, 8192⟩ ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + 8192 ≤ 2 ^ 64 ∧
    Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 32)
  post s t := Spec.Ed25519.bytesAt t.mem (s.gpr .rdi) 64 = Spec.Ed25519.sign
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 32)
    (Spec.Ed25519.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9

def lay (s : State) : Lay :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, s.gpr .rsp - BitVec.ofNat 64 264⟩

theorem lay_ret (s : State) : (lay s).B + BitVec.ofNat 64 264 = s.gpr .rsp := BitVec.sub_add_cancel _ _

theorem lay_ok {s : State} (h : signLocal.pre s) : (lay s).Ok := by
  obtain ⟨-, -, -, os, op, om, oc, ko, ro, no, sc, pc, mc, ks, kp, km, rs, rp, rm, kc, rc, np, nm, ns, nc, -⟩ := h
  have e : (lay s).RET = ⟨s.gpr .rsp, 8⟩ := by simp only [Lay.RET, lay_ret]
  refine ⟨?_, oc, ko, e ▸ ro, no, ?_, ?_, ?_, kc, e ▸ rc, np, nm, ns, nc⟩
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact os
    · exact op
    · exact om
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sc
    · exact pc
    · exact mc
  · intro r hr
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ks
    · exact kp
    · exact km
  · intro r hr
    rw [e]
    simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact rs
    · exact rp
    · exact rm

theorem cached_key {s : State} (h : signLocal.pre s) :
    Spec.Ed25519.bytesAt s.mem (lay s).pk 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem (lay s).seed 32) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩
  exact hk

def pushRs : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9] ++ List.replicate 25 .rax

theorem push_base (sp : Addr) :
    sp - BitVec.ofNat 64 (8 * 31) = sp - BitVec.ofNat 64 264 + BitVec.ofNat 64 16 := by bv_omega

theorem push_slot (sp : Addr) (j : Nat) (hj : j < 6) :
    sp - BitVec.ofNat 64 (8 * (j + 1)) = sp - BitVec.ofNat 64 264 + BitVec.ofNat 64 (256 - 8 * j) := by
  have : 8 * (j + 1) < 2 ^ 64 := by omega
  bv_omega

theorem push_ctx {s : State} (h : signLocal.pre s) :
    Ctx (lay s) s.gpr s.mxcsr s.mem (pushed pushRs s) := by
  have hn : 8 * pushRs.length ≤ (s.gpr .rsp).toNat := by show 8 * 31 ≤ _; have := h.1; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s pushRs (by decide) hn
  have hw' : ∀ j (hj : j < 6), (pushed pushRs s).mem.readW
      ((lay s).B + BitVec.ofNat 64 (256 - 8 * j)) 64 = s.gpr (pushRs[j]'(by show j < 31; omega)) := fun j hj => by
    rw [← hw j (by show j < 31; omega)]; simp only [lay]; rw [push_slot _ j hj]; rfl
  refine ⟨by rw [pushed_rd, h.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr, by rw [pushed_mxcsr],
    hw' 5 (by omega), hw' 4 (by omega), hw' 3 (by omega), hw' 2 (by omega), hw' 1 (by omega), hw' 0 (by omega), ?_⟩
  · rw [pushed_wr, h.2.2.1]; simp only [show pushRs.length = 31 from rfl, lay]; rw [push_base]
  · rw [pushed_rsp]; simp only [show pushRs.length = 31 from rfl, lay]; rw [push_base]
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨(lay s).STK, by simp, ?_⟩
    simp only [show pushRs.length = 31 from rfl]
    rw [push_base]
    exact Offset.sub_base _ (by omega)

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.CT`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTAccess`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTFramework`. -/
section
/-! Relating complete signing runs with equal pointers and lengths; all input bytes remain secret. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (Within)

abbrev Two.Env := Lay × (Reg → BitVec 64) × (Reg → BitVec 64) × BitVec 32 × BitVec 32 × Mem × Mem

def Two (Φ : Lay → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Two.Env, e.1.Ok ∧
    Ctx e.1 e.2.1 e.2.2.2.1 e.2.2.2.2.2.1 a ∧ Ctx e.1 e.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.2 b ∧
    Φ e.1 e.2.2.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2.2.2 b

theorem two_wp {c : Prog isa} {Φ Ψ : Lay → Mem → State → Prop}
    (hct : RelCT isa (Two Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ mx₁ m₁ s₁ hL c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ mx₂ m₂ s₂ hL c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, mx₁, mx₂, m₁, m₂⟩, hL, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem two_block {is : List Instr} {Φ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true) :
    RelCT isa (Two Φ) (.block is) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ ⟨_, _, c₁, c₂, _, _⟩ =>
    Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact c₁.rsp.trans c₂.rsp.symm)) h

theorem two_blk {is : List Instr} {Φ Ψ : Lay → Mem → State → Prop}
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rsp]) (.block is) hc).isSome = true)
    (hw : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g mx m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two Φ) (.block is) (Two Ψ) := two_wp (two_block h) hw

structure Access (L : Lay) (rd wr : List Region) : Prop where
  sub : ∀ r ∈ rd ++ wr, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R
  wsub : ∀ r ∈ wr, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR

theorem covers {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) {rd wr : List Region} (ha : Access L rd wr) :
    Covers (rd ++ wr) (t.rd ++ t.wr) ∧ Covers wr t.wr := by
  constructor <;> apply Covers.of_sub <;> intro r hr
  · obtain ⟨R, hR, hs⟩ := ha.sub r hr
    exact ⟨R, by rw [hc.rd, hc.wr]; exact hR, hs⟩
  · rw [hc.wr]
    rcases ha.wsub r hr with h | h | h
    · obtain ⟨off, hb, hn⟩ := h
      exact ⟨L.FR, by simp, off, hb, Nat.le_trans hn (by show 192 ≤ 248; decide)⟩
    · exact ⟨L.OUT, by simp, h⟩
    · exact ⟨L.SCR, by simp, h⟩

theorem two_call {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, L.Ok →
      Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (ha : ∀ L, L.Ok → Access L (rd L) (wr L)) :
    RelCT isa (Two Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun _ _ ⟨⟨L, _⟩, hL, c₁, c₂, f₁, f₂⟩ =>
    ⟨rd L, wr L, rd L, wr L, hpre _ _ _ _ _ hL c₁ f₁, hpre _ _ _ _ _ hL c₂ f₂,
      hpub _ _ _ _ _ _ _ _ _ hL c₁ c₂ f₁ f₂,
      (covers c₁ (ha L hL)).1, (covers c₁ (ha L hL)).2, (covers c₂ (ha L hL)).1, (covers c₂ (ha L hL)).2,
      c₁.rsp.trans c₂.rsp.symm⟩

theorem two_callP {n : String} {c : Prog isa} {k : Contract isa} {Φ : Lay → Mem → State → Prop}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hd : c.depth ≤ 1) (rd wr : Lay → List Region)
    (hpre : ∀ (L : Lay) g mx m₀ (t : State), L.Ok → Ctx L g mx m₀ t → Φ L m₀ t →
      k.pre (t.callEntry.withRegions (rd L) (wr L)))
    (hpub : ∀ L t₁ t₂ g₁ g₂ mx₁ mx₂ m₁ m₂, L.Ok →
      Ctx L g₁ mx₁ m₁ t₁ → Ctx L g₂ mx₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ →
      k.pub (t₁.callEntry.withRegions (rd L) (wr L)) (t₂.callEntry.withRegions (rd L) (wr L)))
    (ha : ∀ L, L.Ok → Access L (rd L) (wr L)) :
    RelCT isa (Two Φ) (.call n c) (Two fun _ _ _ => True) :=
  two_wp (two_call hv hct rd wr hpre hpub ha) fun L _ _ _ _ hL hc hf =>
    call_ok hL hv hsp hd hc (hpre _ _ _ _ _ hL hc hf) (ha L hL).sub (ha L hL).wsub
      fun _ hc' _ _ _ => ⟨hc', trivial⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Memory coverage for modular constant-time calls in complete signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Proof.Ed25519.X86_64.PublicKey (within_base within_off add_add)

theorem init_access (L : Lay) (_hL : L.Ok) : Access L initRd (initWr L) := by
  constructor
  · intro r hr
    simp only [initRd, initWr, List.nil_append, List.mem_singleton] at hr; subst hr
    exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [initWr, List.mem_singleton] at hr; subst hr
    exact .inr (.inr (within_base _ (by omega)))

theorem upd_access (L : Lay) (p : Addr) (n : BitVec 64) (hi : Input L ⟨p, n.toNat⟩) :
    Access L [⟨p, n.toNat⟩] (updWr L) := by
  constructor
  · intro r hr
    simp only [updWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hi.cover
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [updWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inr (.inr (within_off _ (by omega)))

theorem fin_access (L : Lay) (_hL : L.Ok) : Access L [] (finWr L) := by
  constructor
  · intro r hr
    simp only [finWr, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · intro r hr
    simp only [finWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (within_base _ (by omega)))
    · exact .inl ⟨128, by rw [add_add], by show 128 + 64 ≤ 192; decide⟩
    · exact .inr (.inr (within_off _ (by omega)))

theorem reduce_access (out : Nat) (ho : out + 32 ≤ 128) (L : Lay) (_hL : L.Ok) :
    Access L (reduceRd L) (reduceWr L out) := by
  constructor
  · intro r hr
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, out, by rw [add_add], by change out + 32 ≤ 248; omega⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨out, by rw [add_add], by change out + 32 ≤ 192; omega⟩
    · exact .inr (.inr (within_base _ (by omega)))

theorem base_access (L : Lay) (_hL : L.Ok) : Access L (baseRd L) (baseWr L) := ⟨base_sub, base_wsub⟩

theorem mul_access (L : Lay) (_hL : L.Ok) : Access L (mulRd L) (mulWr L) := by
  constructor
  · intro r hr
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, 96, by rw [add_add], by show 96 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.OUT, by simp, within_off _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (within_off _ (by omega)))
    · exact .inr (.inr (within_base _ (by omega)))

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTHashes`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTHash`. -/
section
/-! SHA-512's trace depends only on the input pointers and length. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (gpr_ce rsp_ce nosp_init upd_verified upd_nosp upd_depth fin_verified fin_nosp fin_depth within_base)
open VG.Proof.Sha512.X86_64 (Compress)

theorem init_ct : RelCT isa (Two fun _ _ _ => True)
    (Impl.Ed25519.X86_64.callWith initArgs Spec.Sha512.init512Api.name
      (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512)) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block initArgs) (Two fun L _ => InitArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (initArgs_ok hc) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := Spec.Sha512.init512Api.name) (Φ := fun L _ => InitArgs L)
    (Proof.Sha512.X86_64.Stream.init_verified _).1 (Proof.Sha512.X86_64.Stream.init_verified _).2.1
    (nosp_init _) (by decide) (fun _ => initRd) initWr (fun _ _ _ _ _ hL hc ha => init_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ _ _ a₁ a₂ =>
      ((gpr_ce t₁ initRd (initWr L) (by decide)).trans a₁).trans
        ((gpr_ce t₂ initRd (initWr L) (by decide)).trans a₂).symm) init_access
  exact b.seq c

theorem upd_ct (v : Compress) (count : Lay → BitVec 64) (p : Lay → Addr) (n : Lay → BitVec 64)
    (hi : ∀ L, L.Ok → Input L ⟨p L, (n L).toNat⟩) :
    RelCT isa (Two fun L _ => UpdArgs L (count L) (p L) (n L))
      (.call (Spec.Sha512.updateApi.name ++ v.suffix) (Impl.Sha512.X86_64.Stream.update v.callee))
      (Two fun _ _ _ => True) := by
  exact two_callP (upd_verified v).1 (upd_verified v).2.1 (upd_nosp v) (upd_depth v)
    (fun L => [⟨p L, (n L).toNat⟩]) updWr
    (fun L _ _ _ _ hL hc ha => upd_pre hL hc ha (hi L hL))
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁', r₁⟩ := upd_regs a₁ [⟨p L, (n L).toNat⟩] (updWr L)
      obtain ⟨d₂, s₂, x₂, c₂', r₂⟩ := upd_regs a₂ [⟨p L, (n L).toNat⟩] (updWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        r₁.trans r₂.symm, by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp]⟩)
    (fun L hL => upd_access L (p L) (n L) (hi L hL))

theorem finalize_ct (v : Compress) (prefixLen : Nat) (hp : prefixLen < 2 ^ 31) (withMessage : Bool)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (finalizeArgs prefixLen withMessage)) hint).isSome = true) : RelCT isa (Two fun _ _ _ => True)
    (Impl.Ed25519.X86_64.callWith (finalizeArgs prefixLen withMessage) (Spec.Sha512.finalizeApi.name ++ v.suffix)
      (Impl.Sha512.X86_64.Stream.finalize v.callee)) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block (finalizeArgs prefixLen withMessage)) (Two fun L _ => FinArgs L (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen)) :=
    two_blk ht fun _ _ _ _ _ _ hc _ =>
      WP.mono (finalizeArgs_ok hc prefixLen hp withMessage) fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := Spec.Sha512.finalizeApi.name ++ v.suffix) (Φ := fun L _ => FinArgs L (if withMessage then L.len + BitVec.ofNat 64 prefixLen else BitVec.ofNat 64 prefixLen))
    (fin_verified v).1 (fin_verified v).2.1 (fin_nosp v) (fin_depth v) (fun _ => []) finWr
    (fun _ _ _ _ _ hL hc ha => fin_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, c₁'⟩ := fin_regs a₁ [] (finWr L)
      obtain ⟨d₂, s₂, x₂, c₂'⟩ := fin_regs a₂ [] (finWr L)
      exact ⟨d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm, c₁'.trans c₂'.symm,
        by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp]⟩) fin_access
  exact b.seq c

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! All three signing hashes leak only their pointers and lengths. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem input_ct (v : Compress) (source count : Nat) (hs : source + 8 ≤ 248) (hc : count < 2 ^ 32)
    (p : Lay → Addr) (hi : ∀ L, L.Ok → Input L ⟨p L, 32⟩)
    (hp : ∀ L g mx m (t : State), Ctx L g mx m t →
      t.mem.readW (L.B + BitVec.ofNat 64 (16 + source)) 64 = p L)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (inputArgs source count)) hint).isSome = true) :
    RelCT isa (Two fun _ _ _ => True) (update v.callee v.suffix (inputArgs source count))
      (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block (inputArgs source count))
      (Two fun L _ => UpdArgs L (BitVec.ofNat 64 count) (p L) 32) :=
    two_blk ht fun L g mx m t _ h _ => WP.mono (inputArgs_ok h source count hs hc (p L) (hp L g mx m t h))
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact b.seq (upd_ct v (fun _ => BitVec.ofNat 64 count) p (fun _ => 32) hi)

theorem message_ct (v : Compress) (count : Nat) (hc : count < 2 ^ 32)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (messageArgs count)) hint).isSome = true) :
    RelCT isa (Two fun _ _ _ => True) (update v.callee v.suffix (messageArgs count))
      (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block (messageArgs count))
      (Two fun L _ => UpdArgs L (BitVec.ofNat 64 count) L.msg L.len) :=
    two_blk ht fun _ _ _ _ _ _ h _ => WP.mono (messageArgs_ok h count hc)
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact b.seq (upd_ct v (fun _ => BitVec.ofNat 64 count) Lay.msg Lay.len
    (fun _ hL => (stable_input hL (by simp [Lay.inputs])).toInput))

theorem hashSeed_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (hashSeed v.callee v.suffix) (Two fun _ _ _ => True) :=
  init_ct.seq ((input_ct v fSeed 0 (by decide) (by decide) Lay.seed
    (fun _ hL => (stable_input hL (by simp [Lay.inputs])).toInput)
    (fun _ _ _ _ _ h => h.pSeed) (by taint_decide)).seq
    (finalize_ct v 32 (by decide) false (by taint_decide)))

theorem hashNonce_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (hashNonce v.callee v.suffix) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block prefixArgs)
      (Two fun L _ => UpdArgs L 0 (L.B + BitVec.ofNat 64 48) 32) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ h _ => WP.mono (prefixArgs_ok h)
      fun _ ⟨h', _, ha⟩ => ⟨h', ha⟩
  exact init_ct.seq ((b.seq (upd_ct v (fun _ => 0) (fun L => L.B + BitVec.ofNat 64 48) (fun _ => 32)
    (fun _ hL => (stable_prefix hL).toInput))).seq
    ((message_ct v 32 (by decide) (by taint_decide)).seq (finalize_ct v 32 (by decide) true (by taint_decide))))

theorem hashChallenge_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (hashChallenge v.callee v.suffix) (Two fun _ _ _ => True) :=
  init_ct.seq ((input_ct v fOut 0 (by decide) (by decide) Lay.out
    (fun _ hL => (stable_out hL).toInput) (fun _ _ _ _ _ h => h.pOut) (by taint_decide)).seq
    ((input_ct v fPublicKey 32 (by decide) (by decide) Lay.pk
      (fun _ hL => (stable_input hL (by simp [Lay.inputs])).toInput)
      (fun _ _ _ _ _ h => h.pPk) (by taint_decide)).seq
    ((message_ct v 64 (by decide) (by taint_decide)).seq (finalize_ct v 64 (by decide) true (by taint_decide)))))

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.CTCalls`. -/
section
/-! The signer's scalar and point operations keep all operand bytes secret. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (callWith scalarBaseName scalarBase_precomputed scalarReduce scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey (rsp_ce)

theorem reduce_ct (out : Nat) (ho : out + 32 ≤ 128)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (reduceArgs out)) hint).isSome = true) :
    RelCT isa (Two fun _ _ _ => True) (reduce out) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block (reduceArgs out)) (Two fun L _ => ReduceArgs L out) :=
    two_blk ht fun _ _ _ _ _ _ hc _ => WP.mono (reduceArgs_ok hc ho)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := "vg_ed25519_scalar_reduce") (Φ := fun L _ => ReduceArgs L out)
    scalarReduce_ok scalarReduce_ct (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)) (by lit_decide)
    reduceRd (fun L => reduceWr L out) (fun _ _ _ _ _ hL hc ha => reduce_pre hL hc ha ho)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := reduce_regs a₁ (reduceRd L) (reduceWr L out)
      obtain ⟨d₂, s₂, x₂⟩ := reduce_regs a₂ (reduceRd L) (reduceWr L out)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    (reduce_access out ho)
  exact b.seq c

theorem base_ct : RelCT isa (Two fun _ _ _ => True)
    (callWith baseArgs (scalarBaseName fs) (scalarBase_precomputed fld)) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block baseArgs) (Two fun L _ => BaseArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ => WP.mono (baseArgs_ok hc)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := (scalarBaseName fs)) (Φ := fun L _ => BaseArgs L)
    (scalarBase_precomputed_ok (fld := fld)) (scalarBase_precomputed_ct (fld := fld)) base_nosp base_depth
    baseRd baseWr
    (fun _ _ _ _ _ hL hc ha => base_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁⟩ := base_regs a₁ (baseRd L) (baseWr L)
      obtain ⟨d₂, s₂, x₂⟩ := base_regs a₂ (baseRd L) (baseWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm, x₁.trans x₂.symm⟩)
    base_access
  exact b.seq c

theorem mul_ct : RelCT isa (Two fun _ _ _ => True)
    (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) (Two fun _ _ _ => True) := by
  have b : RelCT isa (Two fun _ _ _ => True) (.block mulAddArgs) (Two fun L _ => MulArgs L) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ => WP.mono (mulArgs_ok hc)
      fun _ ⟨hc', _, ha⟩ => ⟨hc', ha⟩
  have c := two_callP (n := "vg_ed25519_scalar_mul_add") (Φ := fun L _ => MulArgs L)
    scalarMulAdd_ok scalarMulAdd_ct (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)) (by lit_decide)
    mulRd mulWr (fun _ _ _ _ _ hL hc ha => mul_pre hL hc ha)
    (fun L t₁ t₂ _ _ _ _ _ _ _ c₁ c₂ a₁ a₂ => by
      obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := mul_regs a₁ (mulRd L) (mulWr L)
      obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := mul_regs a₂ (mulRd L) (mulWr L)
      exact ⟨by rw [rsp_ce, rsp_ce, c₁.rsp, c₂.rsp], d₁.trans d₂.symm, s₁.trans s₂.symm,
        x₁.trans x₂.symm, k₁.trans k₂.symm, r₁.trans r₂.symm⟩) mul_access
  exact b.seq c

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Correct`. -/
section
/-! Complete signing meets its functional contract and preserves the ABI. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)
open VG.Proof.Ed25519.X86_64.PublicKey (add_add ne_cs)

theorem sign_ok (v : Compress) {s : State} (h : signLocal.pre s) :
    WP isa (code fld fs v.callee v.suffix) s fun s' => abiPreserved s s' ∧ signLocal.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide) (by show 8 * 31 ≤ _; have := h.1; omega)
    (WP.mono (body_ok v hL hc hL.message_bound (cached_key h))
      fun u ⟨hu, ho⟩ => ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rax pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, show pushRs.length = 31 from rfl, add_add, lay_ret]
    refine ⟨fun r hr => ?_, ?_, by rw [popped_mxcsr, hu.mx]⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
      · rw [Lay.RET, lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base _ (by omega) (by omega)
  · show Spec.Ed25519.bytesAt (popped .rax pushRs.length u).mem (lay s).out 64 = _
    rw [popped_mem, ho]
    rfl

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Complete signing is constant-time with respect to seed, key and message bytes. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem body_ct (v : Compress) : RelCT isa (Two fun _ _ _ => True)
    (body fld fs v.callee v.suffix) (Two fun _ _ _ => True) := by
  have s : RelCT isa (Two fun _ _ _ => True) (.block saveSecret) (Two fun _ _ _ => True) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (saveSecret_ok hc rfl) fun _ ⟨hc', _, _⟩ => ⟨hc', trivial⟩
  have w : RelCT isa (Two fun _ _ _ => True) (.block wipe) (Two fun _ _ _ => True) :=
    two_blk (by taint_decide) fun _ _ _ _ _ _ hc _ =>
      WP.mono (wipe_ok hc) fun _ ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact (hashSeed_ct v).seq (s.seq ((hashNonce_ct v).seq ((reduce_ct 64 (by decide) (by taint_decide)).seq
    (base_ct.seq ((hashChallenge_ct v).seq ((reduce_ct 96 (by decide) (by taint_decide)).seq (mul_ct.seq w)))))))

theorem sign_ct (v : Compress) : ConstantTime isa signLocal.pre signLocal.pub (code fld fs v.callee v.suffix) := by
  refine RelCT.constantTime (RelCT.frame (fun _ _ h => h.2.2.1)
    (RelCT.mono (body_ct v) ?_ fun _ _ _ => trivial))
  rintro _ _ ⟨s₁, s₂, ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, h9⟩, rfl, rfl⟩
  have e : lay s₂ = lay s₁ := by simp only [lay, hsp, hdi, hsi, hdx, hcx, h8, h9]
  exact ⟨⟨lay s₁, s₁.gpr, s₂.gpr, s₁.mxcsr, s₂.mxcsr, s₁.mem, s₂.mem⟩, lay_ok h₁,
    push_ctx h₁, e ▸ push_ctx h₂, trivial, trivial⟩

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Merged from `Proof.Ed25519.X86_64.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed25519.bytesAt satMem 0x2000 32 = satSeed := by
  unfold satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt satMem 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000
    | .r8 => 0 | .r9 => 0x5000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract X86_64.abi 264).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, satState]
    sig_and_intros
    · decide +kernel
    · rw [sat_seed, sat_key]
      rfl

end VG.Proof.Ed25519.X86_64.SignCached
end

/-! Complete signing satisfies the reviewed cached-key signing contract. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce scalarBase_precomputed scalarMulAdd callWith)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem implies : signLocal.Implies (Spec.Ed25519.signCachedContract X86_64.abi 264) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, signLocal]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, signLocal]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, signLocal]
  sat := sat

theorem verified (v : Compress) : Verified X86_64.target (code fld fs v.callee v.suffix)
    (Spec.Ed25519.signCachedContract X86_64.abi 264) :=
  Verified.of_correct (fun _ h => sign_ok v h) (sign_ct v) implies

theorem spSafe (v : Compress) : (code fld fs v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  have hu := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe
  have hf := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe
  have hr : scalarReduce.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
  have hb : (scalarBase_precomputed fld).all (fun i => !isa.writesSp i) = true :=
    PublicKey.base_spSafe
  have hm : scalarMulAdd.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
  have hi : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !isa.writesSp i) = true := by
    decide +kernel
  simp only [code, body, hashSeed, hashNonce, hashChallenge, init, update, finalize, reduce, callWith,
    Code.all, hu, hf, hr, hb, hm, hi, Bool.and_true]
  decide

end VG.Proof.Ed25519.X86_64.SignCached
