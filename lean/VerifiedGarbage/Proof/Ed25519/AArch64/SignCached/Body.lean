import VerifiedGarbage.Impl.Ed25519.AArch64.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Preserve
import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe

/-! Merged from `Proof.Ed25519.AArch64.SignCached.Secret`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.SignCached.Prefix`. -/
section
namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

structure PrefixStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : t.v = s.v
  regs : ∀ r, r ≠ .x0 → r ≠ .x15 → t.gpr r = s.gpr r

theorem PrefixStep.trans {s t u : State} (h : PrefixStep s t) (h' : PrefixStep t u) : PrefixStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.vec.trans h.vec,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem copyWord_ok {s : State} {E : Addr} (he : s.sp = E)
    (hr : (⟨E, 256⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 4) :
    WP isa (.block (copyWord k)) s fun t => PrefixStep s t ∧
      t.mem = s.mem.writeW (E + BitVec.ofNat 64 (64 + 8 * k))
        (s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * k)) 64) := by
  have source : InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (224 + 8 * k)) 8 :=
    ⟨⟨E, 256⟩, List.mem_append_right _ hr, Offset.contains_base E (by omega) (by omega)⟩
  have dest : InRegions s.wr (E + BitVec.ofNat 64 (64 + 8 * k)) 8 :=
    ⟨⟨E, 256⟩, hr, Offset.contains_base E (by omega) (by omega)⟩
  have hl : exec (.ldrSp .x0 (224 + 8 * k)) s =
      some (s.write .x .x0 (s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * k)) 64)) := by
    simp only [exec, show (224 + 8 * k) % 8 = 0 ∧ 224 + 8 * k < 32768 from by omega,
      and_self, ite_true, State.load, he, source, Option.map_some, Mem.readW, BitVec.setWidth_eq]
  have ha {t : State} : exec (.addSp .x15 64) t = some (t.write .x .x15 (t.sp + BitVec.ofNat 64 64)) := by
    simp only [exec, show 64 < 4096 from by decide, ite_true]
  apply WP.of_runBlock
  simp only [copyWord, runBlock_cons, runStep_some, hl, ha, RegUpd.sp_write]
  rw [exec_str_x ⟨by omega, by omega⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write_self, BitVec.setWidth_eq, he, Offset.add_add] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h15
    simp only [RegUpd.gpr_write, h0, h15, ite_false]
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      BitVec.setWidth_eq, he, Offset.add_add]

structure PrefixInv (E : Addr) (s : State) (n : Nat) (t : State) : Prop where
  step : PrefixStep s t
  frame : Frame [⟨E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (E + BitVec.ofNat 64 (64 + 8 * j)) 64 =
    s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * j)) 64

theorem copyPrefix_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap copyWord)) s (PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyPrefix_ok he hw n (by omega)) fun u hu => ?_
    refine WP.mono (copyWord_ok (hu.step.sp.trans he) (hu.step.wr ▸ hw) (by omega : n < 4))
      fun t ⟨kt, mt⟩ => ?_
    have same : u.mem.readW (E + BitVec.ofNat 64 (224 + 8 * n)) 64 =
        s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * n)) 64 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega) (by omega) (by decide)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (a := E + BitVec.ofNat 64 (64 + 8 * j))
          (b := E + BitVec.ofNat 64 (64 + 8 * n)) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem prefix_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => PrefixStep s t ∧
      Frame [⟨E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (E + 64) 32 = Spec.Ed25519.bytesAt s.mem (E + 224) 32 := by
  refine WP.mono (copyPrefix_ok he hw 4 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  rw [Proof.Ed25519.bytesAt_encodeLE t.mem, Proof.Ed25519.bytesAt_encodeLE s.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (off E 64) 32) =
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off E 224) 32)
  rw [decodeLE_words, decodeLE_words]
  simp only [fe, word]
  rw [ht.words 0 (by decide), ht.words 1 (by decide), ht.words 2 (by decide), ht.words 3 (by decide)]

end VG.Proof.Ed25519.AArch64.SignCached
end

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
end

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

structure NonceReady (L : Lay) (m : Mem) (t : State) : Prop where
  scalar : Spec.Ed25519.bytesAt t.mem (L.E + 32) 32 = scalar L m
  nonce : Spec.Ed25519.bytesAt t.mem (L.E + 96) 32 = nonce L m
  point : Spec.Ed25519.bytesAt t.mem (L.out) 32 = Spec.Ed25519.scalarBase (SignCached.nonce L m)

theorem nonce_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : SecretReady L m₀ s) :
    WP isa (nonceCode b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧ NonceReady L m₀ t := by
  refine WP.seq (WP.mono (hashNonce_ok b hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.prefixBytes] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide)).trans hs.scalar
  refine WP.seq (WP.mono (reduce_step hu hL ha 96 (by decide)) fun v ⟨hv, fv, nv⟩ => ?_)
  rw [du] at nv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide)).trans su
  refine WP.mono (base_step hv hL ha) fun t ⟨ht, ft, pt⟩ => ⟨ht, ?_, ?_, ?_⟩
  · exact (base_field_bytes hL ft (d := 32) (by decide)).trans sv
  · exact (base_field_bytes hL ft (d := 96) (by decide)).trans nv
  · change Spec.Ed25519.bytesAt v.mem (L.E + 96) 32 = _ at nv
    rw [nv] at pt
    exact pt

theorem challenge_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) (hs : NonceReady L m₀ s)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed) 32)) :
    WP isa (challengeCode b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (hashChallenge_ok b hc hL ha) fun u ⟨hu, fu, du⟩ => ?_)
  rw [hs.point] at du
  have su := (hash_field_bytes hL fu (d := 32) (by decide)).trans hs.scalar
  have nu := (hash_field_bytes hL fu (d := 96) (by decide)).trans hs.nonce
  have pu := (hash_out_bytes hL fu).trans hs.point
  refine WP.seq (WP.mono (reduce_step hu hL ha 128 (by decide)) fun v ⟨hv, fv, cv⟩ => ?_)
  rw [du] at cv
  have sv := (reduce_field_bytes hL fv (d := 32) (by decide) (by decide) (by decide)).trans su
  have nv := (reduce_field_bytes hL fv (d := 96) (by decide) (by decide) (by decide)).trans nu
  have pv := (reduce_out_bytes hL fv (by decide)).trans pu
  refine WP.mono (mul_step hv hL ha) fun t ⟨ht, ft, st⟩ => ⟨ht, ?_⟩
  change Spec.Ed25519.bytesAt v.mem (L.E + 96) 32 = _ at nv
  change Spec.Ed25519.bytesAt v.mem (L.E + 128) 32 = _ at cv
  change Spec.Ed25519.bytesAt v.mem (L.E + 32) 32 = _ at sv
  rw [nv, cv, sv] at st
  have pt := (mul_out_bytes hL ft).trans pv
  rw [Proof.Ed25519.signatureBytes_split, pt]
  change Spec.Ed25519.scalarBase (nonce L m₀) ++ Spec.Ed25519.bytesAt t.mem (L.out + (32 : BitVec 64)) 32 = _
  rw [st]
  exact Proof.Ed25519.sign_pipeline _ _ _ hk

theorem wipe_ok (hc : Ctx L g vec m₀ s) (hL : L.Ok) :
    WP isa (.block wipe) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.bytesAt s.mem (L.out) 64 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (start := 4) (count := 28) (by decide))
    fun t ⟨ht, hf, _⟩ => ⟨ht, ?_⟩
  refine frame_bytes hf L.OUT ?_ (by change 64 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 4 + 8 * 28 ≤ 256))).symm

theorem body_ok (b : Backend) (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (hk : Spec.Ed25519.bytesAt m₀ (L.pk) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (L.seed) 32)) :
    WP isa (body b.code b.suffix) s fun t => Ctx L g vec m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.out) 64 = Spec.Ed25519.sign
        (Spec.Ed25519.bytesAt m₀ (L.seed) 32)
        (Spec.Ed25519.bytesAt m₀ (L.msg) L.len.toNat) := by
  refine WP.seq (WP.mono (secret_ok b hc hL ha) fun u ⟨hu, su⟩ => ?_)
  refine WP.seq (WP.mono (nonce_ok b hu hL ha su) fun v ⟨hv, nv⟩ => ?_)
  refine WP.seq (WP.mono (challenge_ok b hv hL ha nv hk) fun w ⟨hw, sw⟩ => ?_)
  exact WP.mono (wipe_ok hw hL) fun t ⟨ht, same⟩ => ⟨ht, same.trans sw⟩

end VG.Proof.Ed25519.AArch64.SignCached
