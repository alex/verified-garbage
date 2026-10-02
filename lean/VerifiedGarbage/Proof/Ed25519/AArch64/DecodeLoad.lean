import VerifiedGarbage.Proof.Ed25519.AArch64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.AArch64.CanonicalY


/-! Point decoding loads all bytes before changing its workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

structure DecodeKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem DecodeKeep.trans {base : Addr} {s t u : State}
    (h : DecodeKeep base s t) (k : DecodeKeep base t u) : DecodeKeep base s u :=
  ⟨fun r hr hb hi => (k.gpr r hr hb hi).trans (h.gpr r hr hb hi), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem DecodeKeep.scratch {base : Addr} {s t : State} (h : DecodeKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem DecodeKeep.of_counter {base : Addr} {s t : State} (h : CounterKeep base s t) : DecodeKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.sp, h.mem⟩

theorem DecodeKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob ∨ r = .x19 ∨ r = .x1) : DecodeKeep base s t := by
  refine ⟨fun r hr hb hi => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hr h
    · exact hb h
    · exact hi h
  · rw [h.mem]; exact Outside.refl _ _ _ _

theorem pointDecodeLoad_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block pointDecodeLoad) s fun t => DecodeKeep base s t ∧
      t.gpr .x1 = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      env t.mem base 1 = Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) ∧
      (t.gpr .x8 == 0) = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P) := by
  rw [pointDecodeLoad, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadSign_ok s p hp (hr 24 (by decide))) fun a ⟨asign, ka⟩ => ?_
  have kar : DecodeKeep base s a := DecodeKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok a p ((ka.gpr _ (by decide)).trans hp)
    (by intro d hd; rw [ka.rd, ka.wr]; exact hr d hd)) fun b ⟨byval, kb⟩ => ?_
  rw [ka.mem] at byval
  have kab := kar.trans (DecodeKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok (kab.scratch hs) (slot_range 1)) fun c hc => ?_
  subst c
  have cmem := st4_outside b.mem base (show offset 1 + 32 < 2 ^ 64 by decide)
    (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)
  have kc : DecodeKeep base b { b with mem := (st4 b.mem base (offset 1) (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)) } :=
    ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, cmem.mono (by decide) (by decide)⟩
  have cy : env (st4 b.mem base (offset 1) (b.gpr .x4) (b.gpr .x5) (b.gpr .x6) (b.gpr .x7)) base 1 =
      Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) := by
    change Proof.X25519.toFe (fe _ base (offset 1)) = _
    rw [fe_st4 _ _ (by decide), byval]
  refine WP.mono (canonicalY_ok _ _ (Nat.mod_lt _ (by decide)) byval) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kab.trans kc).trans (DecodeKeep.of_keeps kt (by decide)), ?_, ?_, tz⟩
  · rw [kt.gpr .x1 (by decide), kb.gpr .x1 (by decide)]; exact asign
  · rw [kt.mem]; exact cy

end VG.Proof.Ed25519.AArch64
