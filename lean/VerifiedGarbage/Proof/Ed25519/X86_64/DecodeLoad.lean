import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.CanonicalY
import VerifiedGarbage.Proof.Ed25519.X86_64.StoreWords

/-! Untrusted: point decoding loads all bytes before changing its workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps Outside clob F st4_outside fe_st4 val4)

structure DecodeKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem DecodeKeep.trans {base : Addr} {s t u : State}
    (h : DecodeKeep base s t) (k : DecodeKeep base t u) : DecodeKeep base s u :=
  ⟨fun r hr hb hi => (k.gpr r hr hb hi).trans (h.gpr r hr hb hi), k.rd.trans h.rd,
    k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem DecodeKeep.scratch {base : Addr} {s t : State} (h : DecodeKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem DecodeKeep.of_rbx {base : Addr} {s t : State} (h : RbxKeep base s t) : DecodeKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.mem⟩

theorem DecodeKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hrs : ∀ r ∈ rs, r ∈ clob ∨ r = .rbx ∨ r = .rsi) : DecodeKeep base s t := by
  refine ⟨fun r hr hb hi => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, ?_⟩
  · rcases hrs r hm with h | h | h
    · exact hr h
    · exact hb h
    · exact hi h
  · rw [h.2.1]; exact Outside.refl _ _ _ _

theorem pointDecodeLoad_ok {s : State} {base p : Addr} (hs : Scratch s base) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block pointDecodeLoad) s fun t => DecodeKeep base s t ∧
      t.gpr .rsi = signWord (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) / 2 ^ 255 == 1) ∧
      env t.mem base 1 = Proof.X25519.toFe (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) ∧
      t.zf = some (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P)) := by
  rw [pointDecodeLoad, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadSign_ok s p hp (hr 24 (by decide))) fun a ⟨asign, ka⟩ => ?_
  have kar : DecodeKeep base s a := DecodeKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loadY_ok a p ((ka.1 _ (by decide)).trans hp)
    (by intro d hd; rw [ka.2.2.1, ka.2.2.2]; exact hr d hd)) fun b ⟨byval, kb⟩ => ?_
  rw [ka.2.1] at byval
  have kab := kar.trans (DecodeKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (storeWordsWide_ok (kab.scratch hs) 1) fun c ⟨cm, cg, cr, cw⟩ => ?_
  have cmem : Outside base (offset 1) 32 b.mem c.mem := by
    rw [cm]; exact st4_outside _ _ (by decide) _ _ _ _
  have kc : DecodeKeep base b c := ⟨fun r _ _ _ => cg r, cr, cw, cmem.mono (by decide) (by decide)⟩
  have cy : env c.mem base 1 = Proof.X25519.toFe
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255) := by
    change F c.mem base (offset 1) = _
    rw [F, cm, fe_st4 _ _ (by decide), byval]
  have cv : val4 (c.gpr .r8) (c.gpr .r9) (c.gpr .r10) (c.gpr .r11) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 := by
    rw [val4, cg .r8, cg .r9, cg .r10, cg .r11]; exact byval
  refine WP.mono (canonicalY_ok c _ (Nat.mod_lt _ (by decide)) cv) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kab.trans kc).trans (DecodeKeep.of_keeps kt (by decide)), ?_, ?_, tz⟩
  · rw [kt.1 .rsi (by decide), cg .rsi, kb.1 .rsi (by decide)]; exact asign
  · rw [kt.2.1]; exact cy

end VG.Proof.Ed25519.X86_64
