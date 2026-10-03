import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverParity
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldWide
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverPoint

/-! Merged from `Proof.Ed25519.X86_64.DecodeLoad`. -/
section
/-! Merged from `Proof.Ed25519.X86_64.CanonicalY`. -/
section
/-! Canonical decoding checks y before reduction modulo p. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (low63)
open VG.Proof.X25519.X86_64 (val4 Keeps freezeB freezeB_ok mask)

theorem setLow63_ok (s : State) :
    WP isa (.block [.movImm64 .rdx low63]) s fun t => t.gpr .rdx = low63 ∧ Keeps [.rdx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem canonicalMask_ok {s : State} (n : Nat)
    (hm : s.gpr .rcx = mask (decide (Spec.X25519.P ≤ n))) :
    WP isa (.block [.alu .test .rcx (.reg .rcx)]) s fun t =>
      t.zf = some (decide (n < Spec.X25519.P)) ∧ Keeps [] s t := by
  have hz : (mask (decide (Spec.X25519.P ≤ n)) == 0#64) = decide (n < Spec.X25519.P) := by
    by_cases h : Spec.X25519.P ≤ n
    · rw [decide_eq_true h, decide_eq_false (by omega : ¬ n < Spec.X25519.P)]; rfl
    · rw [decide_eq_false h, decide_eq_true (by omega : n < Spec.X25519.P)]; rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hm]
  exact ⟨hz, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem canonicalY_ok (s : State) (n : Nat) (hn : n < 2 ^ 255)
    (hv : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = n) :
    WP isa (.block canonicalY) s fun t => t.zf = some (decide (n < Spec.X25519.P)) ∧
      Keeps [.rdx, .r12, .r13, .r14, .r15, .rax, .rcx] s t := by
  change WP isa (.block (([.movImm64 .rdx low63] : List Instr) ++ freezeB ++
    [.alu .test .rcx (.reg .rcx)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setLow63_ok s) fun a ⟨ad, ka⟩ => ?_
  have av : val4 (a.gpr .r8) (a.gpr .r9) (a.gpr .r10) (a.gpr .r11) = n := by
    rw [val4, ka.1 .r8 (by decide), ka.1 .r9 (by decide), ka.1 .r10 (by decide), ka.1 .r11 (by decide)]
    exact hv
  rw [WP.block_append_iff]
  refine WP.mono (freezeB_ok a (by rw [av]; omega) ad) fun b ⟨bc, _, kb⟩ => ?_
  rw [av] at bc
  refine WP.mono (canonicalMask_ok n bc) fun t ⟨tz, kt⟩ => ?_
  exact ⟨tz, (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩

end VG.Proof.Ed25519.X86_64
end

/-! Merged from `Proof.Ed25519.X86_64.StoreWords`. -/
section
/-! Save four words in an Ed25519 field slot. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Scr st4)

theorem storeWordsWide_ok {s : State} {base : Addr} (hs : Scratch s base) (o : Slot) :
    WP isa (.block (Impl.X25519.X86_64.store4 (offset o))) s fun t =>
      t.mem = st4 s.mem base (offset o) (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hn : Scr narrow base := ⟨hs.rdi, List.mem_singleton_self _, by have := hs.nowrap; omega⟩
  obtain ⟨tr, t, he, hm, hg, _, _⟩ := Proof.X25519.X86_64.store4_ok hn (o := offset o)
    (by simp only [offset]; omega)
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hs.wr, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hm, hg, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64
end

/-! Point decoding loads all bytes before changing its workspace. -/

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
end

/-! Canonical bytes decode exactly as the merged Ed25519 specification. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off)

variable {fld : Arith} [EdArith fld]

theorem pointDecode_ok {s : State} {base p : Addr} (hs : Scratch s base) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (pointDecode fld) s fun t => DecodeKeep base s t ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem p 32)) t := by
  have hl : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  rw [pointDecode]
  refine WP.seq (WP.mono (pointDecodeLoad_ok hs hp hr) fun a ⟨ka, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p 32) % 2 ^ 255 < Spec.X25519.P))
    (by exact az)
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ka.scratch hs) _ asign) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_rbx kt), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨ka.trans (DecodeKeep.of_rbx (RbxKeep.of_keep kt)), ?_⟩
    rw [decodePoint32 _ hl, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.X86_64
