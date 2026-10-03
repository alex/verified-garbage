import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyContext
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCTBody
import VerifiedGarbage.Proof.Framework.Contract

/-! Merged from `Proof.Ed25519.AArch64.VerifyLit`. -/
section
/-! A checked literal for the complete verification program. -/

namespace VG

materialize_code Impl.Ed25519.AArch64.verifyEquation

end VG
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyMain`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifySetup`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyBody`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyDecodeR`. -/
section
/-! Reject an invalid R encoding or evaluate the complete equation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

def equationWithR (r : Option Spec.Ed25519.Point) (a : Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match r with
  | none => false
  | some r => Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul challenge a))

theorem verifyDecodeR_ok {s : State} {base pk sig challenge : Addr}
    {Aa : EPoint dZ} (h : VerifyContext s base pk sig challenge)
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa verifyDecodeR s fun t => VerifyKeep base s t ∧
      t.gpr .x8 = signWord (equationWithR
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (tablePoint s.mem base 7424)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeR]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .x2 7944 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  apply WP.seq
  have hd := pointDecode_ok (base := base) (p := sig) ha.scratch (ap.trans h.sigHeader) ha.rRead
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem sig 32) = decoded at hd
  rw [ka.mem] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  have kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  have kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c r kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, equationWithR, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    have kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7552 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    have kabcd := kabc.trans (kd.mono (by decide) (by decide))
    have hd := h.of_keep kabcd
    have da : tablePoint d.mem base 7424 = tablePoint s.mem base 7424 := by
      rw [kd.mem.point (by decide) (Or.inl (by decide)) (by decide), kc.mem,
        workspace_tablePoint kb.mem (by decide) (by decide), ka.mem]
    obtain ⟨Ra, hRa⟩ := decodePoint_rep (hp.trans hy)
    refine WP.mono (verifyEquationPoints_ok hd.scratch hd.sigHeader hd.challengeHeader
      hd.scalarBytes hd.scalarFar hd.challengeRead hd.challengeFar (by rw [da]; exact hA)
      (by rw [dp, cp]; exact hRa)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, da, verifyKeep_bytes kabcd h.scalarFar, verifyKeep_bytes kabcd h.challengeFar,
      hp, hy, equationWithR]

end VG.Proof.Ed25519.AArch64
end

/-! Reject an invalid public key encoding before computing the equation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

def decodedEquation (a r : Option Spec.Ed25519.Point) (scalar challenge : Nat) : Bool :=
  match a with
  | none => false
  | some a => equationWithR r a scalar challenge

theorem verifyDecodeA_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa verifyDecodeA s fun t => VerifyKeep base s t ∧
      t.gpr .x8 = signWord (decodedEquation
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))) := by
  rw [verifyDecodeA]
  refine WP.seq (WP.mono (loadPointer_ok h.scratch .x2 7936 (by decide) (by decide)) fun a ⟨ap, ka⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keeps ka (by decide)
  have ha := h.of_keep kap
  apply WP.seq
  have hd := pointDecode_ok (base := base) (p := pk) ha.scratch (ap.trans h.pkHeader) ha.pkRead
  generalize hp : Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt a.mem pk 32) = decoded at hd
  rw [ka.mem] at hp
  with_reducible apply WP.mono hd
  intro b hb
  have kb := hb.1
  have br := hb.2
  have kbp : VerifyKeep base a b := PowersKeep.of_decode kb
  have kab := kap.trans kbp
  refine decodedThen_ok br (fun c kc hn => ?_) (fun c p kc hy cp => ?_)
  · refine WP.mono (recoverInvalid_ok c base) fun t ⟨kt, tr⟩ => ?_
    refine ⟨(kab.trans (PowersKeep.of_keeps kc (by decide))).trans (PowersKeep.of_keep kt), ?_⟩
    simpa only [hp, hn, decodedEquation, signWord, Bool.false_eq_true, ite_false, DecodeResult] using tr
  · have kcp : VerifyKeep base b c := PowersKeep.of_keeps kc (by decide)
    have kabc := kab.trans kcp
    refine WP.seq (WP.mono (pointTableWrite_ok (kabc.scratch h.scratch) 7424 (by decide) (by decide))
      fun d ⟨kd, dp, _⟩ => ?_)
    have kabcd := kabc.trans (kd.mono (by decide) (by decide))
    obtain ⟨Aa, hAa⟩ := decodePoint_rep (hp.trans hy)
    refine WP.mono (verifyDecodeR_ok (h.of_keep kabcd) (by rw [dp, cp]; exact hAa))
      fun t ⟨kt, tv⟩ => ?_
    refine ⟨kabcd.trans kt, ?_⟩
    rw [tv, dp, cp, verifyKeep_bytes kabcd h.rFar, verifyKeep_bytes kabcd h.scalarFar,
      verifyKeep_bytes kabcd h.challengeFar, hp, hy, decodedEquation]

end VG.Proof.Ed25519.AArch64
end

/-! The strict scalar check and decoding branches implement verifyEquation. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

private theorem decodedEquation_order (a r : Option Spec.Ed25519.Point) (s k : Nat) :
    (match a, r with
      | some a, some r => decide (s < Spec.Ed25519.L) &&
          Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint)
            (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul k a))
      | _, _ => false) = (decide (s < Spec.Ed25519.L) && decodedEquation a r s k) := by
  cases a <;> cases r <;> simp only [decodedEquation, equationWithR, Bool.and_false]

private theorem verifyEquation_order (pk sig challenge : List Byte)
    (hp : pk.length = 32) (hs : sig.length = 64) (hc : challenge.length = 64) :
    Spec.Ed25519.verifyEquation pk sig challenge =
      (decide (Spec.Ed25519.decodeLE (sig.drop 32) < Spec.Ed25519.L) &&
        decodedEquation (Spec.Ed25519.decodePoint pk) (Spec.Ed25519.decodePoint (sig.take 32))
          (Spec.Ed25519.decodeLE (sig.drop 32)) (Spec.Ed25519.decodeLE challenge)) := by
  rw [Spec.Ed25519.verifyEquation, hp, hs, hc]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false]
  exact decodedEquation_order _ _ _ _

theorem verifyEquation_bytes (m : Mem) (pk sig challenge : Addr) :
    Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt m pk 32)
      (Spec.Ed25519.bytesAt m sig 64) (Spec.Ed25519.bytesAt m challenge 64) =
    (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32) < Spec.Ed25519.L) &&
      decodedEquation (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m pk 32))
        (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m sig 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (off sig 32) 32))
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m challenge 64))) := by
  rw [verifyEquation_order _ _ _ (bytesAt_length ..) (bytesAt_length ..) (bytesAt_length ..),
    signatureBytes_take, signatureBytes_drop]

theorem verifyBody_ok {s : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) :
    WP isa (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid)) s fun t =>
      VerifyKeep base s t ∧ t.gpr .x8 = signWord
        (Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem pk 32)
          (Spec.Ed25519.bytesAt s.mem sig 64) (Spec.Ed25519.bytesAt s.mem challenge 64)) := by
  refine WP.seq (WP.mono (verifyScalar_ok h.scratch h.sigHeader h.scalarRead) fun a ⟨ka, am, ac⟩ => ?_)
  have kap : VerifyKeep base s a := PowersKeep.of_keep ka
  apply WP.ite _ (congrArg some ac)
  · intro ht
    refine WP.mono (verifyDecodeA_ok (h.of_keep kap)) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans kt, ?_⟩
    rw [am] at tv
    rw [verifyEquation_bytes, ht, Bool.true_and]
    exact tv
  · intro hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨kt, tv⟩ => ?_
    refine ⟨kap.trans (PowersKeep.of_keep kt), ?_⟩
    rw [verifyEquation_bytes, hf, Bool.false_and]
    exact tv

end VG.Proof.Ed25519.AArch64
end

/-! Save the ABI registers and retain the three public input pointers. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem verifyPrepare_ok (s : State) :
    WP isa (.block [mov .x8 .x2, mov .x2 .x3]) s fun t =>
      t.gpr .x8 = s.gpr .x2 ∧ t.gpr .x2 = s.gpr .x3 ∧ Keeps [.x8, .x2] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem verifyHeaders_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block verifyHeaders) s fun t =>
      t.gpr .x0 = base ∧ (∀ r, r ≠ .x0 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Outside base 7936 24 s.mem t.mem ∧
      t.mem.readW (off base 7936) 64 = s.gpr .x0 ∧
      t.mem.readW (off base 7944) 64 = s.gpr .x1 ∧
      t.mem.readW (off base 7952) 64 = s.gpr .x8 := by
  have hw' (d : Nat) (hd : d + 8 ≤ 8192) : InRegions s.wr (off base d) 8 :=
    ⟨_, hw, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [verifyHeaders, mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.store, addr, Size.bytes, hb, hw' 7936 (by decide), hw' 7944 (by decide), hw' 7952 (by decide),
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, BitVec.setWidth_eq,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.mem_write]
    exact (((Outside.refl base 7936 24 s.mem).writeW (by decide) (by decide) (by decide) _).writeW
      (by decide) (by decide) (by decide) _).writeW (by decide) (by decide) (by decide) _
  all_goals simp (disch := decide) only [RegUpd.mem_write, write64_eq_writeW, word_writeW_sep, word_writeW_self]

theorem verifyFinishArgs_ok (s : State) :
    WP isa (.block [mov .x2 .x0, mov .x0 .x8]) s fun t =>
      t.gpr .x2 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x8 ∧ Keeps [.x2, .x0] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Verification preserves the ABI and checks the original input buffers. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

open VG.Spec.Ed25519 (bytesAt)

def verifyLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 64⟩] ∧
    s.wr = [⟨s.gpr .x3, 8192⟩] ∧
    (⟨s.gpr .x0, 32⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x1, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (⟨s.gpr .x2, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 8192⟩ ∧
    (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s t := t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
    (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 64) (bytesAt s.mem (s.gpr .x2) 64))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧
    bytesAt s.mem (s.gpr .x0) 32 = bytesAt t.mem (t.gpr .x0) 32 ∧
    bytesAt s.mem (s.gpr .x1) 64 = bytesAt t.mem (t.gpr .x1) 64 ∧
    bytesAt s.mem (s.gpr .x2) 64 = bytesAt t.mem (t.gpr .x2) 64

theorem verifyBytes_frame {m m' : Mem} {base p : Addr} {n : Nat}
    (hf : Frame [⟨base, 8192⟩] m m') (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) (by simpa only [List.mem_singleton, forall_eq]) hn (List.mem_range.mp hi)

structure VerifyStarted (s t : State) : Prop where
  context : VerifyContext t (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
  saved : Saved (s.gpr .x3) s.gpr t.mem
  frame : Frame [⟨s.gpr .x3, 8192⟩] s.mem t.mem
  sp : t.sp = s.sp
  regs : ∀ r ∈ [Reg.x25, .x26, .x27, .x28, .x30], t.gpr r = s.gpr r

theorem verifySetup_state_ok {s : State} (hs : verifyLocal.pre s) :
    WP isa (.block verifySetup) s (VerifyStarted s) := by
  obtain ⟨hr, hw, hpk, hsig, hchallenge, hn⟩ := hs
  have hws : (⟨s.gpr .x3, 8192⟩ : Region) ∈ s.wr := by rw [hw]; exact List.mem_singleton_self _
  rw [verifySetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (verifyPrepare_ok s) fun a ⟨ach, asc, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok asc (ka.wr ▸ hws)) fun b ⟨gb, rb, wb, spb, mb, svb⟩ => ?_
  have bs : b.gpr .x2 = s.gpr .x3 := (congrFun gb _).trans asc
  refine WP.mono (verifyHeaders_ok bs (by rw [wb, ka.wr]; exact hws))
    fun c ⟨cs, gc, rc, wc, spc, mc, cp, cr, cc⟩ => ?_
  have fm : Frame [⟨s.gpr .x3, 8192⟩] s.mem c.mem := by
    have f := (scratchFrame mb (by decide)).trans (scratchFrame mc (by decide))
    rw [ka.mem] at f
    exact f
  have sv : Saved (s.gpr .x3) s.gpr c.mem := by
    have v := svb.outside mc (by decide)
    intro rd hrd
    rw [v rd hrd]
    apply ka.gpr
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hc : VerifyContext c (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) := by
    have rr : c.rd = s.rd := rc.trans (rb.trans ka.rd)
    have ww : c.wr = s.wr := wc.trans (wb.trans ka.wr)
    refine ⟨⟨cs, ww ▸ hws, hn⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cp, gb, ka.gpr .x0 (by decide)]
    · rw [cr, gb, ka.gpr .x1 (by decide)]
    · rw [cc, gb, ach]
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ hd (by omega)⟩
    · intro d hd
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show d + 8 ≤ 64 by omega) (by omega)⟩
    · intro d hd
      rw [show off (off (s.gpr .x1) 32) d = off (s.gpr .x1) (32 + d) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + d + 8 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      rw [show off (off (s.gpr .x1) 32) i = off (s.gpr .x1) (32 + i) from Offset.add_add ..]
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show 32 + i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi
      exact ⟨_, by rw [rr, hr]; simp, Offset.contains_base _ (show i + 1 ≤ 64 by omega) (by omega)⟩
    · intro i hi; exact farScr hpk hi (by decide)
    · intro i hi; exact farScr hsig (by omega) (by decide)
    · intro i hi
      rw [show off (off (s.gpr .x1) 32) i = off (s.gpr .x1) (32 + i) from Offset.add_add ..]
      exact farScr hsig (by omega) (by decide)
    · intro i hi; exact farScr hchallenge hi (by decide)
  refine ⟨hc, sv, fm, spc.trans (spb.trans ka.sp), fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    rw [gc _ (by decide), gb, ka.gpr _ (by decide)]

theorem verify_correct {s : State} (hs : verifyLocal.pre s) :
    WP isa verifyEquation s fun t => abiPreserved s t ∧ verifyLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  have hpk := hs.2.2.1
  have hsig := hs.2.2.2.1
  have hchallenge := hs.2.2.2.2.1
  rw [verifyEquation]
  refine WP.seq (WP.mono (verifySetup_state_ok hs) fun c hc0 => ?_)
  have hc := hc0.context
  have sv := hc0.saved
  have fm := hc0.frame
  refine WP.seq (WP.mono (verifyBody_ok hc) fun d ⟨kd, dv⟩ => ?_)
  have md := tableFrame_work kd.mem (by decide) (by decide)
  have svd := sv.outside md (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (verifyFinishArgs_ok d) fun e ⟨es, ev, ke⟩ => ?_
  have er : e.gpr .x2 = s.gpr .x3 := es.trans (kd.scratch hc.scratch).x0
  refine WP.mono (scalarRestore_ok (g := s.gpr) er (by rw [ke.wr, kd.wr]; exact hc.scratch.wr)
    (by rw [ke.mem]; exact svd)) fun t ⟨tr, kt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tr (.x19, 0) (by decide)
    · exact tr (.x20, 8) (by decide)
    · exact tr (.x21, 16) (by decide)
    · exact tr (.x22, 24) (by decide)
    · exact tr (.x23, 32) (by decide)
    · exact tr (.x24, 40) (by decide)
    all_goals
      rw [kt.gpr _ (by decide), ke.gpr _ (by decide), kd.gpr _ (by decide) (by decide) (by decide)]
      exact hc0.regs _ (by decide)
  · exact kt.sp.trans (ke.sp.trans (kd.sp.trans hc0.sp))
  · change t.gpr .x0 = _
    rw [kt.gpr _ (by decide), ev, dv,
      verifyBytes_frame fm hpk (by decide), verifyBytes_frame fm hsig (by decide),
      verifyBytes_frame fm hchallenge (by decide)]

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyCT`. -/
section
/-! Complete verification leaks only the inputs declared public by its contract. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

open VG.Spec.Ed25519 (bytesAt)

theorem VerifyStarted.public {s t : State} (hs : verifyLocal.pre s) (h : VerifyStarted s t) :
    VerifyPublic (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
      (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 32)
      (bytesAt s.mem (off (s.gpr .x1) 32) 32) (bytesAt s.mem (s.gpr .x2) 64) t := by
  have hm := verifyBytes_frame h.frame hs.2.2.2.1 (by decide)
  have hr := congrArg (List.take 32) hm
  have hscalar := congrArg (List.drop 32) hm
  rw [signatureBytes_take, signatureBytes_take] at hr
  rw [signatureBytes_drop, signatureBytes_drop] at hscalar
  exact ⟨h.context, verifyBytes_frame h.frame hs.2.2.1 (by decide), hr, hscalar,
    verifyBytes_frame h.frame hs.2.2.2.2.1 (by decide)⟩

theorem VerifyStarted.public_right {s u t : State} (hu : verifyLocal.pre u)
    (hp : verifyLocal.pub s u) (h : VerifyStarted u t) :
    VerifyPublic (s.gpr .x3) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
      (bytesAt s.mem (s.gpr .x0) 32) (bytesAt s.mem (s.gpr .x1) 32)
      (bytesAt s.mem (off (s.gpr .x1) 32) 32) (bytesAt s.mem (s.gpr .x2) 64) t := by
  have ht := h.public hu
  obtain ⟨_, pk, sig, challenge, base, pbs, sigbs, kbs⟩ := hp
  have rbs := congrArg (List.take 32) sigbs
  have sbs := congrArg (List.drop 32) sigbs
  rw [signatureBytes_take, signatureBytes_take] at rbs
  rw [signatureBytes_drop, signatureBytes_drop] at sbs
  rw [← pbs, ← rbs, ← sbs, ← kbs, ← pk, ← sig, ← challenge, ← base] at ht
  exact ht

theorem verifyFinish_ct (base : Addr) :
    CT (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base)
      (.block (([mov .x2 .x0, mov .x0 .x8] : List Instr) ++ scalarRestore)) (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
  exact fun _ _ h => x0_agree h.1 h.2

theorem verifyBody_base_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) :
    CT (fun s t => VerifyPublic base pk sig challenge pkbs rbs sbs kbs s ∧
      VerifyPublic base pk sig challenge pkbs rbs sbs kbs t)
      (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid))
      (fun s t => s.gpr .x0 = base ∧ t.gpr .x0 = base) := by
  have hw (s : State) (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs s) :
      WP isa (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecodeA recoverInvalid)) s
        (fun t => t.gpr .x0 = base) :=
    WP.mono (verifyBody_ok h.context) fun _ kt => (kt.1.scratch h.context.scratch).x0
  exact (CT.wp (verifyBody_ct base pk sig challenge pkbs rbs sbs kbs)
    (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  have setupCT : CT (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      (.block verifySetup) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x3]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.2.2.2.2.2.2.1
  have hp := withRuns setupCT (fun s t h => ⟨verifySetup_state_ok h.1, verifySetup_state_ok h.2.1⟩)
  have whole : CT (fun s t => verifyLocal.pre s ∧ verifyLocal.pre t ∧ verifyLocal.pub s t)
      verifyEquation (fun _ _ => True) := by
    rw [verifyEquation]
    refine CT.seq hp ?_
    intro s t ts tt s' t' ⟨hsp, _, a, b, hab, ha, hb⟩ es et
    have pa := ha.public hab.1
    have pb := hb.public_right hab.2.1 hab.2.2
    exact CT.seq
      (verifyBody_base_ct (a.gpr .x3) (a.gpr .x0) (a.gpr .x1) (a.gpr .x2)
        (bytesAt a.mem (a.gpr .x0) 32) (bytesAt a.mem (a.gpr .x1) 32)
        (bytesAt a.mem (off (a.gpr .x1) 32) 32) (bytesAt a.mem (a.gpr .x2) 64))
      (verifyFinish_ct (a.gpr .x3)) _ _ _ _ _ _ ⟨hsp, pa, pb⟩ es et
  intro s t ts tt s' t' hs ht hp es et
  exact (whole _ _ _ _ _ _ ⟨hp.1, hs, ht, hp⟩ es et).1

end VG.Proof.Ed25519.AArch64
end

/-! The complete verifier satisfies the merged specification and leakage contract. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def verifySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' := verify_correct hs

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract AArch64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, verifyLocal]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs]
    change t.gpr .x0 = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs] [verifySatState] using verifySatState

theorem verify_verified : Verified AArch64.target verifyEquation (Spec.Ed25519.verifyEquationContract AArch64.abi) :=
  Verified.of_correct verify_ok verify_ct verify_implies

end VG.Proof.Ed25519.AArch64
