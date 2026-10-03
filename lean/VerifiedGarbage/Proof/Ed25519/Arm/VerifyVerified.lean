import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTRhs
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.DecodedThen
import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTRoot
import VerifiedGarbage.Proof.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTLit
import VerifiedGarbage.Impl.Ed25519.Arm.Verify
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Ed25519.Arm.DecodeCTLit
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-! Merged from `Proof.Ed25519.Arm.VerifyCT`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTPoints`. -/
section
/-! The strict equation has identical traces for identical public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def EquationCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7744 = a ∧ tablePoint s.mem b 7872 = r

theorem verifyLhs_public_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t)
      verifyLhs (fun s t => RhsCTPre m b pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint) s ∧
        RhsCTPre m b pk sig challenge a r
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32)) Spec.Ed25519.basePoint) t) := by
  apply ctBoth
  · exact (verifyLhs_ct b pk sig challenge).mono (fun _ _ h =>
      ⟨⟨h.1.1.ctx, h.1.2.1⟩, ⟨h.2.1.ctx, h.2.2.1⟩⟩) (fun _ _ h => h)
  · intro s ⟨hp, hl, ha, hr⟩
    refine WP.mono (verifyLhs_ok hp.ctx hl) fun t ⟨tk, tl, tp, ta, tr⟩ => ?_
    exact ⟨hp.keep tk, tl, ta.trans ha, tr.trans hr,
      tp.trans (congrArg (fun bs => Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE bs) Spec.Ed25519.basePoint) hp.sBytes)⟩

theorem verifyEquationPoints_ct (m : Mem) (b pk sig challenge : BitVec 32) (a r : Spec.Ed25519.Point) :
    CT (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t)
      verifyEquationPoints (fun _ _ => True) :=
  RelCT.seq (verifyLhs_public_ct m b pk sig challenge a r) (verifyRhs_ct m b pk sig challenge a r _)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTDecodeSupport`. -/
section
/-! Merged from `Proof.Ed25519.Arm.DecodedThenCT`. -/
section
/-! The success branch follows the public decoder flag. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem decodedThen_ct {P : State → Prop} {next : Prog isa} (flag : Bool)
    (hp : ∀ s, P s → s.gpr .r9 = BitVec.ofNat 32 flag.toNat)
    (keep : ∀ s t, P s → Rest [] s t → t.mem = s.mem → P t)
    (yes : flag = true → CT (fun s t => P s ∧ P t) next (fun _ _ => True)) :
    CT (fun s t => P s ∧ P t) (decodedThen next) (fun _ _ => True) := by
  have hc : CT (fun s t => P s ∧ P t) (.block [.cmp .r9 (.imm 0)])
      (fun s t => (P s ∧ VG.Arm.eval .ne s = some flag) ∧ (P t ∧ VG.Arm.eval .ne t = some flag)) := by
    apply ctBoth
    · exact ctRegs [] (fun _ _ _ _ hr => (List.not_mem_nil hr).elim) (by taint_decide)
    · intro s hs
      refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨keep s t hs (ht.rest []) ht.mem, ?_⟩
      rw [VG.Arm.eval, hz, hp s hs]
      cases flag <;> rfl
  refine RelCT.seq hc (RelCT.ite (fun _ _ h => h.1.2.trans h.2.2.symm) ?_ ?_)
  · intro s t ts tt u v h ex ey
    have hy : flag = true := Option.some.inj (h.1.1.2.symm.trans h.2)
    exact yes hy _ _ _ _ _ _ ⟨h.1.1.1, h.1.2.1⟩ ex ey
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.PointDecodeCT`. -/
section
/-! Strict point decoding leaks only its public encoded bytes and pointers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def DecodeCTPre (base ptr : BitVec 32) (bs : List Byte) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ s.gpr .r12 = ptr ∧ ptr.toNat + 32 ≤ 2 ^ 32 ∧
    (∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩ ∧
    Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = bs

theorem pointDecode_ct (base ptr : BitVec 32) (bs : List Byte) :
    CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t) pointDecode (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := VG.Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : CT (fun s t => DecodeCTPre base ptr bs s ∧ DecodeCTPre base ptr bs t)
      pointDecodeLoad (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base ptr bs s) :
      WP isa pointDecodeLoad s fun t => RecoverCTPre base b y t ∧
        t.z = decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P) := by
    obtain ⟨hc, hl, hp, hf, hr, hsep, hbs⟩ := h
    refine WP.mono (pointDecodeLoad_ok hc hl hp hf hr hsep) fun t ⟨kt, lt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.ctx hc, lt, ?_, ?_⟩, ?_⟩
    · rw [tb, hbs]
    · rw [ty, hbs]
    · rw [tz, hbs]
  rw [pointDecode]
  refine RelCT.seq (ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.2.1.2.trans h.2.2.2.symm)
  · exact (recoverPoint_ct base b y).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .r9 = BitVec.ofNat 32 p.isSome.toNat := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.Arm
end

/-! Reload and decode either public point, retaining the equation's packed points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem decodeResult_congr {b : BitVec 32} {p q : Option Spec.Ed25519.Point} {s : State}
    (he : p = q) (h : DecodeResult b p s) : DecodeResult b q s := he ▸ h

theorem decodeResult_rest {b : BitVec 32} {p : Option Spec.Ed25519.Point} {s t : State}
    (hr : Rest [] s t) (hm : t.mem = s.mem) (h : DecodeResult b p s) : DecodeResult b p t := by
  cases p with
  | none => exact (hr.gpr _ (by decide)).trans h
  | some p => exact ⟨(hr.gpr _ (by decide)).trans h.1,
      (congrArg (fun m => point (env m b) 0 1 2 3) hm).trans h.2⟩

def LoadDecodePre (b ptr : BitVec 32) (bs : List Byte) (d : Nat) (s : State) : Prop :=
  Ctx b s ∧ AllLim s.mem b ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = ptr ∧
    VerifyInput b ptr 32 s ∧ Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 = bs

theorem loadDecode_ct (b ptr : BitVec 32) (bs : List Byte) (d : Nat) (hd : d = 8128 ∨ d = 8132) :
    CT (fun s t => LoadDecodePre b ptr bs d s ∧ LoadDecodePre b ptr bs d t)
      (.seq (.block (loadHeader d)) pointDecode) (fun _ _ => True) := by
  have trace : CT (fun s t => s.gpr .r0 = t.gpr .r0) (.block (loadHeader d)) (fun _ _ => True) := by
    rcases hd with rfl | rfl
    all_goals
      apply ctRegs [.r0] _ (by taint_decide)
      intro s t h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h
  have head : CT (fun s t => LoadDecodePre b ptr bs d s ∧ LoadDecodePre b ptr bs d t)
      (.block (loadHeader d)) (fun s t => DecodeCTPre b ptr bs s ∧ DecodeCTPre b ptr bs t) := by
    apply ctBoth
    · exact trace.mono (fun _ _ h => h.1.1.r0.trans h.2.1.r0.symm) (fun _ _ h => h)
    · intro s ⟨hc, hl, hh, hi, hb⟩
      refine WP.mono (loadHeader_ok hc d (by omega)) fun t ⟨tr, tm, tp⟩ => ?_
      exact ⟨hc.of_rest tr (by decide), tm ▸ hl, tp.trans hh, hi.fit,
        fun i hn => by rw [tr.rd, tr.wr]; exact hi.readable i hn, hi.separate,
        (congrArg (fun m => Spec.Ed25519.bytesAt m (State.addr ptr) 32) tm).trans hb⟩
  exact RelCT.seq head (pointDecode_ct b ptr bs)

theorem loadDecode_ok {b ptr : BitVec 32} {bs : List Byte} {d : Nat} {s : State}
    (h : LoadDecodePre b ptr bs d s) (hd : d + 4 ≤ 8192) :
    WP isa (.seq (.block (loadHeader d)) pointDecode) s fun t =>
      VerifyKeep b s t ∧ AllLim t.mem b ∧ DecodeResult b (Spec.Ed25519.decodePoint bs) t ∧
        ∀ k, 1600 ≤ k → k + 128 ≤ 8192 → tablePoint t.mem b k = tablePoint s.mem b k := by
  obtain ⟨hc, hl, hh, hi, hb⟩ := h
  refine WP.seq (WP.mono (loadHeader_ok hc d (by omega)) fun u ⟨ur, um, up⟩ => ?_)
  have ku : VerifyKeep b s u := VerifyKeep.of_rest ur (by decide) um
  have ui := hi.keep ku
  refine WP.mono (pointDecode_ok (ku.ctx hc) (um ▸ hl) (up.trans hh) ui.fit ui.readable ui.separate)
    fun t ht => ?_
  refine ⟨ku.trans (VerifyKeep.of_decode ht.1), ht.2.1, ?_, fun k hk hn => ?_⟩
  · with_reducible exact decodeResult_congr (congrArg Spec.Ed25519.decodePoint
      ((congrArg (fun m => Spec.Ed25519.bytesAt m (State.addr ptr) 32) um).trans hb)) ht.2.2
  · exact (ht.1.table hk hn).trans (congrArg (fun m => tablePoint m b k) um)

end VG.Proof.Ed25519.Arm
end

/-! Untrusted: R decoding and its success branch are determined by public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def RDecodeCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ tablePoint s.mem b 7744 = a

def RDecodedCTPre (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point)
    (q : Option Spec.Ed25519.Point) (s : State) : Prop :=
  RDecodeCTPre m b pk sig challenge a s ∧ DecodeResult b q s

theorem verifyAfterR_ct (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) (q : Option Spec.Ed25519.Point) :
    CT (fun s t => RDecodedCTPre m b pk sig challenge a q s ∧ RDecodedCTPre m b pk sig challenge a q t)
      (decodedThen (.seq (.block (pointTableWrite 7872)) verifyEquationPoints)) (fun _ _ => True) := by
  apply decodedThen_ct q.isSome
  · exact fun _ h => decodeResult_flag h.2
  · intro s t h tr tm
    have kt : VerifyKeep b s t := VerifyKeep.of_rest tr (by decide) tm
    exact ⟨⟨h.1.1.keep kt, tm ▸ h.1.2.1, (congrArg (fun mem => tablePoint mem b 7744) tm).trans h.1.2.2⟩,
      decodeResult_rest tr tm h.2⟩
  · intro yes
    cases q with
    | none => exact Bool.noConfusion yes
    | some r =>
      have hw : CT (fun s t => RDecodedCTPre m b pk sig challenge a (some r) s ∧ RDecodedCTPre m b pk sig challenge a (some r) t)
          (.block (pointTableWrite 7872)) (fun s t => EquationCTPre m b pk sig challenge a r s ∧ EquationCTPre m b pk sig challenge a r t) := by
        apply ctBoth
        · apply ctRegs [.r0] _ (by taint_decide)
          intro s t h reg hr
          rw [List.mem_singleton] at hr
          subst reg
          exact h.1.1.1.ctx.ctx.r0.trans h.2.1.1.ctx.ctx.r0.symm
        · intro s ⟨⟨hp, hl, ha⟩, _, hpoint⟩
          refine WP.mono (pointTableWrite_ok hp.ctx.ctx hl 7872 (by decide) (by decide)) fun t ⟨tk, tl, _, tp⟩ => ?_
          exact ⟨hp.keep (VerifyKeep.of_powers tk (by decide) (by decide)), tl,
            (tk.frame.point (by decide) (.inl (by decide)) (by decide) (by decide)).trans ha, tp.trans hpoint⟩
      exact RelCT.seq hw (verifyEquationPoints_ct m b pk sig challenge a r)

theorem verifyDecodeR_ct (m : Mem) (b pk sig challenge : BitVec 32) (a : Spec.Ed25519.Point) :
    CT (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t)
      verifyDecodeR (fun _ _ => True) := by
  have loadPre (s : State) (h : RDecodeCTPre m b pk sig challenge a s) :
      LoadDecodePre b sig (Spec.Ed25519.bytesAt m (State.addr sig) 32) 8132 s :=
    ⟨h.1.ctx.ctx, h.2.1, h.1.ctx.sigHeader, h.1.ctx.sigInput.prefix (by decide), h.1.rBytes⟩
  have hd : CT (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t)
      (.seq (.block (loadHeader 8132)) pointDecode)
      (fun s t => RDecodedCTPre m b pk sig challenge a (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) s ∧
        RDecodedCTPre m b pk sig challenge a (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr sig) 32)) t) := by
    apply ctBoth
    · exact (loadDecode_ct b sig _ 8132 (by decide)).mono (fun s t h => ⟨loadPre s h.1, loadPre t h.2⟩) (fun _ _ h => h)
    · intro s hs
      refine WP.mono (loadDecode_ok (loadPre s hs) (by decide)) fun t ht => ?_
      refine ⟨⟨hs.1.keep ht.1, ht.2.1, (ht.2.2.2 7744 (by decide) (by decide)).trans hs.2.2⟩, ?_⟩
      with_reducible exact ht.2.2.1
  exact ctSeqAssoc (RelCT.seq hd (verifyAfterR_ct m b pk sig challenge a _))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTBody`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyCTDecodeA`. -/
section
/-! Untrusted: A decoding and its success branch are determined by public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ADecodedCTPre (m : Mem) (b pk sig challenge : BitVec 32)
    (q : Option Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b ∧ DecodeResult b q s

theorem verifyAfterA_ct (m : Mem) (b pk sig challenge : BitVec 32) (q : Option Spec.Ed25519.Point) :
    CT (fun s t => ADecodedCTPre m b pk sig challenge q s ∧ ADecodedCTPre m b pk sig challenge q t)
      (decodedThen (.seq (.block (pointTableWrite 7744)) verifyDecodeR)) (fun _ _ => True) := by
  apply decodedThen_ct q.isSome
  · exact fun _ h => decodeResult_flag h.2.2
  · intro s t h tr tm
    have kt : VerifyKeep b s t := VerifyKeep.of_rest tr (by decide) tm
    exact ⟨h.1.keep kt, tm ▸ h.2.1, decodeResult_rest tr tm h.2.2⟩
  · intro yes
    cases q with
    | none => exact Bool.noConfusion yes
    | some a =>
      have hw : CT (fun s t => ADecodedCTPre m b pk sig challenge (some a) s ∧ ADecodedCTPre m b pk sig challenge (some a) t)
          (.block (pointTableWrite 7744)) (fun s t => RDecodeCTPre m b pk sig challenge a s ∧ RDecodeCTPre m b pk sig challenge a t) := by
        apply ctBoth
        · apply ctRegs [.r0] _ (by taint_decide)
          intro s t h reg hr
          rw [List.mem_singleton] at hr
          subst reg
          exact h.1.1.ctx.ctx.r0.trans h.2.1.ctx.ctx.r0.symm
        · intro s ⟨hp, hl, _, hpoint⟩
          refine WP.mono (pointTableWrite_ok hp.ctx.ctx hl 7744 (by decide) (by decide)) fun t ⟨tk, tl, _, tp⟩ => ?_
          exact ⟨hp.keep (VerifyKeep.of_powers tk (by decide) (by decide)), tl, tp.trans hpoint⟩
      exact RelCT.seq hw (verifyDecodeR_ct m b pk sig challenge a)

theorem verifyDecodeA_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) verifyDecodeA (fun _ _ => True) := by
  have loadPre (s : State) (h : VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) :
      LoadDecodePre b pk (Spec.Ed25519.bytesAt m (State.addr pk) 32) 8128 s :=
    ⟨h.1.ctx.ctx, h.2, h.1.ctx.pkHeader, h.1.ctx.pkInput, h.1.pkBytes⟩
  have hd : CT (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
      (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b))
      (.seq (.block (loadHeader 8128)) pointDecode)
      (fun s t => ADecodedCTPre m b pk sig challenge (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) s ∧
        ADecodedCTPre m b pk sig challenge (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt m (State.addr pk) 32)) t) := by
    apply ctBoth
    · exact (loadDecode_ct b pk _ 8128 (by decide)).mono (fun s t h => ⟨loadPre s h.1, loadPre t h.2⟩) (fun _ _ h => h)
    · intro s hs
      refine WP.mono (loadDecode_ok (loadPre s hs) (by decide)) fun t ht => ?_
      refine ⟨hs.1.keep ht.1, ht.2.1, ?_⟩
      with_reducible exact ht.2.2.1
  exact ctSeqAssoc (RelCT.seq hd (verifyAfterA_ct m b pk sig challenge _))

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyCTScalar`. -/
section
/-! Canonical scalar checking loads through the public signature pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyScalar_ct (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block verifyScalar) (fun _ _ => True) := by
  have head : CT (fun s t => VerifyContext b pk sig challenge s ∧ VerifyContext b pk sig challenge t)
      (.block (loadHeader 8132 ++ ([.dp .add .r12 .r12 (.imm 32)] : List Instr)))
      (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32)) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by taint_decide)
      intro s t h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.ctx.r0.trans h.2.ctx.r0.symm
    · intro s hc
      rw [WP.block_append_iff]
      refine WP.mono (loadHeader_ok hc.ctx 8132 (by decide)) fun u ⟨ur, um, up⟩ => ?_
      refine WP.mono (addInput32_ok u) fun t ⟨tr, _, tp⟩ => ?_
      exact ⟨(tr.gpr _ (by decide)).trans ((ur.gpr _ (by decide)).trans hc.ctx.r0), by rw [tp, up, hc.sigHeader]⟩
  have tail : CT (fun s t => (s.gpr .r0 = b ∧ s.gpr .r12 = sig + 32) ∧ (t.gpr .r0 = b ∧ t.gpr .r12 = sig + 32))
      (.block (unpackField SR 0 ++ scalarCompare ++ ([.cmp .r5 (.imm 0)] : List Instr))) (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro s t h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.trans h.2.1.symm
    · exact h.1.2.trans h.2.2.symm
  simpa only [verifyScalar, List.append_assoc] using ctBlockAppend head tail

theorem verifyScalar_public_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      (.block verifyScalar) (fun s t =>
        (VerifyPublic m b pk sig challenge s ∧ s.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L)) ∧
        (VerifyPublic m b pk sig challenge t ∧ t.z = decide (Spec.Ed25519.decodeLE
          (Spec.Ed25519.bytesAt m (State.addr (sig + 32)) 32) < Spec.Ed25519.L))) := by
  apply ctBoth
  · exact (verifyScalar_ct b pk sig challenge).mono (fun _ _ h => ⟨h.1.ctx, h.2.ctx⟩) (fun _ _ h => h)
  · intro s hs
    refine WP.mono (verifyScalar_ok hs.ctx) fun t ⟨tk, tz⟩ => ?_
    exact ⟨hs.keep tk, tz.trans (congrArg (fun bs => decide (Spec.Ed25519.decodeLE bs < Spec.Ed25519.L)) hs.sBytes)⟩

end VG.Proof.Ed25519.Arm
end

/-! The complete strict verifier leaks only its declared public inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem verifyInit_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      (.block initFields) (fun s t => (VerifyPublic m b pk sig challenge s ∧ AllLim s.mem b) ∧
        (VerifyPublic m b pk sig challenge t ∧ AllLim t.mem b)) := by
  apply ctBoth
  · apply ctRegs [.r0] _ (by taint_decide)
    intro s t h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.ctx.ctx.r0.trans h.2.ctx.ctx.r0.symm
  · intro s hs
    refine WP.mono (initFields_ok hs.ctx.ctx) fun t ⟨tk, tl, _⟩ => ?_
    exact ⟨hs.keep (VerifyKeep.of_keep tk), tl⟩

theorem verifyBody_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
      verifyBody (fun _ _ => True) := by
  refine RelCT.seq (verifyScalar_public_ct m b pk sig challenge) (RelCT.ite ?_ ?_ ?_)
  · exact fun _ _ h => congrArg some (h.1.2.trans h.2.2.symm)
  · exact (RelCT.seq (verifyInit_ct m b pk sig challenge) (verifyDecodeA_ct m b pk sig challenge)).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
end

/-! The verifier's ABI wrapper preserves the public input relation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

structure VerifyWrapPublic (m : Mem) (b pk sig challenge : BitVec 32) (s : State) : Prop where
  pre : verifyLocal.pre s
  r0 : s.gpr .r0 = pk
  r1 : s.gpr .r1 = sig
  r2 : s.gpr .r2 = challenge
  r3 : s.gpr .r3 = b
  pkBytes : Spec.Ed25519.bytesAt s.mem (State.addr pk) 32 = Spec.Ed25519.bytesAt m (State.addr pk) 32
  sigBytes : Spec.Ed25519.bytesAt s.mem (State.addr sig) 64 = Spec.Ed25519.bytesAt m (State.addr sig) 64
  challengeBytes : Spec.Ed25519.bytesAt s.mem (State.addr challenge) 64 = Spec.Ed25519.bytesAt m (State.addr challenge) 64

theorem verifySetup_ct (m : Mem) (b pk sig challenge : BitVec 32) :
    CT (fun x y => VerifyWrapPublic m b pk sig challenge x ∧ VerifyWrapPublic m b pk sig challenge y)
      (.block verifySetup) (fun x y => VerifyPublic m b pk sig challenge x ∧ VerifyPublic m b pk sig challenge y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r1, .r2, .r3] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.1.r0.trans h.2.r0.symm
    · exact h.1.r1.trans h.2.r1.symm
    · exact h.1.r2.trans h.2.r2.symm
    · exact h.1.r3.trans h.2.r3.symm
  · intro s h
    have hp := VerifyPre.of h.pre
    refine WP.mono (verifySetup_ok hp) fun t ⟨tc, _, _, tf⟩ => ?_
    have tc' : VerifyContext b pk sig challenge t := by rw [h.r0, h.r1, h.r2, h.r3] at tc; exact tc
    have bytes (p : BitVec 32) (n : Nat) (hn : n ≤ 64)
        (hd : (⟨State.addr p, n⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
        Spec.Ed25519.bytesAt t.mem (State.addr p) n = Spec.Ed25519.bytesAt s.mem (State.addr p) n := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun i hi => tf.bytes (R := ⟨State.addr p, n⟩)
        (fun r hr => ?_) (by omega : n ≤ 2 ^ 64) (List.mem_range.mp hi)
      rw [List.mem_singleton.mp hr, h.r3]
      exact hd
    exact ⟨tc', (bytes pk 32 (by decide) tc'.pkInput.separate).trans h.pkBytes,
      (bytes sig 64 (by decide) tc'.sigInput.separate).trans h.sigBytes,
      (bytes challenge 64 (by decide) tc'.challengeInput.separate).trans h.challengeBytes⟩

theorem verify_ct_of_body
    (bodyCT : ∀ (m : Mem) (b pk sig challenge : BitVec 32),
      CT (fun s t => VerifyPublic m b pk sig challenge s ∧ VerifyPublic m b pk sig challenge t)
        verifyBody (fun _ _ => True)) :
    ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation := by
  have hct (m : Mem) (b pk sig challenge : BitVec 32) :
      CT (fun x y => VerifyWrapPublic m b pk sig challenge x ∧ VerifyWrapPublic m b pk sig challenge y)
        verifyEquation (fun _ _ => True) := by
    have hb := (bodyCT m b pk sig challenge).wpDep (fun x y h => ⟨verifyBody_ok h.1.ctx, verifyBody_ok h.2.ctx⟩)
    have hb' := hb.mono (fun _ _ h => h) (fun x y ⟨_, a, c, h, hx, hy⟩ =>
      And.intro (hx.1.ctx h.1.ctx.ctx).r0 (hy.1.ctx h.2.ctx.ctx).r0)
    refine RelCT.seq (verifySetup_ct m b pk sig challenge) (RelCT.seq hb' ?_)
    apply ctRegs [.r0] _ (by taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.trans h.2.symm
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2, h3, hbytes⟩ ex ey
  have hb := byteMap_inj hbytes
  obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
  obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
  rw [← h0] at first
  rw [← h1] at middle
  rw [← h2] at last
  exact (hct s.mem (s.gpr .r3) (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨ht, h0.symm, h1.symm, h2.symm, h3.symm, first.symm, middle.symm, last.symm⟩⟩ ex ey).1

theorem verify_ct : ConstantTime isa verifyLocal.pre verifyLocal.pub verifyEquation :=
  verify_ct_of_body verifyBody_ct

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.VerifyLit`. -/
section
namespace VG.Impl.Ed25519.Arm
materialize_code verifyEquation
end VG.Impl.Ed25519.Arm
end

/-! The verification equation meets the reviewed contract and preserves the ARM ABI. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' :=
  verifyEquation_correct (VerifyPre.of hs)

private theorem returnFlag_value (v : BitVec 32) (b : Bool)
    (h : v.toNat = if b then 1 else 0) : v = if b then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  cases b <;> exact h

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract Arm.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    intro s t _ h
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    exact (e _ _).trans (returnFlag_value _ _ h)
  pub := by
    sig_implies_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, verifyLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [verifySatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using verifySatState

theorem verify_verified : Verified Arm.target verifyEquation (Spec.Ed25519.verifyEquationContract Arm.abi) :=
  Verified.of_correct verify_ok verify_ct verify_implies

end VG.Proof.Ed25519.Arm
