import VerifiedGarbage.Proof.Ed25519.Arm.VerifyCTPublic
import VerifiedGarbage.Proof.Ed25519.Arm.PointDecodeCT
import VerifiedGarbage.Proof.Ed25519.Arm.DecodedThenCT

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
