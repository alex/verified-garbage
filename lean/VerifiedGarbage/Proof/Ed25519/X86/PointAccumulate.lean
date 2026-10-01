import VerifiedGarbage.Proof.Ed25519.X86.BitMask
import VerifiedGarbage.Proof.Ed25519.X86.PointSelect

/-! Untrusted: one exact scalar-multiplication bit, including masked selection. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem select_flip {α : Sort _} (bit : Bool) {a b c d e : α}
    (hc : c = if !bit then d else e) (hd : d = a) (he : e = b) :
    c = if bit then b else a := by
  cases bit <;> simpa only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, hd, he] using hc

theorem pointAccumulate_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (batch j : Nat) (hb : batch < 32) (hj : j < 16)
    (hbv : wd s.mem x 28 = BitVec.ofNat 32 batch) (hjv : s.gpr .esi = BitVec.ofNat 32 j)
    (bit : Bool) (hbit : s.mem (addr x (7168 + (16 * batch + j))) = BitVec.ofNat 8 bit.toNat)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa (.block pointAccumulate) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 =
        (if bit then Spec.Ed25519.pointAdd (point (env s.mem x) 0 1 2 3)
          (tablePoint s.mem x (5120 + 128 * j)) else point (env s.mem x) 0 1 2 3) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  simp only [pointAccumulate, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (prepareAdd_ok hc j hj hjv) fun u ⟨ku, pu, qu, su, du⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointAdd_ok (ku.ctx hc) (du.trans hd)) fun v ⟨kv, pv, hv⟩ => ?_
  have kp := ku.trans kv
  have va := pv.trans (congrArg₂ Spec.Ed25519.pointAdd pu qu)
  have vs : point (env v.mem x) 17 18 19 20 = point (env s.mem x) 0 1 2 3 :=
    (point_congr _ _ _ _ (hv 17 (by decide)) (hv 18 (by decide))
      (hv 19 (by decide)) (hv 20 (by decide))).trans su
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitMask_ok (kp.ctx hc) batch j hb hj
    ((kp.word hc 28 (by decide)).trans hbv) (kp.keep.esi.trans hjv) bit
    ((kp.bit hc _ (by omega)).trans hbit)) fun w ⟨kw, mw, bw⟩ => ?_
  refine WP.mono (pointSelect_ok (kw.ctx (kp.ctx hc)) (!bit) bw) fun t ⟨kt, pt, dt⟩ => ?_
  refine ⟨kp.trans (kw.trans kt), ?_, ?_⟩
  · exact select_flip bit pt (by rw [mw]; exact vs) (by rw [mw]; exact va)
  · rw [dt, mw, hv 16 (by decide), du, hd]

end VG.Proof.Ed25519.X86
