import VerifiedGarbage.Proof.X25519.AArch64.Word.Head
import VerifiedGarbage.Proof.X25519.AArch64.Word.Formula
import VerifiedGarbage.Proof.X25519.AArch64.Word.Small

/-! One complete four-word ladder iteration. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

theorem stepFields_ok {base : Addr} {s : State} (hs : Scratch s base)
    (hc : env s.mem base 18 = 121665) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.stepFields) s fun t =>
      Keep base s t ∧ env t.mem base = evalOps VG.Impl.X25519.AArch64.Word.stepOps (env s.mem base) := by
  rw [VG.Impl.X25519.AArch64.Word.stepFields,List.append_assoc,WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka,ea⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulA24_ok (ka.scr hs) 2 11) fun b ⟨kb,eb⟩ => ?_
  refine WP.mono (fieldCode_ok _ (kb.scr (ka.scr hs))) fun t ⟨kt,et⟩ => ?_
  refine ⟨ka.trans (kb.trans kt),?_⟩
  rw [et,eb,ea]
  have he : evalOp (.mul 2 11 18) (evalOps (VG.Impl.X25519.AArch64.Word.stepOps.take 15) (env s.mem base)) =
      Function.update (evalOps (VG.Impl.X25519.AArch64.Word.stepOps.take 15) (env s.mem base)) 2
        (evalOps (VG.Impl.X25519.AArch64.Word.stepOps.take 15) (env s.mem base) 11 * 121665) := by
    have hp : evalOps (VG.Impl.X25519.AArch64.Word.stepOps.take 15) (env s.mem base) 18 =
        env s.mem base 18 := rfl
    simp only [evalOp,hp,hc]
  rw [← he]
  rfl

theorem step_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} {st : Ladder} {i : Nat}
    (hs : Scratch s base) (hi : i < 255) (hg : Good (env s.mem base) x1 st)
    (hsw : st.swap ≤ 1) (hc : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hw : word s.mem base 768 = BitVec.ofNat 64 st.swap)
    (hb : s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit k i)) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.step) s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x1 (ladderStep k x1 st i) ∧
      t.gpr .x19 = BitVec.ofNat 64 i ∧ word t.mem base 768 = BitVec.ofNat 64 (bit k i) := by
  simp only [VG.Impl.X25519.AArch64.Word.step, VG.Impl.X25519.AArch64.Word.stepHead,
    VG.Impl.X25519.AArch64.Word.cswap, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (prefix_ok hs hi hsw (bit_le k i) hc hw hb) fun a ⟨ka, ea, ca, ma, wa⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (swapField_ok (ka.scratch hs) 1 3 (by decide) ma) fun b ⟨kb, eb, mb⟩ => ?_
  have kab : LoopKeep base s b := ka.trans (LoopKeep.of_field kb)
  rw [WP.block_append_iff]
  refine WP.mono (swapField_ok (kab.scratch hs) 2 4 (by decide) (mb.trans ma)) fun c ⟨kc, ec, _⟩ => ?_
  have kac : LoopKeep base s c := kab.trans (LoopKeep.of_field kc)
  refine WP.mono (stepFields_ok (kac.scratch hs) (by
    rw [ec,eb,ea]; exact hg.2.2.2.2.2)) fun t ⟨kt, et⟩ => ?_
  refine ⟨kac.trans (LoopKeep.of_field kt), ?_, ?_, ?_⟩
  · rw [et, ec, eb, ea]
    exact formula_ok _ k x1 st i hg
  · rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), ca]
  · rw [kt.mem.word (Or.inr (by decide : 64+704 ≤ 768)) (by decide : 768+8<2^64),
      kc.mem.word (Or.inr (by decide : 64+704 ≤ 768)) (by decide : 768+8<2^64),
      kb.mem.word (Or.inr (by decide : 64+704 ≤ 768)) (by decide : 768+8<2^64), wa]

end VG.Proof.X25519.AArch64.Word
