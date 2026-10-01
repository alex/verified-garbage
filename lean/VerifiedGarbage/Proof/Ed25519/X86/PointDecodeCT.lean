import VerifiedGarbage.Proof.Ed25519.X86.RecoverCTPoint
import VerifiedGarbage.Proof.Ed25519.X86.PointDecode

/-! Decoding branches only on the shared public compressed point. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def DecodeCTPre (base : BitVec 32) (n : Nat) (s : State) : Prop := Ctx base s ∧ fe s.mem base 96 = n

theorem decodeHeadCT_ok {base : BitVec 32} {s : State} (hc : Ctx base s) :
    WP isa (.block (decodeY ++ canonicalY)) s fun t =>
      RecoverCTPre base (fe s.mem base 96 / 2 ^ 255 == 1)
        (VG.Proof.X25519.toFe (fe s.mem base 96 % 2 ^ 255)) t ∧
      t.zf = some (decide (fe s.mem base 96 % 2 ^ 255 < Spec.X25519.P)) := by
  rw [WP.block_append_iff]
  refine WP.mono (decodeY_ok hc) fun a ⟨ka, ya, ba⟩ => ?_
  have ca := ka.ctx hc
  refine WP.mono (canonicalY_ok ca (by rw [ya]; exact Nat.mod_lt _ (by decide))) fun t ⟨kt, et, bt, zt⟩ => ?_
  refine ⟨⟨kt.ctx ca, ?_, ?_⟩, ?_⟩
  · rw [bt, ba]
    have hn : fe s.mem base 96 / 2 ^ 255 ≤ 1 := by
      have hlt := fe_lt s.mem base 96
      omega_using [hlt]
    rcases (by omega_using [hn] : fe s.mem base 96 / 2 ^ 255 = 0 ∨ fe s.mem base 96 / 2 ^ 255 = 1) with h | h
    all_goals rw [h]; rfl
  · rw [et]
    change VG.Proof.X25519.toFe (fe a.mem base 96) = _
    rw [ya]
  · rw [zt, ya]

theorem pointDecode_ct (base : BitVec 32) (n : Nat) :
    RelCT isa (fun s t => DecodeCTPre base n s ∧ DecodeCTPre base n t) pointDecode (fun _ _ => True) := by
  let b := n / 2 ^ 255 == 1
  let y := VG.Proof.X25519.toFe (n % 2 ^ 255)
  have ht : RelCT isa (fun s t => DecodeCTPre base n s ∧ DecodeCTPre base n t)
      (.block (decodeY ++ canonicalY)) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
    exact fun _ _ h => edi_agree h.1.1.edi h.2.1.edi
  have hw (s : State) (h : DecodeCTPre base n s) :
      WP isa (.block (decodeY ++ canonicalY)) s fun t =>
        RecoverCTPre base b y t ∧ t.zf = some (decide (n % 2 ^ 255 < Spec.X25519.P)) := by
    have hh := decodeHeadCT_ok h.1
    rw [h.2] at hh
    exact hh
  have hp := ht.wp (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [pointDecode]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (recoverPoint_ct base b y).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .eax = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.X86
