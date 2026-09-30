import VerifiedGarbage.Proof.Ed25519.AArch64.Mul
import VerifiedGarbage.Impl.Ed25519.AArch64.MulAdd

/-! Untrusted: full-width multiplication with an initial four-word addend. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64

def wideValue (s : State) : Nat :=
  val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
    2 ^ 256 * val4 (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)

theorem zeroReg_ok (s : State) (r : Reg) :
    WP isa (.block [.movz .w r 0 0]) s fun t => t.gpr r = 0 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun q hq => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hq)

theorem wideAccumulate_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : FieldRange a) (hb : FieldRange b) :
    WP isa (.block (wideAccumulate a b)) s fun t =>
      wideValue t = val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) +
        fe s.mem base a * fe s.mem base b ∧ Keeps (.x10 :: wideClob) s t := by
  rw [wideAccumulate, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (zeroReg_ok s .x10) fun s₀ ⟨hz, k0⟩ => ?_
  refine WP.mono (rowsAccumulate_ok (hs.of_keeps k0 (by decide)) ha hb hz) fun t ⟨hv, kt⟩ => ?_
  refine ⟨?_, (k0.mono (by decide)).trans (kt.mono (by decide))⟩
  rw [k0.gpr .x4 (by decide), k0.gpr .x5 (by decide), k0.gpr .x6 (by decide),
    k0.gpr .x7 (by decide), k0.mem] at hv
  exact hv

end VG.Proof.Ed25519.AArch64
