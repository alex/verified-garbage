import VerifiedGarbage.Impl.Ed25519.X86_64.MulAdd
import VerifiedGarbage.Proof.X25519.X86_64.Ops
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-! The eight product words represent the full unsigned product. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64

def wideValue (s : State) : Nat :=
  val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
    2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)

theorem wideAccumulate_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat}
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (wideAccumulate a b)) s fun t =>
      wideValue t = val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
        fe s.mem base a * fe s.mem base b ∧ Keeps clob s t := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [show wideAccumulate a b = row a b 0 ++ (row a b 1 ++ (row a b 2 ++ row a b 3)) by
    simp only [wideAccumulate, List.append_assoc]]
  rw [WP.block_append_iff, row0]
  refine WP.mono (rowR_ok hs (by omega) hb (by decide)) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, row1]
  refine WP.mono (rowR_ok hs₁ (by omega) hb (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff, row2]
  refine WP.mono (rowR_ok hs₂ (by omega) hb (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [row3]
  refine WP.mono (rowR_ok hs₃ (by omega) hb (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  refine ⟨?_, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide)) |>.trans (k4.mono (by decide))⟩
  change val4 (s₄.gpr .r8) (s₄.gpr .r9) (s₄.gpr .r10) (s₄.gpr .r11) +
    2 ^ 256 * val4 (s₄.gpr .r12) (s₄.gpr .r13) (s₄.gpr .r14) (s₄.gpr .r15) = _
  rw [fe_mul_expand]
  -- Every row read the same memory.
  rw [k1.2.1] at e2
  rw [k2.2.1, k1.2.1] at e3
  rw [k3.2.1, k2.2.1, k1.2.1] at e4
  -- The registers along the way.
  have r1 := g k2 .r8 (by decide); have r2 := g k3 .r8 (by decide); have r3 := g k4 .r8 (by decide)
  have q2 := g k3 .r9 (by decide); have q3 := g k4 .r9 (by decide); have q4 := g k4 .r10 (by decide)
  simp only [val4] at e1 e2 e3 e4 ⊢
  rw [r3, r2, r1, q3, q2, q4]
  omega_using [e1, e2, e3, e4]

/-- Reuse the checked four-KiB arithmetic within Ed25519's larger scratch
argument. Execution is lifted by the framework's memory-permission theorem. -/
theorem wideAccumulate8192_ok {s : State} {base : Addr}
    (hp : s.gpr .rdi = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) {a b : Nat} (ha : Slot a) (hb : Slot b) :
    WP isa (.block (wideAccumulate a b)) s fun t =>
      wideValue t = val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
        fe s.mem base a * fe s.mem base b ∧ Keeps clob s t := by
  let narrow := s.withRegions s.rd [⟨base, 4096⟩]
  have hs : Scr narrow base := ⟨hp, List.mem_singleton_self _, by omega⟩
  obtain ⟨tr, t, he, hv, hk⟩ := wideAccumulate_ok hs ha hb
  have cw : Covers [⟨base, 4096⟩] s.wr := by
    apply Covers.of_sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨base, 8192⟩, hw, 0, (BitVec.add_zero base).symm, by change 0 + 4096 ≤ 8192; decide⟩
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, hv, hk.1, hk.2.1, rfl, rfl⟩
  have e := VG.X86_64.Exec.widen he (Covers.append (fun _ _ h => h) cw) cw
  simpa only [narrow, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_self] using e

end VG.Proof.Ed25519.X86_64
