import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlKem.AArch64.KgEnd
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono

/-!
# ML-DSA on AArch64: the blocks between calls

What the top-level functions' own instructions between their calls do, in
their layout: byte stores (`setB_ok`), copies of 32 bytes (`copyP_ok`,
ML-KEM's `copy32`), and the AND of a callee's result into `x24` (`and24_ok`).
-/

namespace VG.Proof.MlDsa.AArch64

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_strb)
open VG.Spec.Sha3 (bytesAt)

/-! ## 32-bit operations -/

theorem only_write32 (s : State) (d : Reg) (v : BitVec 32) : Only [d] s (s.write .w d v) :=
  ⟨fun r h => by simp only [List.mem_singleton] at h; simp [State.write, h], rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem write32_gpr (s : State) (d : Reg) (v : BitVec 32) : (s.write .w d v).gpr d = v.setWidth 64 := by
  simp [State.write]

theorem wp_and32 {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = ((s.gpr n).setWidth 32 &&& (s.gpr m).setWidth 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .w d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 &&& (s.gpr m).setWidth 32))
    (by simp [exec, State.read]) (k _ (only_write32 _ _ _) (write32_gpr _ _ _))

theorem and24_ok (s : State) :
    WP isa (.block and24) s fun s' => Only [.x24] s s' ∧
      s'.gpr .x24 = ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32).setWidth 64 :=
  wp_and32 fun _ h e => wp_nil ⟨h, e⟩

/-! ## Byte stores -/

theorem imm8 (v : Nat) : ((BitVec.ofNat 16 v).setWidth 64).setWidth 8 = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem bytesAt_one (m : Mem) (a : Addr) : bytesAt m a 1 = [m a] := by
  simp [Spec.Sha3.bytesAt, BitVec.add_zero]

theorem writeW8_self (m : Mem) (a : Addr) (b : Byte) : m.writeW a b a = b := by
  rw [Proof.MlKem.writeW8_apply, Proof.MlDsa.KeyGen.ifp rfl]

theorem ne_x9 {r : Reg} (h : r ∈ keptRegs) : r ≠ .x9 := by
  intro e; rw [e] at h; revert h; decide

/-- The byte `v` to `p`. -/
theorem setB_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {p : Ptr} {v : Nat}
    (ho : p.2 < 4096) (hw : inB wbs p 1 = true) (hb : p.1 ∈ keptRegs) :
    WP isa (.block (setB p v)) s fun s' => PPostB S s s' [(p, 1)] ∧ Keep [.x9] s s' ∧
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) := by
  have h9 := ne_x9 hb
  refine wp_movz fun s₁ h₁ e₁ => wp_strb (a := pa s p) ho (by rw [h₁.get p.1 (by simpa using h9)])
    (by rw [h₁.wr]; exact L.inW hw) fun s₂ h₂ => wp_nil ?_
  have m₂ : s₂.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) := by rw [h₂.mem, e₁, h₁.mem, imm8 v]
  have k₂ : Keep [.x9] s s₂ := (h₁.keep.trans h₂.keep).mono (by simp)
  refine ⟨postB_of_keep k₂ (by decide) ?_, k₂, m₂⟩
  rw [m₂]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-! ## Copies of 32 bytes -/

/-- The 32 bytes at `src` can be copied to `dst`. -/
def copyPChk (rbs wbs : List (Reg × Nat)) (dst src : Ptr) : Bool :=
  decide (src.2 % 8 = 0 ∧ src.2 + 32 ≤ 32768) && decide (dst.2 % 8 = 0 ∧ dst.2 + 32 ≤ 32768) &&
    sepB rbs wbs src 32 dst 32 && inB wbs dst 32

theorem copyP_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {dst src : Ptr}
    (hc : copyPChk rbs wbs dst src = true) :
    WP isa (.block (Impl.MlKem.AArch64.copy32 src.1 src.2 dst.1 dst.2)) s fun s' =>
      PPostB S s s' [(dst, 32)] ∧ Keep [.x9] s s' ∧ bytesAt s'.mem (pa s dst) 32 = bytesAt s.mem (pa s src) 32 := by
  simp only [copyPChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hso, hdo⟩, hsep⟩, hw⟩ := hc
  have i1 := (sepB_spec hsep).1
  have i2 := (sepB_spec hsep).2.1
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr src.1) (D := s.gpr dst.1)
    (ne_x9 (L.ptrBs i1)) (ne_x9 (L.ptrBs i2)) hso hdo (L.disj hsep) rfl rfl (L.cR i1) (L.cW hw))
    fun s' ⟨k, f, b⟩ => ⟨postB_of_keep k (by decide) f, k, b⟩

end VG.Proof.MlDsa.AArch64
