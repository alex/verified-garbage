import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith

/-!
# ML-DSA signing on AArch64: the layout registers

The proof of `vg_mldsa*_sign` uses the framework of
`Proof/MlDsa/AArch64/Call/`: the function keeps the addresses of its buffers
in `bases`, which two runs agree on (`SameB`, `LRel`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call

/-- The registers the function keeps the addresses of its buffers in. -/
abbrev bases : List Reg := [.x23, .x25, .x26, .x27, .x28]

theorem bases_pres : ∀ r ∈ bases, r ∈ preserved ∧ r ≠ .x30 := by decide

theorem bases_kept : ∀ r ∈ bases, r ∈ keptRegs := by decide

/-- The buffers of a layout are in the registers `bases`. -/
abbrev LayOk : List (Reg × Nat) → Prop := LayIn bases

/-- Two states whose layout registers and stack pointer agree. -/
abbrev SameB : State → State → Prop := SameIn bases

/-! ## Two runs in the same layout -/

/-- Two states in the same layout (whose buffers are in `bases`), with the
same stack pointer. -/
structure LRel (S : Nat) (rbs wbs : List (Reg × Nat)) (x y : State) : Prop where
  lx : Lay S rbs wbs x
  ly : Lay S rbs wbs y
  regs : ∀ r ∈ bases, x.gpr r = y.gpr r
  sp : x.sp = y.sp
  ok : LayOk (rbs ++ wbs)

theorem LRel.pa {S : Nat} {rbs wbs : List (Reg × Nat)} {x y : State} (h : LRel S rbs wbs x y) {p : Ptr}
    (hp : p.1 ∈ bases) : pa x p = pa y p := by
  simp only [VG.Proof.MlDsa.AArch64.pa, h.regs _ hp]

theorem LRel.post {S : Nat} {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region}
    (h : LRel S rbs wbs x y) (hx : PostB S x x' W₁) (hy : PostB S y y' W₂) : LRel S rbs wbs x' y' :=
  ⟨h.lx.post hx, h.ly.post hy, fun r hr => by
    rw [hx.bs r (bases_kept r hr), hy.bs r (bases_kept r hr), h.regs r hr], by rw [hx.sp, hy.sp, h.sp], h.ok⟩

end VG.Proof.MlDsa.AArch64.Sign
