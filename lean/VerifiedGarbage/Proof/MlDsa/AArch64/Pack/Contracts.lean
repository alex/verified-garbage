import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on AArch64: the contracts of the encodings, for the proofs

For each packing function, a contract with the facts of its shared contract
(`Spec/MlDsa/Poly.lean`) spelled out for AArch64: the arguments in their
registers, the permitted regions, their disjointness, and the postcondition.
The proofs are written against these, and `Verified.of_correct` moves them to
the shared contracts, which imply them. Also: `sel_ok`, the branch of `sel` on
a length.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (Only wp_subImm wp_nil eval_zero eq_zero_iff)
open VG.Proof.MlDsa.Pack

/-- The 32-bit argument in `r`. -/
abbrev wArg (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mldsa_simple_bit_pack(f = x0, b = w1, out = x2, len = x3)`. -/
def simpleBitPackK : Contract isa where
  pre s :=
    s.rd = [polyRegion (s.gpr .x0)] ∧ s.wr = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩] ∧
    (polyRegion (s.gpr .x0)).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩ ∧ wArg s .x1 ∈ simpleBitPackBounds ∧
    (s.gpr .x3).toNat = 32 * bitlen (wArg s .x1) ∧ ∀ i < n, (coeffAt s.mem (s.gpr .x0) i).toNat ≤ wArg s .x1
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .x2) (s.gpr .x3).toNat =
    simpleBitPack (natPolyAt s.mem (s.gpr .x0)) (wArg s .x1)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_bit_pack(f = x0, a = w1, b = w2, out = x3, len = x4)`. -/
def bitPackK : Contract isa where
  pre s :=
    s.rd = [polyRegion (s.gpr .x0)] ∧ s.wr = [⟨s.gpr .x3, (s.gpr .x4).toNat⟩] ∧
    (polyRegion (s.gpr .x0)).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧ (wArg s .x1, wArg s .x2) ∈ bitPackParams ∧
    (s.gpr .x4).toNat = 32 * bitlen (wArg s .x1 + wArg s .x2) ∧ Reduced s.mem (s.gpr .x0) ∧
    ∀ i < n, -(wArg s .x1 : Int) ≤ modPm (coeffAt s.mem (s.gpr .x0) i).toNat q ∧
      modPm (coeffAt s.mem (s.gpr .x0) i).toNat q ≤ wArg s .x2
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
    bitPack ((polyAt s.mem (s.gpr .x0)).map fun c => modPm c.val q) (wArg s .x1) (wArg s .x2)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_bit_unpack(v = x0, len = x1, a = w2, b = w3, f = x4)`. -/
def bitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [polyRegion (s.gpr .x4)] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ (polyRegion (s.gpr .x4)) ∧
    (wArg s .x2, wArg s .x3) ∈ bitPackParams ∧ (s.gpr .x1).toNat = 32 * bitlen (wArg s .x2 + wArg s .x3)
  post s s' := PolyIs s'.mem (s.gpr .x4)
    (toRq (bitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (wArg s .x2) (wArg s .x3)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_mldsa_unpack_t1(v = x0, f = x1)`. -/
def unpackT1K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 320⟩] ∧ s.wr = [polyRegion (s.gpr .x1)] ∧
    Region.Disjoint ⟨s.gpr .x0, 320⟩ (polyRegion (s.gpr .x1))
  post s s' := PolyIs s'.mem (s.gpr .x1)
    ((simpleBitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .x0) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-! ## Branching on a length -/

/-- `sel r v p e` runs `p` if `r = v`, else `e`, after writing `x9`. -/
theorem sel_ok {r : Reg} {v : Nat} (hv : v < 4096) {p e : Prog isa} {s : State} {Q : State → Prop}
    (hp : ∀ s', Only [.x9] s s' → (s.gpr r).toNat = v → WP isa p s' Q)
    (he : ∀ s', Only [.x9] s s' → (s.gpr r).toNat ≠ v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  refine WP.seq (wp_subImm hv fun s₁ o₁ e₁ => wp_nil ?_)
  have hr := (s.gpr r).isLt
  have hz : isa.eval (.zero .x .x9) s₁ = some (decide ((s.gpr r).toNat = v)) := by
    rw [eval_zero, eq_zero_iff, e₁, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v) (by omega)]
    congr 1
    apply decide_eq_decide.mpr
    omega
  refine WP.ite _ hz (fun h => hp s₁ o₁ (of_decide_eq_true h)) (fun h => he s₁ o₁ (of_decide_eq_false h))

/-- The arguments of `BitPack` and `BitUnpack`, by the length. -/
theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, Mem.read]
  rfl

end VG.Proof.MlDsa.AArch64.Pack
