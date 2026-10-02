import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Loop
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on 32-bit ARM: the contracts of the encodings, for the proofs

For each function of this group, what its shared contract
(`Spec/MlDsa/Poly.lean`) requires, spelled out for 32-bit ARM (`SbpPre`,
`BpPre`, `BuPre`, `T1Pre`, from `pre_of`); the branch of `sel` on a width
(`sel_ok`); and the frame of `bitPack` and `bitUnpack`, which saves `r4` in
the 4 bytes below the stack pointer that their contracts reserve
(`pushed4_mem`, `popped4`).
-/

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Proof.MlKem.Arm (cmp_z)
open VG.Proof.MlDsa.Pack

/-! ## The preconditions -/

/-- `vg_mldsa_simple_bit_pack(f = r0, b = r1, out = r2, len = r3)`. -/
structure SbpPre (s : State) : Prop where
  rd : s.rd = [polyRegion (State.addr (s.gpr .r0))]
  wr : s.wr = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩]
  disj : (polyRegion (State.addr (s.gpr .r0))).Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  fitF : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  fitO : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  b : (s.gpr .r1).toNat ∈ simpleBitPackBounds
  len : (s.gpr .r3).toNat = 32 * bitlen (s.gpr .r1).toNat
  le : ∀ i < n, (coeffAt s.mem (State.addr (s.gpr .r0)) i).toNat ≤ (s.gpr .r1).toNat

theorem SbpPre.of {s : State} (h : (simpleBitPackContract Arm.abi).pre s) : SbpPre s := by
  sig_pre [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The 4 bytes below the stack pointer. -/
abbrev below4 (s : State) : Region := ⟨State.addr s.sp - 4, 4⟩

/-- `vg_mldsa_bit_pack(f = r0, a = r1, b = r2, out = r3, len = [sp])`. -/
structure BpPre (s : State) : Prop where
  sp4 : 4 ≤ s.sp.toNat
  rd : s.rd = [polyRegion (State.addr (s.gpr .r0)), ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩]
  disj : (polyRegion (State.addr (s.gpr .r0))).Disjoint ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
  bF : (below4 s).Disjoint (polyRegion (State.addr (s.gpr .r0)))
  bO : (below4 s).Disjoint ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
  fitF : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  fitO : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  ab : ((s.gpr .r1).toNat, (s.gpr .r2).toNat) ∈ bitPackParams
  len : (stackArg s 0).toNat = 32 * bitlen ((s.gpr .r1).toNat + (s.gpr .r2).toNat)
  red : Reduced s.mem (State.addr (s.gpr .r0))
  bnd : ∀ i < n, -((s.gpr .r1).toNat : Int) ≤ modPm (coeffAt s.mem (State.addr (s.gpr .r0)) i).toNat q ∧
    modPm (coeffAt s.mem (State.addr (s.gpr .r0)) i).toNat q ≤ (s.gpr .r2).toNat

theorem BpPre.of {s : State} (h : (bitPackContract Arm.abi 4).pre s) : BpPre s := by
  sig_pre [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, -, h5, h6, -, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h0, h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- `vg_mldsa_bit_unpack(v = r0, len = r1, a = r2, b = r3, f = [sp])`. -/
structure BuPre (s : State) : Prop where
  sp4 : 4 ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨stackArgAddr s 0, 4⟩]
  wr : s.wr = [polyRegion (State.addr (stackArg s 0))]
  disj : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ (polyRegion (State.addr (stackArg s 0)))
  bV : (below4 s).Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  bP : (below4 s).Disjoint (polyRegion (State.addr (stackArg s 0)))
  fitV : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fitP : (stackArg s 0).toNat + 1024 ≤ 2 ^ 32
  ab : ((s.gpr .r2).toNat, (s.gpr .r3).toNat) ∈ bitPackParams
  len : (s.gpr .r1).toNat = 32 * bitlen ((s.gpr .r2).toNat + (s.gpr .r3).toNat)

theorem BuPre.of {s : State} (h : (bitUnpackContract Arm.abi 4).pre s) : BuPre s := by
  sig_pre [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, -, h5, h6, -, h7, h8, h9, h10⟩ := h
  exact ⟨h0, h1, h2, h3, h5, h6, h7, h8, h9, h10⟩

/-- `vg_mldsa_unpack_t1(v = r0, f = r1)`. -/
structure T1Pre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 320⟩]
  wr : s.wr = [polyRegion (State.addr (s.gpr .r1))]
  disj : Region.Disjoint ⟨State.addr (s.gpr .r0), 320⟩ (polyRegion (State.addr (s.gpr .r1)))
  fitV : (s.gpr .r0).toNat + 320 ≤ 2 ^ 32
  fitP : (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32

theorem T1Pre.of {s : State} (h : (unpackT1Contract Arm.abi).pre s) : T1Pre s := by
  sig_pre [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem mem_bitPackParams {a b : Nat} (h : (a, b) ∈ bitPackParams) :
    (a = 2 ∧ b = 2) ∨ (a = 4 ∧ b = 4) ∨ (a = 4095 ∧ b = 4096) ∨ (a = 131071 ∧ b = 131072) ∨
      (a = 524287 ∧ b = 524288) := by
  simp only [bitPackParams, d, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  exact h

/-! ## Branching on a width -/

/-- The same registers, memory, regions and stack pointer. -/
def Same (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem cmp_ok (r : Reg) (v : Nat) (he : encodable (BitVec.ofNat 32 v) = true) (s : State) :
    WP isa (.block [.cmp r (.imm (BitVec.ofNat 32 v))]) s fun s' =>
      s'.z = (s.gpr r - BitVec.ofNat 32 v == 0) ∧ Same s s' := by
  run_block [he, Same, and_true]

theorem sel_ok (r : Reg) (v : Nat) (hv : v < 2 ^ 32) (he : encodable (BitVec.ofNat 32 v) = true)
    (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', Same s s' → (s.gpr r).toNat = v → WP isa p s' Q)
    (hn : ∀ s', Same s s' → (s.gpr r).toNat ≠ v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (cmp_ok r v he s) fun s' ⟨z, hs⟩ => ?_)
  refine WP.ite (M := isa) (decide ((s.gpr r).toNat = v)) (by
    show some s'.z = _
    rw [z, cmp_z _ _ hv]) (fun h => hp s' hs (of_decide_eq_true h)) (fun h => hn s' hs (of_decide_eq_false h))

/-! ## The frame of `r4` -/

theorem addr_sub {sp : BitVec 32} {n : Nat} (h : n ≤ sp.toNat) :
    State.addr (sp - BitVec.ofNat 32 n) = State.addr sp - BitVec.ofNat 64 n := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt (a := n) (by omega),
    Nat.mod_eq_of_lt (a := sp.toNat) (by omega)]
  omega

theorem pushed4_sp (s : State) : (pushed [.r4] s).sp = s.sp - 4 := rfl

theorem pushed4_mem {s : State} (hsp : 4 ≤ s.sp.toNat) :
    (pushed [.r4] s).mem = s.mem.writeW (State.addr s.sp - 4) (s.gpr .r4) := by
  show s.mem.writeW (State.addr (s.sp - BitVec.ofNat 32 4)) (s.gpr .r4) = _
  rw [addr_sub hsp]; rfl

theorem pushed4_frame {s : State} (hsp : 4 ≤ s.sp.toNat) : Frame [below4 s] s.mem (pushed [.r4] s).mem := by
  rw [pushed4_mem hsp]
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- What the pop of the frame restores: `r4`, from the frame, which the body
left as the push wrote it, and the stack pointer. -/
theorem popped4 {s s₂ : State} (hsp : 4 ≤ s.sp.toNat) (h₂ : s₂.sp = s.sp - 4)
    (hr4 : s₂.mem.readW (State.addr s.sp - 4) 32 = s.gpr .r4) :
    (popped .r4 4 s₂).gpr .r4 = s.gpr .r4 ∧ (popped .r4 4 s₂).sp = s.sp := by
  refine ⟨?_, ?_⟩
  · show (s₂.setReg .r4 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r4 = _
    rw [RegUpd.gpr_setReg_self, h₂, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, addr_sub hsp]
    exact hr4
  · rw [popped_sp, h₂]; exact BitVec.sub_add_cancel _ _

end VG.Proof.MlDsa.Arm.Pack
