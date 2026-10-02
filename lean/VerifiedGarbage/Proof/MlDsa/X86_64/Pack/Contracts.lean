import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode
import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode

/-!
# ML-DSA on x86-64: the contracts of the encodings, for the proofs

For each function of this group, a contract with the facts of its shared
contract (`Spec/MlDsa/Poly.lean`) spelled out for x86-64: the arguments in
their registers, the permitted regions, their disjointness, and the
postcondition. The proofs are written against these, and `Verified.of_correct`
moves them to the shared contracts, which imply them. Also: `sel_ok`, the
branch of `sel` on a 32-bit argument.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (retR pR dArg sub_beq_zero32)

/-- `vg_mldsa_simple_bit_pack(f = rdi, b = esi, out = rdx, len = rcx)`. -/
def simpleBitPackK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ dArg s .rsi ∈ simpleBitPackBounds ∧
    (s.gpr .rcx).toNat = 32 * bitlen (dArg s .rsi) ∧ ∀ i < n, (coeffAt s.mem (s.gpr .rdi) i).toNat ≤ dArg s .rsi
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    simpleBitPack (natPolyAt s.mem (s.gpr .rdi)) (dArg s .rsi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `vg_mldsa_bit_pack(f = rdi, a = esi, b = edx, out = rcx, len = r8)`. -/
def bitPackK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧ (dArg s .rsi, dArg s .rdx) ∈ bitPackParams ∧
    (s.gpr .r8).toNat = 32 * bitlen (dArg s .rsi + dArg s .rdx) ∧ Reduced s.mem (s.gpr .rdi) ∧
    ∀ i < n, -(dArg s .rsi : Int) ≤ modPm (coeffAt s.mem (s.gpr .rdi) i).toNat q ∧
      modPm (coeffAt s.mem (s.gpr .rdi) i).toNat q ≤ dArg s .rdx
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
    bitPack ((polyAt s.mem (s.gpr .rdi)).map fun c => modPm c.val q) (dArg s .rsi) (dArg s .rdx)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32 ∧
    (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

/-- `vg_mldsa_bit_unpack(v = rdi, len = rsi, a = edx, b = ecx, f = r8)`. -/
def bitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [pR (s.gpr .r8)] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (pR (s.gpr .r8)) ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .r8)) ∧
    (dArg s .rdx, dArg s .rcx) ∈ bitPackParams ∧ (s.gpr .rsi).toNat = 32 * bitlen (dArg s .rdx + dArg s .rcx)
  post s s' := PolyIs s'.mem (s.gpr .r8)
    (toRq (bitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (dArg s .rdx) (dArg s .rcx)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    (s₁.gpr .rcx).setWidth 32 = (s₂.gpr .rcx).setWidth 32

/-- `vg_mldsa_unpack_t1(v = rdi, f = rsi)`. -/
def unpackT1K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 320⟩] ∧ s.wr = [pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 320⟩ (pR (s.gpr .rsi)) ∧ (retR s).Disjoint ⟨s.gpr .rdi, 320⟩ ∧
    (retR s).Disjoint (pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi)
    ((simpleBitUnpack (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Branching on a width -/

theorem cmp_ok (r : Reg) (k : BitVec 32) (s : State) :
    WP isa (.block [.alu32 .cmp r (.imm k)]) s fun s' =>
      s'.zf = some (BitVec.setWidth 32 (s.gpr r) - k == 0) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun

/-- The same registers, memory and permissions. -/
def Same (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem sel_ok (r : Reg) (v : Nat) (p e : Prog isa) (s : State) {Q : State → Prop}
    (hp : ∀ s', Same s s' → (s.gpr r).setWidth 32 = BitVec.ofNat 32 v → WP isa p s' Q)
    (he : ∀ s', Same s s' → (s.gpr r).setWidth 32 ≠ BitVec.ofNat 32 v → WP isa e s' Q) :
    WP isa (sel r v p e) s Q := by
  unfold sel
  refine WP.seq (WP.mono (cmp_ok r _ s) fun s' ⟨z, hg, hm, hrd, hwr⟩ => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .e s' = _ from z) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    exact hp s' ⟨hg, hm, hrd, hwr⟩ h
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    exact he s' ⟨hg, hm, hrd, hwr⟩ h

/-- The low 32 bits of `r` are `v` if its argument is. -/
theorem lo_eq {s : State} {r : Reg} {v : Nat} (hv : v < 2 ^ 32) (h : dArg s r = v) :
    (s.gpr r).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; exact h

theorem lo_ne {s : State} {r : Reg} {v : Nat} (h : (s.gpr r).setWidth 32 ≠ BitVec.ofNat 32 v) :
    dArg s r ≠ v := fun e => h (by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← e]; exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm)

theorem lo_of_eq {s : State} {r : Reg} {v : Nat} (h : (s.gpr r).setWidth 32 = BitVec.ofNat 32 v) :
    dArg s r = v % 2 ^ 32 := by
  unfold dArg; rw [h, BitVec.toNat_ofNat]

end VG.Proof.MlDsa.X86_64.Pack
