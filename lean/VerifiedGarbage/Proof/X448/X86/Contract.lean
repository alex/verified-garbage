import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.X86.Target

/-!
# X448 on x86 (32-bit): the contract the proof is written against

Untrusted: everything here is checked by Lean. The facts of the shared
contract (`Spec.X448.x448Contract`) the proof uses, stated for x86; the
shared contract implies it (`sig_implies`, in `Main.lean`).
-/

namespace VG.Proof.X448

open VG VG.X86 in
/-- `vg_x448(out, scalar, point, scratch)`, whose arguments are on the
stack (cdecl). -/
def x448X86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 56⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 56⟩
    let point : Region := ⟨(arg s 2).setWidth 64, 56⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [scalar, point, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 56 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 56 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 56 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := Spec.X448.bytesAt s'.mem ((arg s 0).setWidth 64) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem ((arg s 1).setWidth 64) 56)
      (Spec.X448.bytesAt s.mem ((arg s 2).setWidth 64) 56)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

end VG.Proof.X448

namespace VG.Proof.X448.X86

open VG VG.X86

section
variable (s₀ : State)
/-- The arguments and the regions, on entry. -/
abbrev scR (b : BitVec 32) : Region := ⟨b.setWidth 64, 8192⟩
abbrev outR : Region := ⟨(arg s₀ 0).setWidth 64, 56⟩
abbrev scalarR : Region := ⟨(arg s₀ 1).setWidth 64, 56⟩
abbrev pointR : Region := ⟨(arg s₀ 2).setWidth 64, 56⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [scalarR s₀, pointR s₀, argsR s₀]
  wr : s₀.wr = [outR s₀, scR (arg s₀ 3)]
  out_sc : (outR s₀).Disjoint (scR (arg s₀ 3))
  scalar_sc : (scalarR s₀).Disjoint (scR (arg s₀ 3))
  point_sc : (pointR s₀).Disjoint (scR (arg s₀ 3))
  args_out : (argsR s₀).Disjoint (outR s₀)
  args_sc : (argsR s₀).Disjoint (scR (arg s₀ 3))
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_sc : (retR s₀).Disjoint (scR (arg s₀ 3))
  out_fit : (arg s₀ 0).toNat + 56 ≤ 2 ^ 32
  scalar_fit : (arg s₀ 1).toNat + 56 ≤ 2 ^ 32
  point_fit : (arg s₀ 2).toNat + 56 ≤ 2 ^ 32
  sc_fit : (arg s₀ 3).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem Pre.of (s₀ : State) (h : Proof.X448.x448X86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem argAddr_eq (s : State) (i : Nat) : argAddr s i = addr (s.gpr .esp) (4 + 4 * i) := rfl

/-- An argument slot's address, in the argument region. -/
theorem arg_contains {s : State} (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat}
    (hi : i < 4) : (⟨argAddr s 0, 16⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  VG.Proof.X25519.X86.sub_contains (x := s.gpr .esp) (a := 4) (k := 16) (by omega_using [hfit]) (by omega_using [])
    (by omega_using [hi]) (by decide)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨argsR s₀, by rw [hp.rd]; simp, arg_contains hp.sp_fit hi⟩

/-- An argument, in memory the code has written only in the working space. -/
theorem arg_same {m : Mem} (hf : Frame [scR (arg s₀ 3)] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (arg_contains hp.sp_fit hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

theorem sc_in : scR (arg s₀ 3) ∈ s₀.wr := by rw [hp.wr]; simp

theorem out_in : outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end Pre

end VG.Proof.X448.X86
