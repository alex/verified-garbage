import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# ML-KEM on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. For each function, a
contract with the facts of its shared contract (`Spec/MlKem/Poly.lean`,
`Spec/MlKem/Contract.lean`) spelled out for x86-64: the arguments in their
registers, the permitted regions, their disjointness, and the
postcondition. The proofs are written against these, and callers use them
(`WP.call`); `Verified.of_correct` moves a proof to the shared contract,
which implies it (`sig_implies`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64
open VG.Spec.MlKem

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A polynomial, at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

/-- `vg_mlkem_add(f = rdi, g = rsi)` and `vg_mlkem_sub(f = rdi, g = rsi)`:
`f` becomes `t f g`. -/
def accK (t : Poly → Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rdi)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi) ∧ Reduced s.mem (s.gpr .rsi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_encode12(f = rdi, out = rsi)`. -/
def encode12K : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rsi, 384⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rsi, 384⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rsi, 384⟩ ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rsi) 384 = encode12 (polyAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_decode12(b = rdi, f = rsi)`. -/
def decode12K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 384⟩] ∧ s.wr = [pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 384⟩ (pR (s.gpr .rsi)) ∧ (retR s).Disjoint ⟨s.gpr .rdi, 384⟩ ∧
    (retR s).Disjoint (pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi) (decode12 (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 384))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_cbd2(b = rdi, f = rsi)`. -/
def cbd2K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 128⟩] ∧ s.wr = [pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 128⟩ (pR (s.gpr .rsi)) ∧ (retR s).Disjoint ⟨s.gpr .rdi, 128⟩ ∧
    (retR s).Disjoint (pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi) (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 128))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The width `d`, a `u32` argument in `r`. -/
abbrev dArg (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mlkem_compress_encode(f = rdi, d = esi, out = rdx, len = rcx)`. -/
def compressEncodeK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ ∧ dArg s .rsi ∈ compressWidths ∧
    (s.gpr .rcx).toNat = 32 * dArg s .rsi ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    compressEncode (dArg s .rsi) (polyAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `vg_mlkem_decode_decompress(b = rdi, len = rsi, d = edx, f = rcx)`. -/
def decodeDecompressK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [pR (s.gpr .rcx)] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (retR s).Disjoint (pR (s.gpr .rcx)) ∧
    dArg s .rdx ∈ compressWidths ∧ (s.gpr .rsi).toNat = 32 * dArg s .rdx
  post s s' := PolyIs s'.mem (s.gpr .rcx)
    (decodeDecompress (dArg s .rdx) (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

/-! ## Constant time -/

/-- The taint in which the registers `rs` are public, and the low halves of
`los` (public 32-bit arguments). -/
def regsLo (rs los : List Reg) : X86_64.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, lo := RegSet.ofList los }

theorem agree_regsLo {rs los : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hl : ∀ r ∈ los, (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32) :
    X86_64.Taint.Agree (regsLo rs los) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  ok _ h := by cases h
  slots _ h := by cases h
  lo r hr := hl r (RegSet.mem_ofList.mp hr)

/-! ## Satisfiability -/

theorem read_zero (a : Addr) : ∀ n, Mem.read (fun _ => 0) a n = 0
  | 0 => rfl
  | n + 1 => by
    rw [Mem.read, read_zero (a + 1) n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    have (w : Nat) : (0 : BitVec w).toNat = 0 := BitVec.toNat_zero
    rw [this, this, this]
    rfl

/-- In memory of zeros, every polynomial is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun _ _ => by
  simp only [coeffAt, Mem.readW, read_zero]
  decide

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
syntax "mlkem_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| mlkem_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

end VG.Proof.MlKem.X86_64
