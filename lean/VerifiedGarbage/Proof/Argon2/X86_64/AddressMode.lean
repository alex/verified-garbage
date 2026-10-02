import VerifiedGarbage.Proof.Argon2.X86_64.AddressModeSteps
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapState

/-! The segment mode is exactly the reviewed Argon2d/i/id addressing predicate. -/

namespace VG.Proof.Argon2.X86_64.AddressMode

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressMode

def value (s : State) : Addr :=
  let kind := s.mem.readW (off (s.gpr .rbp) 112) 64
  let pass := s.mem.readW (off (s.gpr .rbp) 0) 64
  (Divide.mask (decide (kind = 1)) ||| ((Divide.mask (decide (kind = 2)) &&&
    Divide.mask (decide (pass = 0#64))) &&& Divide.mask (decide ((s.gpr .r14).toNat < 2)))) &&& 1

def changed : List Reg := [.rax, .r8, .r9, .r10, .r11]

theorem code_ok (s : State)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8) :
    WP isa code s fun t => t.gpr .r10 = value s ∧ Divide.Keeps changed s t := by
  unfold code
  refine WP.seq ((kind_ok s kindRead).mono ?_)
  rintro a ⟨i, id, ka⟩
  have read : InRegions (a.rd ++ a.wr) (off (a.gpr .rbp) 0) 8 := by
    rw [ka.rd, ka.wr, ka.regs .rbp (by decide)]; exact passRead
  refine WP.seq ((pass_ok a read).mono ?_)
  rintro b ⟨zero, kb⟩
  refine (slice_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [result, kb.regs .r10 (by decide), i, kb.regs .r8 (by decide), id, zero,
    ka.mem, ka.regs .rbp (by decide), kb.regs .r14 (by decide), ka.regs .r14 (by decide)]
  rfl

theorem masks : ∀ a b c d : Bool,
    (Divide.mask a ||| ((Divide.mask b &&& Divide.mask c) &&& Divide.mask d)) &&& 1 =
      (BitVec.ofBool (a || (b && c && d))).setWidth 64 := by decide +kernel

theorem variants : ∀ v : Spec.Argon2.Variant, ∀ a b : Bool,
    (decide (BitVec.ofNat 64 v.code = (1 : Addr)) ||
      (decide (BitVec.ofNat 64 v.code = (2 : Addr)) && a && b)) =
    ((v == .i) || ((v == .id) && a && b)) := by
  intro v
  cases v <;> decide +kernel

theorem value_spec (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    value s = (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 := by
  have passZero : BitVec.ofNat 64 pass = 0#64 ↔ pass = 0 := ReferenceMap.word_zero pass passBound
  unfold value
  rw [kindWord, passWord, sliceWord, masks,
    ReferenceMap.word_nat slice sliceBound]
  simp only [passZero]
  unfold Spec.Argon2.independent
  rw [variants, Bool.beq_eq_decide_eq pass 0]

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass slice : Nat)
    (kindRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 112) 8)
    (passRead : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 0) 8)
    (kindWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code)
    (passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass)
    (sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice)
    (passBound : pass < 2 ^ 64) (sliceBound : slice < 2 ^ 64) :
    WP isa code s fun t => t.gpr .r10 =
      (BitVec.ofBool (Spec.Argon2.independent p pass slice)).setWidth 64 ∧ Divide.Keeps changed s t :=
  (code_ok s kindRead passRead).mono (fun _ h =>
    ⟨h.1.trans (value_spec s p pass slice kindWord passWord sliceWord passBound sliceBound), h.2⟩)

end VG.Proof.Argon2.X86_64.AddressMode
