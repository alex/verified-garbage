import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeader
import VerifiedGarbage.Proof.Argon2.AddressInput

/-! The prepared input agrees with RFC 9106's seven public address words. -/

namespace VG.Proof.Argon2.X86_64.AddressHeader

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressHeader

def input (s : State) : Block :=
  zeroBlock |>.set 0 (value s 0) |>.set 1 (value s 1) |>.set 2 (value s 2)
    |>.set 3 (value s 3) |>.set 4 (value s 4) |>.set 5 (value s 5) |>.set 6 (value s 6)

theorem headerMem_block (s : State) (p : Addr) (zero : blockAt s.mem p = zeroBlock) :
    blockAt (headerMem s p 7) p = input s := by
  rw [headerMem, blockAt_write_nat _ p 6 (by decide),
    headerMem, blockAt_write_nat _ p 5 (by decide),
    headerMem, blockAt_write_nat _ p 4 (by decide),
    headerMem, blockAt_write_nat _ p 3 (by decide),
    headerMem, blockAt_write_nat _ p 2 (by decide),
    headerMem, blockAt_write_nat _ p 1 (by decide),
    headerMem, blockAt_write_nat _ p 0 (by decide), headerMem, zero]
  rfl

theorem code_ok (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (zero : blockAt s.mem (s.gpr .rdi) = zeroBlock) :
    WP isa code s fun t => blockAt t.mem (s.gpr .rdi) = input s ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  refine (prefix_ok 7 (by decide) s reads write sep).mono ?_
  rintro t ⟨mem, frame, keeps, mx⟩
  exact ⟨by rw [mem]; exact headerMem_block s _ zero, frame, keeps, mx⟩

structure Words (p : Params) (pass lane slice counter : Nat) (s : State) : Prop where
  passWord : s.mem.readW (off (s.gpr .rbp) 0) 64 = BitVec.ofNat 64 pass
  laneWord : s.gpr .rbx = BitVec.ofNat 64 lane
  sliceWord : s.gpr .r14 = BitVec.ofNat 64 slice
  blocksWord : s.mem.readW (off (s.gpr .rbp) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .rbp) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .rbp) 112) 64 = BitVec.ofNat 64 p.variant.code
  counterWord : s.mem.readW (off (s.gpr .rbp) 8) 64 = BitVec.ofNat 64 counter

theorem input_spec (p : Params) (pass lane slice counter : Nat) (s : State)
    (h : Words p pass lane slice counter s) :
    input s = Proof.Argon2.addressInput p pass lane slice counter := by
  simp (config := {decide := true}) only [input, value, frameOffset,
    ite_true, ite_false, h.passWord, h.laneWord, h.sliceWord, h.blocksWord,
    h.passesWord, h.variantWord, h.counterWord, Proof.Argon2.addressInput]

theorem code_spec_ok (p : Params) (pass lane slice counter : Nat) (s : State)
    (reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr)
    (sep : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩)
    (zero : blockAt s.mem (s.gpr .rdi) = zeroBlock)
    (words : Words p pass lane slice counter s) :
    WP isa code s fun t =>
      blockAt t.mem (s.gpr .rdi) = Proof.Argon2.addressInput p pass lane slice counter ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ CopyKeeps s t ∧ t.mxcsr = s.mxcsr :=
  (code_ok s reads write sep zero).mono (fun _ h =>
    ⟨h.1.trans (input_spec p pass lane slice counter s words), h.2⟩)

end VG.Proof.Argon2.X86_64.AddressHeader
