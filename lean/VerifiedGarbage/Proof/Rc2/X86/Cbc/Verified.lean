import VerifiedGarbage.Proof.Rc2.X86.Cbc.Correct
import VerifiedGarbage.Proof.Rc2.X86.Cbc.ConstantTime

namespace VG.Proof.Rc2.X86.Cbc
open VG VG.X86

def wideContract (d : Spec.Rc2.Direction) : Contract isa :=
  { contract d with
    pre := fun s =>
    let key : Region := ⟨addr32 (arg s 0), 128⟩
    let iv : Region := ⟨addr32 (arg s 1), 8⟩
    let data : Region := ⟨addr32 (arg s 2), 8 * (arg s 3).toNat⟩
    let buf : Region := ⟨addr32 (arg s 4), 512⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key] ∧ s.wr = [iv, data, buf, args] ∧ key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      iv.Disjoint data ∧ iv.Disjoint buf ∧ data.Disjoint buf ∧
      args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region :=
  [⟨addr32 (arg s 0), 128⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨addr32 (arg s 1), 8⟩, ⟨addr32 (arg s 2), 8 * (arg s 3).toNat⟩, ⟨addr32 (arg s 4), 512⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.Rc2.X86.Cbc.contract, VG.Proof.Rc2.X86.Cbc.wideContract,
    VG.Proof.Rc2.X86.Cbc.narrowRd, VG.Proof.Rc2.X86.Cbc.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wide_pre (d : Spec.Rc2.Direction) (s : State) (h : (wideContract d).pre s) :
    (contract d).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

def satState : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6009 then 0x20 else if a = 0x600d then 0x30 else if a = 0x6015 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 512⟩, ⟨0x6004, 20⟩]

theorem wide_implies (d : Spec.Rc2.Direction) :
    (wideContract d).Implies (Spec.Rc2.cbcContract abi d 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below] at h
    sig_split h
    sig_reduce [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
    sig_simp [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [Taint.sub_setWidth (by omega)]; simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
  · sig_implies_pub [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
  · sig_implies_sat [Spec.Rc2.cbcContract, Spec.Rc2.cbcSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem cbc_verified (d : Spec.Rc2.Direction) :
    Verified target (Impl.Rc2.X86.Cbc.cbc d) (Spec.Rc2.cbcContract abi d 16) := by
  have hsat := (wide_implies d).sat_left
  have narrowSat : ∃ s, (contract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre d s hs⟩
  apply Verified.of_implies _ (wide_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (cbc_body_correct d) (cbc_constantTime d) (.refl narrowSat))
    narrowRd narrowWr (wide_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem encrypt_verified : Verified target Impl.Rc2.X86.Cbc.encrypt (Spec.Rc2.cbcEncryptContract abi 16) := cbc_verified .encrypt
theorem decrypt_verified : Verified target Impl.Rc2.X86.Cbc.decrypt (Spec.Rc2.cbcDecryptContract abi 16) := cbc_verified .decrypt

end VG.Proof.Rc2.X86.Cbc
