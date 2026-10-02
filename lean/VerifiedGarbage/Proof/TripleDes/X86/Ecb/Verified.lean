import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Correct
import VerifiedGarbage.Proof.TripleDes.X86.Ecb.ConstantTime

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def wideContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { contract d with
    pre := fun s =>
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩
    let buf : Region := ⟨addr32 (arg s 3), 1024⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key] ∧ s.wr = [data, buf, args] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint data ∧ ret.Disjoint buf ∧ stack.Disjoint key ∧ stack.Disjoint data ∧
      stack.Disjoint buf ∧ (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region := [⟨addr32 (arg s 0), 384⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩, ⟨addr32 (arg s 3), 1024⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.TripleDes.X86.Ecb.contract, VG.Proof.TripleDes.X86.Ecb.wideContract,
    VG.Proof.TripleDes.X86.Ecb.narrowRd, VG.Proof.TripleDes.X86.Ecb.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wide_pre (d : Spec.TripleDes.Direction) (s : State) (h : (wideContract d).pre s) :
    (contract d).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩, ⟨0x4004, 16⟩]

theorem wide_implies (d : Spec.TripleDes.Direction) :
    (wideContract d).Implies (Spec.TripleDes.ecbContract abi d 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below] at h
    sig_split h
    sig_reduce [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
    sig_simp [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [Taint.sub_setWidth (by omega)]; simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
  · sig_implies_pub [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
  · sig_implies_sat [Spec.TripleDes.ecbContract, Spec.TripleDes.ecbSig, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ecb_constantTime (d : Spec.TripleDes.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.TripleDes.X86.Ecb.ecb d) := by
  cases d
  · exact ecbEncrypt_constantTime _ _ (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp)
  · exact ecbDecrypt_constantTime _ _ (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp)

theorem ecb_verified (d : Spec.TripleDes.Direction) :
    Verified target (Impl.TripleDes.X86.Ecb.ecb d) (Spec.TripleDes.ecbContract abi d 16) := by
  have hsat := (wide_implies d).sat_left
  have narrowSat : ∃ s, (contract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre d s hs⟩
  apply Verified.of_implies _ (wide_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (ecb_correct d) (ecb_constantTime d) (.refl narrowSat))
    narrowRd narrowWr (wide_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem encrypt_verified : Verified target Impl.TripleDes.X86.Ecb.encrypt (Spec.TripleDes.ecbEncryptContract abi 16) := ecb_verified .encrypt
theorem decrypt_verified : Verified target Impl.TripleDes.X86.Ecb.decrypt (Spec.TripleDes.ecbDecryptContract abi 16) := ecb_verified .decrypt

end VG.Proof.TripleDes.X86.Ecb
