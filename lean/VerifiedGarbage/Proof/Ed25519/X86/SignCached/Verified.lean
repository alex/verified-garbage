import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Entry
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.Ed25519.X86.SignCached
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarLit
import VerifiedGarbage.Proof.Ed25519.X86.ScalarBaseLit
import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CT

/-! Merged from `Proof.Ed25519.X86.SignCached.Contract`. -/
section
/-! Merged from `Proof.Ed25519.X86.SignCached.Sat`. -/
section
/-! A satisfiability witness with a matching seed and cached public key. -/
namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def satSeed : List Byte := Spec.Ed25519.bytesAt (fun _ => 0) 0x2000 32
def satKey : List Byte := Spec.Ed25519.publicKey satSeed

theorem satKey_length : satKey.length = 32 := by
  simp only [satKey, Spec.Ed25519.publicKey, Spec.Ed25519.encodePoint, Spec.Ed25519.encodeLE,
    List.length_map, List.length_range]

def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 then 0 else if a.toNat < 0x3020 then satKey[a.toNat - 0x3000]?.getD 0
  else if a = 0x9005 then 0x10 else if a = 0x9009 then 0x20 else
    if a = 0x900d then 0x30 else if a = 0x9011 then 0x40 else if a = 0x9019 then 0x50 else 0

theorem sat_seed : Spec.Ed25519.bytesAt satMem 0x2000 32 = satSeed := by
  unfold satSeed Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  unfold satMem
  rw [ha]
  simp only [show 0x2000 + i < 0x3000 from by omega, ite_true]

theorem sat_key : Spec.Ed25519.bytesAt satMem 0x3000 32 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 32 := by simpa only [Spec.Ed25519.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed25519.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ 0x3000 + i < 0x3000 from by omega, ite_false, show 0x3000 + i < 0x3020 from by omega, ite_true, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

def satState : State where
  gpr r := match r with | .esp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x5000, 8192⟩, ⟨0x9004, 24⟩]

theorem sat : ∃ s, (Spec.Ed25519.signCachedContract X86.abi 280).pre s := by
  refine ⟨satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, satState]
    sig_and_intros
    · decide +kernel
    · decide +kernel
    · change Spec.Ed25519.bytesAt satMem ((arg satState 2).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt satMem ((arg satState 1).setWidth 64) 32)
      have a1 : arg satState 1 = 0x2000 := by decide
      have a2 : arg satState 2 = 0x3000 := by decide
      rw [a1, a2]
      change Spec.Ed25519.bytesAt satMem 0x3000 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt satMem 0x2000 32)
      rw [sat_seed, sat_key]
      rfl

end VG.Proof.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def signWide : Contract isa := { signCachedLocal with
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let seed : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let pk : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let msg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 280, 280⟩
    s.rd = [seed, pk, msg] ∧ s.wr = [out, scr, args] ∧
      out.Disjoint seed ∧ out.Disjoint pk ∧ out.Disjoint msg ∧ out.Disjoint args ∧
      out.Disjoint scr ∧ stk.Disjoint out ∧ ret.Disjoint out ∧
      seed.Disjoint scr ∧ pk.Disjoint scr ∧ msg.Disjoint scr ∧ args.Disjoint scr ∧
      ret.Disjoint seed ∧ ret.Disjoint pk ∧ ret.Disjoint msg ∧ ret.Disjoint scr ∧
      stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint msg ∧ stk.Disjoint scr ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 8192 ≤ 2 ^ 32 ∧
      280 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) }

theorem signWide_pre (s : State) (h : signWide.pre s) :
    signCachedLocal.pre (s.withRegions (signRd s) (signWr s)) := by
  simp only [signCachedLocal, signRd, signWr, arg_withRegions, argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem]
  exact ⟨True.intro, True.intro, h.2.2⟩

theorem signWide_implies : signWide.Implies (Spec.Ed25519.signCachedContract X86.abi 280) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, signWide, signCachedLocal,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  sat := sat

end VG.Proof.Ed25519.X86.SignCached
end

/-! Merged from `Proof.Ed25519.X86.SignCached.Lit`. -/
section
namespace VG.Impl.Ed25519.X86.SignCached
materialize_code code
end VG.Impl.Ed25519.X86.SignCached
end

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

theorem signCached_verified : Verified X86.target code (Spec.Ed25519.signCachedContract X86.abi 280) := by
  have hsat := signWide_implies.sat_left
  have satLocal : ∃ s, signCachedLocal.pre s := hsat.elim fun s h => ⟨_, signWide_pre s h⟩
  have verifiedLocal : Verified X86.target code signCachedLocal :=
    Verified.of_correct (fun _ h => signCached_ok h) signCached_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal signRd signWr signWide_pre
    ?_ ?_ ?_ ?_ hsat) signWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [signRd, signWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [signWide, signCachedLocal, arg_withRegions, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [signWide, signCachedLocal, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ed25519.X86.SignCached
