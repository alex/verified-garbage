import VerifiedGarbage.Proof.Scrypt.Arm.BlockMixFun
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scryptBlockMix on 32-bit ARM: verified

Untrusted: everything here is checked by Lean. `SalsaSpec` of the verified
Salsa20/8 Core, from its `Verified` proof by `WP.call`; then the `Verified`
proof of `vg_scrypt_blockmix`. Only the pointers, `r` and the stack argument
(the scratch pointer) are public, and the taint analysis checks that nothing
else reaches an address or a branch.
-/

namespace VG.Proof.Scrypt.Arm.BlockMix

open VG VG.Arm

/-- A region inside one of `rs` is covered by `rs`. -/
theorem covers_of_in {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    Covers [⟨a, n⟩] rs := by
  obtain ⟨R, hR, hc⟩ := h
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨R, hR, (a - R.base).toNat, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega, hc⟩

theorem covers_pair {rs : List Region} {a b : Region} (ha : Covers [a] rs) (hb : Covers [b] rs) :
    Covers [a, b] rs := by
  intro x n ⟨r, hr, hc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha x n ⟨_, List.mem_singleton_self _, hc⟩
  · exact hb x n ⟨_, List.mem_singleton_self _, hc⟩

theorem salsaSpec : SalsaSpec Impl.Scrypt.Arm.salsa := by
  intro s d sc hd hsc fd fsc hds hind hins Q hQ
  have c0 : s.callEntry.gpr .r0 = d := (State.callEntry_gpr _ (by decide)).trans hd
  have c1 : s.callEntry.gpr .r1 = sc := (State.callEntry_gpr _ (by decide)).trans hsc
  have hw : Covers [⟨State.addr d, 64⟩, ⟨State.addr sc, 64⟩] s.wr :=
    covers_pair (covers_of_in hind) (covers_of_in hins)
  refine WP.call (k := Proof.Scrypt.salsaArm) Proof.Scrypt.Arm.salsa_correct
    (rd := []) (wr := [⟨State.addr d, 64⟩, ⟨State.addr sc, 64⟩]) ?_ ?_ hw ?_
  · simp only [Proof.Scrypt.salsaArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨by trivial, by trivial, hds, fd, fsc⟩
  · intro a n h
    obtain ⟨R, hR, hc⟩ := hw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.salsaArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

/-- The initial taint: `r0`–`r3` are public, and so is the stack argument
(the scratch pointer). -/
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := 4 }

theorem wf₀ {s : State} (h : Proof.Scrypt.blockMixArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hp.sp_nw, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
  simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hp.a_y
  · exact hp.a_s

theorem argByte_eq (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Scrypt.blockMixArm.pre s₁)
    (h₂ : Proof.Scrypt.blockMixArm.pre s₂) (hpub : Proof.Scrypt.blockMixArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · simp only [τ₀] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

/-- A state satisfying the precondition: `b` at `0x1000`, `y` at `0x2000`
and the scratch space at `0x3000`, passed on the stack at `0x5000`. -/
def bmSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x30 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixArm.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.Arm.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixArm.post s s' := by
  obtain ⟨t, s', he, h⟩ := BlockMix.correct salsaSpec (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixArm.pre Proof.Scrypt.blockMixArm.pub
    Impl.Scrypt.Arm.blockMix := by
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem blockMix_verified :
    Verified Arm.target Impl.Scrypt.Arm.blockMix (Spec.Scrypt.blockMixContract Arm.abi) :=
  Verified.of_correct blockMix_correct blockMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      post := by
        sig_implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      pub := by
        sig_implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      sat := by
        implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr,
          Proof.Scrypt.Arm.BlockMix.bmSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
          using Proof.Scrypt.Arm.BlockMix.bmSat }

end VG.Proof.Scrypt.Arm.BlockMix
