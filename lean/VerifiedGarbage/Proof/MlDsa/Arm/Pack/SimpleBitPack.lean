import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Contracts
import VerifiedGarbage.Proof.MlKem.Arm.Add

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_simple_bit_pack`

Untrusted: everything here is checked by Lean. The loop is proven once for
every width (`packLoop_ok`), and the function by its three cases.
-/

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Pack

theorem sbpLd_ok : LdOk sbpLd BitVec.toNat := fun j s hj hin => by
  refine WP.keep _ ?_ rfl
  unfold sbpLd
  run_block [hj, hin, and_true]

/-- A value at most `b` is less than `2 ^ bitlen b`. -/
theorem lt_bitlen {x b : Nat} (h : x ≤ b) : x < 2 ^ bitlen b := Nat.lt_of_le_of_lt h Nat.lt_log2_self

/-- The registers `s'` has as `s` (for the ABI). -/
theorem keep_of_same {rs : List Reg} {s₀ s s' : State} (hs : Same s₀ s) (hk : Keep rs s s') : Keep rs s₀ s' :=
  ⟨fun r hr => by rw [hk.1 r hr, hs.1], hk.2.1.trans hs.2.2.1, hk.2.2.1.trans hs.2.2.2.1, hk.2.2.2.trans hs.2.2.2.2⟩

theorem sbp_wp {s₀ : State} (hp : SbpPre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.simpleBitPack s₀ fun s' =>
      bytesAt s'.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
        simpleBitPack (natPolyAt s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1).toNat ∧ Keep packRegs s₀ s' := by
  have go : ∀ {d c nb : Nat}, Shape d c nb → bitlen (s₀.gpr .r1).toNat = d → ∀ s : State, Same s₀ s →
      WP isa (packLoop sbpLd d c nb) s fun s' =>
        bytesAt s'.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
          simpleBitPack (natPolyAt s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1).toNat ∧ Keep packRegs s₀ s' := by
    intro d c nb hs hd s hS
    have hlen := hp.len
    rw [hd] at hlen
    refine WP.mono (packLoop_ok sbpLd_ok hs (pf := s₀.gpr .r0) (po := s₀.gpr .r2) (m₀ := s₀.mem) (rd := s₀.rd)
      (wr := s₀.wr) (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
      (by rw [hp.wr, hlen]; exact List.mem_singleton_self _) (by rw [← hlen]; exact hp.disj) hp.fitF
      (by rw [← hlen]; exact hp.fitO) (fun i hi => by rw [← hd]; exact lt_bitlen (hp.le i hi))
      (by rw [hS.1]) (by rw [hS.1]) hS.2.2.1 hS.2.2.2.1 hS.2.1)
      fun s' ⟨hB, _, hk⟩ => ⟨?_, keep_of_same hS hk⟩
    rw [hlen, hB, simpleBitPack_eq, natPolyAt_toList, hd]
  unfold Impl.MlDsa.Arm.Pack.simpleBitPack
  refine sel_ok .r1 15 (by decide) (by decide) _ _ s₀ (fun s₁ h₁ e => ?_) (fun s₁ h₁ n15 => ?_)
  · exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) (by rw [e]; decide) s₁ h₁
  refine sel_ok .r1 43 (by decide) (by decide) _ _ s₁ (fun s₂ h₂ e => ?_) (fun s₂ h₂ n43 => ?_)
  · rw [h₁.1] at e
    exact go (d := 6) (c := 4) (nb := 3) (by constructor <;> decide) (by rw [e]; decide) s₂
      ⟨by rw [h₂.1, h₁.1], by rw [h₂.2.1, h₁.2.1], by rw [h₂.2.2.1, h₁.2.2.1], by rw [h₂.2.2.2.1, h₁.2.2.2.1],
        by rw [h₂.2.2.2.2, h₁.2.2.2.2]⟩
  · rw [h₁.1] at n43
    have e : (s₀.gpr .r1).toNat = 1023 := by
      have hb := hp.b
      simp only [simpleBitPackBounds, t1Max_eq, List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
    exact go (d := 10) (c := 4) (nb := 5) (by constructor <;> decide) (by rw [e]; decide) s₂
      ⟨by rw [h₂.1, h₁.1], by rw [h₂.2.1, h₁.2.1], by rw [h₂.2.2.1, h₁.2.2.1], by rw [h₂.2.2.2.1, h₁.2.2.2.1],
        by rw [h₂.2.2.2.2, h₁.2.2.2.2]⟩

/-- `simpleBitPack` writes no register the ABI preserves. -/
theorem sbp_preserves : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.MlDsa.Arm.Pack.simpleBitPack, dstOf i ≠ some r := by
  have h : (instrs Impl.MlDsa.Arm.Pack.simpleBitPack).all
      (fun i => preserved.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-- In memory of zeros, every coefficient is 0. -/
theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp [coeffAt, Mem.readW, Mem.read]

/-- A state satisfying the precondition. -/
def sbpSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 15 | .r2 => 0x2000 | .r3 => 128 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 128⟩]

example : ∃ pre post leak, simpleBitPackContract Arm.abi =
    simpleBitPackApi.sig.contract Arm.target.abi pre post simpleBitPackApi.writeArgs 0 leak := ⟨_, _, _, rfl⟩

theorem simpleBitPack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.simpleBitPack (simpleBitPackContract Arm.abi) := by
  refine ⟨fun s hs => ?_, Proof.MlKem.Arm.Add.ctRegs [.r0, .r1, .r2, .r3] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := SbpPre.of hs
    obtain ⟨t, s', he, hpost, hk⟩ := sbp_wp hp
    refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (sbp_preserves r hr) he, hk.2.2.2⟩, ?_⟩
    sig_post [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hpost
  · sig_pub [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2, h3⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨sbpSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | exact fun i _ => by rw [coeffAt_zero]; exact Nat.zero_le _
        | (simp only [simpleBitPackBounds, t1Max_eq]; decide +kernel)
        | decide +kernel

end VG.Proof.MlDsa.Arm.Pack
