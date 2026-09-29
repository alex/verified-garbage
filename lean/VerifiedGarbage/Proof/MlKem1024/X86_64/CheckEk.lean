import VerifiedGarbage.Impl.MlKem1024.X86_64.CheckEk
import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
import VerifiedGarbage.Proof.MlKem.EkCheck1024
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_check_ek`

Untrusted: everything here is checked by Lean. As `vg_mlkem768_check_ek`
(`Proof/MlKem/X86_64/CheckEk.lean`, whose loop body and count `cnt` it
shares): all 1024 fields are less than `q` exactly when the key passes the
check (`cnt_eq_iff`, `ekCheck1024`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem1024_check_ek(ek = rdi) -> rax`. -/
def checkEk1024K : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, 1568⟩] ∧ s.wr = [] ∧ (retR s).Disjoint ⟨s.gpr .rdi, 1568⟩
  post s s' := (s'.gpr .rax).setWidth 32 = if ekCheck mlKem1024 (bytesAt s.mem (s.gpr .rdi) 1568) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsp = s₂.gpr .rsp

theorem sx1024 : BitVec.signExtend 64 (1024 : BitVec 32) = 1024 := by decide

theorem checkEkFin1024_ok (s : State) :
    WP isa (.block [.alu .cmp .r8 (.imm 1024), .alu .sbb .rax (.reg .rax), .alu .add .rax (.imm 1)]) s fun s' =>
      s'.gpr .rax = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((s.gpr .r8).toNat < 1024))) + 1 ∧
        Keep [.rax, .r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [sx1024]
  rfl

namespace CheckEk1024

section
variable (s₀ : State)
abbrev eP : Addr := s₀.gpr .rdi
abbrev E : List Byte := bytesAt s₀.mem (eP s₀) 1568
end

/-- After `i` groups. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = eP s₀ + BitVec.ofNat 64 (3 * i)
  r8 : (s.gpr .r8).toNat = cnt (E s₀) i
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem

section
variable {s₀ : State} (hp : checkEk1024K.pre s₀)
include hp

theorem step {i : Nat} (hi : i < 512) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block checkEkBody) s fun s' => Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hb : ∀ j < 3, s.gpr .rdi + BitVec.ofNat 64 j = eP s₀ + BitVec.ofNat 64 (3 * i + j) := fun j _ => by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hin : ∀ j < 3, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, hb j hj]
    exact ⟨⟨eP s₀, 1568⟩, by simp, contains_offset' (by omega) (by decide)⟩
  have e : ∀ j < 3, s.mem (s.gpr .rdi + BitVec.ofNat 64 j) = (E s₀).getD (3 * i + j) 0 := fun j hj => by
    rw [hb j hj, hI.mem, bytesAt_getD _ _ (by omega)]
  refine WP.mono (checkEkBody_ok s (by simpa using hin 0 (by omega)) (hin 1 (by omega)) (hin 2 (by omega)))
    fun s' ⟨⟨h8, hdi, hcx, hz, hm⟩, hk⟩ => ⟨⟨?_, ?_, hk.2.1.trans hI.rd, hk.2.2.trans hI.wr, hm.trans hI.mem⟩,
      hcx, hz⟩
  · rw [hdi, hI.rdi]; exact ptr_step _ i 3
  · have e0 := e 0 (by omega); simp only [add_ofNat_zero, Nat.add_zero] at e0
    rw [h8, e0, e 1 (by omega), e 2 (by omega)]
    have hw := w24_toNat ((E s₀).getD (3 * i) 0) ((E s₀).getD (3 * i + 1) 0) ((E s₀).getD (3 * i + 2) 0)
    have l0 := ((E s₀).getD (3 * i) 0).isLt
    have l1 := ((E s₀).getD (3 * i + 1) 0).isLt
    have l2 := ((E s₀).getD (3 * i + 2) 0).isLt
    generalize w24 _ _ _ = W at hw
    have f0 : (W &&& 4095).toNat = field0 (E s₀) i := by rw [and4095_toNat, hw, field0]; omega
    have f1 : (W >>> (12 : Nat)).toNat = field1 (E s₀) i := by rw [shr_toNat, hw, field1]; omega
    have hc := cnt_le (E s₀) i
    have b0 := Bool.toNat_le (decide (field0 (E s₀) i < q))
    have b1 := Bool.toNat_le (decide (field1 (E s₀) i < q))
    rw [f0, f1, qImm_toNat, ← q_eq, BitVec.toNat_add, BitVec.toNat_add, hI.r8]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofBool, cnt]
    have : ∀ b : Bool, b.toNat % 2 ^ 64 = b.toNat := fun b => Nat.mod_eq_of_lt (by cases b <;> decide)
    rw [this, this]
    omega

theorem correct : ∃ t s', Exec isa checkEk1024 s₀ t s' ∧ abiPreserved s₀ s' ∧ checkEk1024K.post s₀ s' := by
  obtain ⟨t, s', he, hr, hk⟩ := WP.keep (c := checkEk1024) [.rax, .rdx, .rdi, .rcx, .r8]
    (Q := fun s' => (s'.gpr .rax).setWidth 32 =
      if ekCheck mlKem1024 (bytesAt s₀.mem (s₀.gpr .rdi) 1568) then 1 else 0) (by
    unfold checkEk1024
    refine WP.seq (WP.mono (WP.keep (s := s₀) (c := .block [.mov32 .r8 (.imm 0)]) [.r8]
      (Q := fun s => s.gpr .r8 = 0 ∧ s.mem = s₀.mem) (by xrun) (by decide)) fun s₁ ⟨⟨h8, m₁⟩, k₁⟩ => ?_)
    refine WP.seq (WP.mono (wp_counted (s₀ := s₁) (N := 512) (v := 512) rfl (by decide) (Inv s₀)
      (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_⟩) fun i hi s hI => step hp hi hI) fun s₃ hI => ?_)
    · rw [k₂.gpr (by decide), k₁.gpr (by decide)]; simp
    · rw [k₂.gpr (by decide), h8]; rfl
    · rw [k₂.2.1, k₁.2.1]
    · rw [k₂.2.2, k₁.2.2]
    · rw [m₂, m₁]
    refine WP.mono (checkEkFin1024_ok s₃) fun s₄ ⟨hax, _⟩ => ?_
    have hc := cnt_le (E s₀) 512
    have hck := ekCheck1024 (E s₀) (bytesAt_length _ _ _)
    rw [hax, hI.r8]
    by_cases h : cnt (E s₀) 512 = 1024
    · rw [h, (cnt_eq_iff _ 512).mp h |> hck.mpr]; decide
    · have : ekCheck mlKem1024 (E s₀) = false := by
        rw [Bool.eq_false_iff]; intro h'; exact h ((cnt_eq_iff _ 512).mpr (hck.mp h'))
      rw [this, decide_eq_true (by omega : cnt (E s₀) 512 < 1024)]
      decide) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he
    (gprPreserved_of hk (by decide) (ws := [])
      (by have := (Exec.regions he (by decide)).2.2; rwa [hp.2.1] at this) (by simp)), hr⟩

end

end CheckEk1024

theorem checkEk1024_ct : ConstantTime isa checkEk1024K.pre checkEk1024K.pub checkEk1024 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.1, hp.2])
    (by taint_decide)

/-- A state satisfying the precondition. -/
def checkEk1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1568⟩]
  wr := []

theorem checkEk1024_verified :
    Verified X86_64.target checkEk1024 (Spec.MlKem1024.checkEkContract X86_64.abi) :=
  Verified.of_correct (fun s hs => CheckEk1024.correct hs) checkEk1024_ct (by
    mlkem_implies [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, checkEk1024K, X86_64.abi,
      X86_64.argRegs] [checkEk1024Sat] using checkEk1024Sat)

end VG.Proof.MlKem1024.X86_64
