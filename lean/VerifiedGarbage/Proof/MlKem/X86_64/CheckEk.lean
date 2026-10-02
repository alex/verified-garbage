import VerifiedGarbage.Impl.MlKem.X86_64.CheckEk
import VerifiedGarbage.Proof.MlKem.X86_64.Decode12
import VerifiedGarbage.Proof.MlKem.EkCheck
import VerifiedGarbage.Spec.MlKem.Contract

/-!
# ML-KEM on x86-64: the key check (`vg_mlkem768_check_ek`, `vg_mlkem1024_check_ek`)

For a parameter set `p` of rank `k`: the code counts the fields less than `q`
(`cnt`); all `256k` are exactly when the key passes the check (`cnt_eq_iff`,
`ekCheck_iff`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `checkEkK p.k (ek = rdi) -> rax`, the key check of the parameter set `p`. -/
def checkEkC (p : Params) : Contract isa where
  pre s := s.rd = [⟨s.gpr .rdi, p.ekLen⟩] ∧ s.wr = [] ∧ (retR s).Disjoint ⟨s.gpr .rdi, p.ekLen⟩
  post s s' := (s'.gpr .rax).setWidth 32 = if ekCheck p (bytesAt s.mem (s.gpr .rdi) p.ekLen) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The number of fields of the first `i` groups that are less than `q`. -/
def cnt (B : List Byte) : Nat → Nat
  | 0 => 0
  | i + 1 => cnt B i + (decide (field0 B i < q)).toNat + (decide (field1 B i < q)).toNat

theorem cnt_le (B : List Byte) : ∀ i, cnt B i ≤ 2 * i
  | 0 => Nat.le_refl _
  | i + 1 => by
    have := cnt_le B i
    have h0 := Bool.toNat_le (decide (field0 B i < q))
    have h1 := Bool.toNat_le (decide (field1 B i < q))
    simp only [cnt]; omega

theorem cnt_eq_iff (B : List Byte) : ∀ i, cnt B i = 2 * i ↔ ∀ g < i, field0 B g < q ∧ field1 B g < q
  | 0 => by simp [cnt]
  | i + 1 => by
    have ih := cnt_eq_iff B i
    have hl := cnt_le B i
    have h0 := Bool.toNat_le (decide (field0 B i < q))
    have h1 := Bool.toNat_le (decide (field1 B i < q))
    simp only [cnt]
    constructor
    · intro h g hg
      have e0 : (decide (field0 B i < q)).toNat = 1 := by omega
      have e1 : (decide (field1 B i < q)).toNat = 1 := by omega
      by_cases hgi : g = i
      · subst hgi
        simp only [Bool.toNat_eq_one, decide_eq_true_eq] at e0 e1
        exact ⟨e0, e1⟩
      · exact ih.mp (by omega) g (by omega)
    · intro h
      have hi := h i (by omega)
      rw [ih.mpr fun g hg => h g (by omega), decide_eq_true hi.1, decide_eq_true hi.2]
      rfl

theorem sx0 : BitVec.signExtend 64 (0 : BitVec 32) = 0#64 := by decide

theorem checkEkBody_ok (s : State) (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 1) 1)
    (h3 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 2) 1) :
    WP isa (.block checkEkBody) s fun s' =>
      (s'.gpr .r8 = s.gpr .r8 +
          BitVec.setWidth 64 (BitVec.ofBool (decide ((w24 (s.mem (s.gpr .rdi)) (s.mem (s.gpr .rdi + BitVec.ofNat 64 1))
            (s.mem (s.gpr .rdi + BitVec.ofNat 64 2)) &&& 4095).toNat < qImm.toNat))) +
          BitVec.setWidth 64 (BitVec.ofBool (decide ((w24 (s.mem (s.gpr .rdi)) (s.mem (s.gpr .rdi + BitVec.ofNat 64 1))
            (s.mem (s.gpr .rdi + BitVec.ofNat 64 2)) >>> (12 : Nat)).toNat < qImm.toNat))) ∧
        s'.gpr .rdi = s.gpr .rdi + 3 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        s'.mem = s.mem) ∧ Keep [.rax, .rdx, .rdi, .rcx, .r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold checkEkBody dec12Load
  xrun [h1, h2, h3, List.cons_append, List.nil_append, w24, z32, sx0, BitVec.add_zero]
  rfl

theorem checkEkFin_ok {n : Nat} (hn : n < 2 ^ 31) (s : State) :
    WP isa (.block [.alu .cmp .r8 (.imm (BitVec.ofNat 32 n)), .alu .sbb .rax (.reg .rax), .alu .add .rax (.imm 1)]) s
      fun s' => s'.gpr .rax = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((s.gpr .r8).toNat < n))) + 1 ∧
        Keep [.rax, .r8] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sx_ofNat hn]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]

namespace CheckEk

section
variable (p : Params) (s₀ : State)
abbrev eP : Addr := s₀.gpr .rdi
abbrev E : List Byte := bytesAt s₀.mem (eP s₀) p.ekLen
end

/-- After `i` groups. -/
structure Inv (p : Params) (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = eP s₀ + BitVec.ofNat 64 (3 * i)
  r8 : (s.gpr .r8).toNat = cnt (E p s₀) i
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem

section
variable {p : Params} (hk : 0 < p.k ∧ p.k ≤ 4) {s₀ : State} (hp : (checkEkC p).pre s₀)
include hk hp

theorem step {i : Nat} (hi : i < 128 * p.k) {s : State} (hI : Inv p s₀ i s) :
    WP isa (.block checkEkBody) s fun s' => Inv p s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hb : ∀ j < 3, s.gpr .rdi + BitVec.ofNat 64 j = eP s₀ + BitVec.ofNat 64 (3 * i + j) := fun j _ => by
    rw [hI.rdi, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hin : ∀ j < 3, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, hb j hj]
    exact ⟨⟨eP s₀, p.ekLen⟩, by simp, contains_offset' (by simp only [Params.ekLen]; omega)
      (by simp only [Params.ekLen]; omega)⟩
  have e : ∀ j < 3, s.mem (s.gpr .rdi + BitVec.ofNat 64 j) = (E p s₀).getD (3 * i + j) 0 := fun j hj => by
    rw [hb j hj, hI.mem, bytesAt_getD _ _ (by simp only [Params.ekLen]; omega)]
  refine WP.mono (checkEkBody_ok s (by simpa using hin 0 (by omega)) (hin 1 (by omega)) (hin 2 (by omega)))
    fun s' ⟨⟨h8, hdi, hcx, hz, hm⟩, hk⟩ => ⟨⟨?_, ?_, hk.2.1.trans hI.rd, hk.2.2.trans hI.wr, hm.trans hI.mem⟩,
      hcx, hz⟩
  · rw [hdi, hI.rdi]; exact ptr_step _ i 3
  · have e0 := e 0 (by omega); simp only [add_ofNat_zero, Nat.add_zero] at e0
    rw [h8, e0, e 1 (by omega), e 2 (by omega)]
    have hw := w24_toNat ((E p s₀).getD (3 * i) 0) ((E p s₀).getD (3 * i + 1) 0) ((E p s₀).getD (3 * i + 2) 0)
    have l0 := ((E p s₀).getD (3 * i) 0).isLt
    have l1 := ((E p s₀).getD (3 * i + 1) 0).isLt
    have l2 := ((E p s₀).getD (3 * i + 2) 0).isLt
    generalize w24 _ _ _ = W at hw
    have f0 : (W &&& 4095).toNat = field0 (E p s₀) i := by rw [and4095_toNat, hw, field0]; omega
    have f1 : (W >>> (12 : Nat)).toNat = field1 (E p s₀) i := by rw [shr_toNat, hw, field1]; omega
    have hc := cnt_le (E p s₀) i
    have b0 := Bool.toNat_le (decide (field0 (E p s₀) i < q))
    have b1 := Bool.toNat_le (decide (field1 (E p s₀) i < q))
    rw [f0, f1, qImm_toNat, ← q_eq, BitVec.toNat_add, BitVec.toNat_add, hI.r8]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofBool, cnt]
    have : ∀ b : Bool, b.toNat % 2 ^ 64 = b.toNat := fun b => Nat.mod_eq_of_lt (by cases b <;> decide)
    rw [this, this]
    omega

theorem correct : ∃ t s', Exec isa (checkEkK p.k) s₀ t s' ∧ abiPreserved s₀ s' ∧ (checkEkC p).post s₀ s' := by
  obtain ⟨t, s', he, hr, hk'⟩ := WP.keep (c := checkEkK p.k) [.rax, .rdx, .rdi, .rcx, .r8]
    (Q := fun s' => (s'.gpr .rax).setWidth 32 =
      if ekCheck p (bytesAt s₀.mem (s₀.gpr .rdi) p.ekLen) then 1 else 0) (by
    unfold checkEkK
    refine WP.seq (WP.mono (WP.keep (s := s₀) (c := .block [.mov32 .r8 (.imm 0)]) [.r8]
      (Q := fun s => s.gpr .r8 = 0 ∧ s.mem = s₀.mem) (by xrun) (by decide)) fun s₁ ⟨⟨h8, m₁⟩, k₁⟩ => ?_)
    refine WP.seq (WP.mono (wp_counted (s₀ := s₁) (N := 128 * p.k) (v := BitVec.ofNat 32 (128 * p.k))
      (by rw [BitVec.toNat_ofNat]; omega) (by omega) (Inv p s₀)
      (fun s₂ m₂ k₂ => ⟨?_, ?_, ?_, ?_, ?_⟩) fun i hi s hI => step hk hp hi hI) fun s₃ hI => ?_)
    · rw [k₂.gpr (by decide), k₁.gpr (by decide)]; simp
    · rw [k₂.gpr (by decide), h8]; rfl
    · rw [k₂.2.1, k₁.2.1]
    · rw [k₂.2.2, k₁.2.2]
    · rw [m₂, m₁]
    refine WP.mono (checkEkFin_ok (n := 256 * p.k) (by omega) s₃) fun s₄ ⟨hax, _⟩ => ?_
    have hc := cnt_le (E p s₀) (128 * p.k)
    have hck := ekCheck_iff p (E p s₀) (bytesAt_length _ _ _)
    rw [hax, hI.r8]
    by_cases h : cnt (E p s₀) (128 * p.k) = 2 * (128 * p.k)
    · rw [h, (cnt_eq_iff _ _).mp h |> hck.mpr, decide_eq_false (by omega)]; decide
    · have : ekCheck p (E p s₀) = false := by
        rw [Bool.eq_false_iff]; intro h'; exact h ((cnt_eq_iff _ _).mpr (hck.mp h'))
      rw [this, decide_eq_true (by omega : cnt (E p s₀) (128 * p.k) < 256 * p.k)]
      decide) (by rfl)
  exact ⟨t, s', he, abiPreserved_of_exec (by rfl) he
    (gprPreserved_of hk' (by decide) (ws := [])
      (by have := (Exec.regions he (by rfl)).2.2; rwa [hp.2.1] at this) (by simp)), hr⟩

end

end CheckEk

/-- Constant time, from the taint check of the code of the parameter set. -/
theorem checkEk_ct (p : Params) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rdi, .rsp]) (checkEkK p.k) h).isSome = true) :
    ConstantTime isa (checkEkC p).pre (checkEkC p).pub (checkEkK p.k) :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.1, hp.2]) ht

/-- A state satisfying the precondition. -/
def checkEkSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1184⟩]
  wr := []

theorem checkEk_verified :
    Verified X86_64.target Impl.MlKem.X86_64.checkEk (Spec.MlKem.checkEkContract X86_64.abi) :=
  Verified.of_correct (fun s hs => CheckEk.correct (p := mlKem768) (by decide) hs) (checkEk_ct mlKem768 (by taint_decide)) (by
    mlkem_implies [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, checkEkC, X86_64.abi,
      X86_64.argRegs, Params.ekLen, mlKem768] [checkEkSat] using checkEkSat)

end VG.Proof.MlKem.X86_64
