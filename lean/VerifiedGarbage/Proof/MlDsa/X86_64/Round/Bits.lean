import VerifiedGarbage.Proof.MlDsa.X86_64.Round.OneOut
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# ML-DSA on x86-64: `vg_mldsa_high_bits` and `vg_mldsa_low_bits`
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of)

theorem dShift_ge (g : Nat) : 1 ≤ dShift g := by unfold dShift; split <;> decide
theorem dShift_le (g : Nat) : dShift g ≤ 63 := by unfold dShift; split <;> decide

/-! ## The bodies -/

/-- The `r₁` the body of `highBits` stores. -/
def hbS (g : Nat) (x : BitVec 32) : BitVec 32 := BitVec.setWidth 32 (hbV g (BitVec.setWidth 64 x))

/-- The `r₀` the body of `lowBits` stores. -/
def lbS (g : Nat) (x : BitVec 32) : BitVec 32 :=
  BitVec.setWidth 32 (condAddV (BitVec.setWidth 64 x)
    (BitVec.ofNat 64 ((hbV g (BitVec.setWidth 64 x)).toNat * (BitVec.setWidth 64 (BitVec.ofNat 32 (2 * g))).toNat))
    qImm)

theorem hbBody_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4) :
    WP isa (.block (hbBody g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
          (hbS g (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by rcases hg with rfl | rfl <;> decide)
  unfold hbBody hb hbRaw condAdd
  xrun [h1, h2, ea_cf, List.cons_append, List.nil_append, hbS, hbV, hbRawV, condAddV, dShift_ge, dShift_le]
  rfl

theorem lbBody_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4) :
    WP isa (.block (lbBody g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
          (lbS g (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r8, .r11, .rcx] s s' := by
  refine WP.keep _ ?_ (by rcases hg with rfl | rfl <;> decide)
  unfold lbBody hb hbRaw condAdd
  xrun [h1, h2, ea_cf, List.cons_append, List.nil_append, lbS, hbV, hbRawV, condAddV, dShift_ge, dShift_le]
  rfl

/-! ## The values -/

theorem hbS_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (hbS g x).toNat = hbF g x.toNat % Proof.MlDsa.Round.hbM g := by
  have hx' : (BitVec.setWidth 64 x).toNat < q := by rw [setWidth64_toNat]; exact hx
  have hM : Proof.MlDsa.Round.hbM g ≤ 44 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have := Nat.mod_lt (hbF g x.toNat) (show Proof.MlDsa.Round.hbM g > 0 by rcases mem_gamma2s h with rfl | rfl <;> decide)
  rw [hbS, BitVec.toNat_setWidth, hbV_toNat h hx', setWidth64_toNat]
  omega

theorem lbS_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (lbS g x).toNat = (ofInt (lowBits g (Fin.ofNat q x.toNat))).val := by
  have hx' : (BitVec.setWidth 64 x).toNat < q := by rw [setWidth64_toNat]; exact hx
  have hv : (Fin.ofNat q x.toNat).val = x.toNat := Nat.mod_eq_of_lt hx
  rw [lowBits_val h, hv]
  have hM := hbM_mul h
  have hlt : hbF g x.toNat % Proof.MlDsa.Round.hbM g < Proof.MlDsa.Round.hbM g :=
    Nat.mod_lt _ (by rcases mem_gamma2s h with rfl | rfl <;> decide)
  have hle : hbF g x.toNat % Proof.MlDsa.Round.hbM g * (2 * g) ≤ q - 1 := by
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hlt))
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt hlt)
    rw [← hM]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have hg : 2 * g < 2 ^ 31 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have e1 : (BitVec.ofNat 64 ((hbV g (BitVec.setWidth 64 x)).toNat *
      (BitVec.setWidth 64 (BitVec.ofNat 32 (2 * g))).toNat)).toNat =
      hbF g x.toNat % Proof.MlDsa.Round.hbM g * (2 * g) := by
    rw [BitVec.toNat_ofNat, hbV_toNat h hx', setWidth64_toNat, setWidth64_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 * g < 2 ^ 32 by omega)]
    rw [q_eq] at hle
    omega
  have hq : qImm.toNat = q := rfl
  rw [lbS, BitVec.toNat_setWidth, condAddV_toNat (by decide) (by rw [e1, hq, setWidth64_toNat]; omega), e1, hq,
    setWidth64_toNat]
  rw [q_eq] at hx hle ⊢
  split <;> omega

/-! ## The functions -/

section
variable {post : State → State → Prop} {s₀ : State} (hp : (bitsK post).pre s₀)
include hp

theorem bits_ok {body : Nat → List Instr} {F : Nat → List (BitVec 32) → BitVec 32} {clob : List Reg}
    (hfix : ∀ r ∈ [Reg.r10, .rdi], r ∉ clob) (hcx : .rcx ∈ clob)
    (hbody : ∀ g, (g = g32 ∨ g = g88) → ∀ s, (∀ p ∈ [Reg.rdi], InRegions (s.rd ++ s.wr) (cfAddr (s.gpr p) (s.gpr .rcx)) 4) →
      InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4 →
      WP isa (.block (body g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
            (F g ([Reg.rdi].map fun p => s.mem.readW (cfAddr (s.gpr p) (s.gpr .rcx)) 32)) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep clob s s') :
    WP isa (.seq (.block (gammaCmp .rsi ++ ([.mov .r10 (.reg .rdx)] : List Instr))) (.ite .e (mapLoop (body g32)) (mapLoop (body g88))))
      s₀ fun s' =>
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rdx) k = F (arg32 s₀ .rsi) [coeffAt s₀.mem (s₀.gpr .rdi) k]) ∧
          Frame [pR (s₀.gpr .rdx)] s₀.mem s'.mem :=
  oneOut_ok (ins := [.rdi]) (fun p h => by simp only [List.mem_singleton] at h; subst h; rw [hp.1]; simp) hp.2.1
    (fun p h => by simp only [List.mem_singleton] at h; subst h; exact hp.2.2.1) hp.2.2.2.2.2.1
    (prologue_rsi_rdx s₀) (fun p h => by simp only [List.mem_singleton] at h; subst h; decide) hfix hcx hbody

end

theorem highBits_correct (s₀ : State) (hp : highBitsK.pre s₀) :
    ∃ t s', Exec isa highBits s₀ t s' ∧ abiPreserved s₀ s' ∧ highBitsK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .r8, .r10]
    (bits_ok hp (F := fun g xs => hbS g (xs.headD 0)) (by decide) (by decide)
      fun g hg s h1 h2 => hbBody_ok hg s (h1 _ (List.mem_singleton_self _)) h2) (by decide)
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.1
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hv k hk, map_get _ _ hk, List.headD_cons, hbS_toNat hp.2.2.2.2.2.1 (hr k hk), highBits_eq hp.2.2.2.2.2.1,
      polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm

theorem lowBits_correct (s₀ : State) (hp : lowBitsK.pre s₀) :
    ∃ t s', Exec isa lowBits s₀ t s' ∧ abiPreserved s₀ s' ∧ lowBitsK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .r8, .r10, .r11]
    (bits_ok hp (F := fun g xs => lbS g (xs.headD 0)) (by decide) (by decide)
      fun g hg s h1 h2 => lbBody_ok hg s (h1 _ (List.mem_singleton_self _)) h2) (by decide)
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.1
  · refine polyIs_of_toNat fun k hk => ?_
    rw [hv k hk, map_get _ _ hk, List.headD_cons, lbS_toNat hp.2.2.2.2.2.1 (hr k hk), polyAt_get _ _ hk]

/-- The pointers and `rsp` are public, and `γ₂`. -/
def bitsτ : X86_64.Taint.T := regsLo [.rdi, .rdx, .rsp] [.rsi]

theorem bits_agree {post : State → State → Prop} (s₁ s₂ : State) (_ : (bitsK post).pre s₁)
    (_ : (bitsK post).pre s₂) (hp : (bitsK post).pub s₁ s₂) : X86_64.Taint.Agree bitsτ s₁ s₂ :=
  agree_regsLo (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2.2

theorem highBits_ct : ConstantTime isa highBitsK.pre highBitsK.pub highBits :=
  VG.Taint.constantTime (A := X86_64.taint) bitsτ bits_agree (by taint_decide)

theorem lowBits_ct : ConstantTime isa lowBitsK.pre lowBitsK.pub lowBits :=
  VG.Taint.constantTime (A := X86_64.taint) bitsτ bits_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def bitsSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 95232 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem highBits_verified : Verified X86_64.target highBits (highBitsContract X86_64.abi) :=
  Verified.of_correct highBits_correct highBits_ct (by
    round_implies [highBitsContract, bitsSig, highBitsK, bitsK, X86_64.abi, X86_64.argRegs] [bitsSat]
      using bitsSat)

theorem lowBits_verified : Verified X86_64.target lowBits (lowBitsContract X86_64.abi) :=
  Verified.of_correct lowBits_correct lowBits_ct (by
    round_implies [lowBitsContract, bitsSig, lowBitsK, bitsK, X86_64.abi, X86_64.argRegs] [bitsSat]
      using bitsSat)

end VG.Proof.MlDsa.X86_64.Round
