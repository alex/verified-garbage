import VerifiedGarbage.Proof.Blake2.X86.Stream.Init
import VerifiedGarbage.Proof.Blake2.X86.Stream.Update
import VerifiedGarbage.Proof.Blake2.X86.Stream.Finalize

/-!
# Streaming BLAKE2 on x86 (32-bit): `Verified`, for any compression function

Untrusted: everything here is checked by Lean. `init`, `update` and
`finalize` meet the per-target contracts of `Proof/Blake2/X86/Contract.lean`,
for either word size, given a correct compression function (`CalleeOk`) and
that the code (with that compression function) is constant time, which each
instance proves by the taint analysis (`VG.Taint.constantTime`) from the
initial taint (`τInit`, `τUpdate`, `τFinalize`) and the facts that the
public inputs give it (`init_agree`, `update_agree`, `finalize_agree`).
-/

namespace VG.Proof.Blake2.X86.Stream

open VG VG.X86 VG.Spec.Blake2
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86)

variable {w : Nat} {P : Params w}

/-! ## The initial taint -/

section
variable (w : Nat)

/-- `init`: the stack arguments are public, and the word holding `state` is
the base address of the writable region. -/
def τInit : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w], argLen := 20,
    argBases := [(4, 0)] }

/-- `update`: the stack arguments are public, the words holding `state` and
`scratch` are the base addresses of the writable regions, and the 32 bytes
below `esp` are outside them. -/
def τUpdate : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w, 576], argLen := 28,
    argBases := [(4, 0), (24, 1)], room := 32 }

/-- `finalize`: as `update`, with the output. -/
def τFinalize : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w, bufOff w, 576], argLen := 24,
    argBases := [(4, 0), (16, 1), (20, 2)], room := 32 }

end

theorem argMem_eq {s₁ s₂ : State} {n : Nat} (f₁ : (s₁.gpr .esp).toNat + n ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + n ≤ 2 ^ 32) (ha : ∀ i, 4 + 4 * i < n → arg s₁ i = arg s₂ i) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    s₁.mem (VG.X86.Taint.argByte s₁ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) =
      s₂.mem (VG.X86.Taint.argByte s₂ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) := by
  rw [show VG.X86.Taint.depth ([] : List (Option Nat)) = 0 from rfl, Nat.zero_add,
    VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (ha _ (by omega))

/-! ## `init` -/

theorem init_wf (hP : Ok P) {s : State} (h : (initX86 P).pre s) : VG.X86.Taint.Wf (τInit w) s := by
  have hp := Init.pre_of h
  have hst := hp.st_fit; have hs := hp.sp_fit; have hl := hP.len
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τInit], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [τInit]; omega, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.a_st
  · intro p hp'
    simp only [τInit, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    exact ⟨by simp [τInit], by simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]⟩

theorem init_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (initX86 P).pre s₁) (h₂ : (initX86 P).pre s₂)
    (hpub : (initX86 P).pub s₁ s₂) : VG.X86.Taint.Agree (τInit w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Init.pre_of h₁; have hp₂ := Init.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, init_wf hP h₁, init_wf hP h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 20) (by have := hp₁.sp_fit; omega) (by have := hp₂.sp_fit; omega)
      (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [τInit, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Init.stR, Init.stA, Init.st, ha 0 (by omega)]

/-! ## `update` -/

theorem update_wf (hP : Ok P) {s : State} (h : (updateX86 P).pre s) : VG.X86.Taint.Wf (τUpdate w) s := by
  have hp := Update.pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have hl := hP.len
  obtain ⟨-, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τUpdate], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [τUpdate]; omega, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.st_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [τUpdate, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [τUpdate], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [k1, k2]

theorem update_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (updateX86 P).pre s₁) (h₂ : (updateX86 P).pre s₂)
    (hpub : (updateX86 P).pub s₁ s₂) : VG.X86.Taint.Agree (τUpdate w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Update.pre_of h₁; have hp₂ := Update.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, update_wf hP h₁, update_wf hP h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 28) hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [τUpdate, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Update.stR, Update.scR, Update.stA, Update.scA, Update.st, Update.scr, ha 0 (by omega),
      ha 5 (by omega)]

/-! ## `finalize` -/

theorem finalize_wf (hP : Ok P) {s : State} (h : (finalizeX86 P).pre s) :
    VG.X86.Taint.Wf (τFinalize w) s := by
  have hp := Finalize.pre_of h
  have hst := hp.st_fit; have hso := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have hl := hP.len
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k1, k2, k3, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τFinalize], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [τFinalize]; omega, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr⟩, hp.out_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.a_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [τFinalize, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by simp [τFinalize], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [k1, k2, k3]

theorem finalize_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (finalizeX86 P).pre s₁)
    (h₂ : (finalizeX86 P).pre s₂) (hpub : (finalizeX86 P).pub s₁ s₂) :
    VG.X86.Taint.Agree (τFinalize w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Finalize.pre_of h₁; have hp₂ := Finalize.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, finalize_wf hP h₁, finalize_wf hP h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 24) hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega)) h4 hk⟩
  · simp only [τFinalize, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Finalize.stR, Finalize.outR, Finalize.scR, Finalize.stA, Finalize.opA, Finalize.scA,
      Finalize.st, Finalize.op, Finalize.scr, ha 0 (by omega), ha 3 (by omega), ha 4 (by omega)]

/-! ## `Verified` -/

theorem init_verified (hP : Ok P)
    (hct : ConstantTime isa (initX86 P).pre (initX86 P).pub (Impl.Blake2.X86.Stream.init P))
    (hsat : ∃ s, (initX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.init P) (initX86 P) :=
  ⟨fun _ hs => Init.correct hP (Init.pre_of hs), hct, hsat⟩

theorem update_verified (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code)
    (hct : ConstantTime isa (updateX86 P).pre (updateX86 P).pub (Impl.Blake2.X86.Stream.update w name code))
    (hsat : ∃ s, (updateX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.update w name code) (updateX86 P) :=
  ⟨fun _ hs => Update.correct hP hf (Update.pre_of hs), hct, hsat⟩

theorem finalize_verified (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code)
    (hct : ConstantTime isa (finalizeX86 P).pre (finalizeX86 P).pub (Impl.Blake2.X86.Stream.finalize w name code))
    (hsat : ∃ s, (finalizeX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.finalize w name code) (finalizeX86 P) :=
  ⟨fun _ hs => Finalize.correct hP hf (Finalize.pre_of hs), hct, hsat⟩

end VG.Proof.Blake2.X86.Stream
