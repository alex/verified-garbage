import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
import VerifiedGarbage.Proof.Poly1305.X86_64.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import Mathlib.Tactic.IntervalCases

/-!
# Poly1305 on x86-64: `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr leBytes)

/-- The 32 bytes at `p` as four little-endian words. -/
theorem bytesAt_32 (m : Mem) (p : Addr) :
    bytesAt m p 32 = leBytes 8 (m.readW (off p 0) 64).toNat ++ leBytes 8 (m.readW (off p 8) 64).toNat ++
      leBytes 8 (m.readW (off p 16) 64).toNat ++ leBytes 8 (m.readW (off p 24) 64).toNat := by
  rw [show 32 = 8 + (8 + (8 + 8)) from rfl, Poly1305.bytesAt_add, Poly1305.bytesAt_add,
    Poly1305.bytesAt_add, Poly1305.bytesAt_leBytes_64, Poly1305.bytesAt_leBytes_64,
    Poly1305.bytesAt_leBytes_64, Poly1305.bytesAt_leBytes_64]
  simp only [off_eq, BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc]

/-- The memory `init` leaves. -/
def initMem (m : Mem) (st key : Addr) : Mem :=
  ((((((m.writeW (off st 24) (m.readW (off key 0) 64)).writeW (off st 32) (m.readW (off key 8) 64)).writeW
    (off st 40) (m.readW (off key 16) 64)).writeW (off st 48) (m.readW (off key 24) 64)).writeW
    (off st 0) ((0 : BitVec 32).setWidth 64)).writeW (off st 8) ((0 : BitVec 32).setWidth 64)).writeW
    (off st 16) ((0 : BitVec 32).setWidth 64)

section
variable (s₀ : State)
abbrev kp : Addr := s₀.gpr .rsi
end

structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨kp s₀, 32⟩]
  wr : s₀.wr = [sR (st s₀)]
  st_key : (sR (st s₀)).Disjoint ⟨kp s₀, 32⟩
  ret_st : (retR s₀).Disjoint (sR (st s₀))

set_option simprocs false in
theorem init_exec {s₀ : State} (hp : IPre s₀) :
    WP isa init s₀ fun s' => s'.mem = initMem s₀.mem (st s₀) (kp s₀) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s₀.gpr r) := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s₀.wr (off (st s₀) d) 8 :=
    fun d hd => ⟨_, by rw [hp.wr]; exact List.mem_singleton_self _, contains_off hd (by omega)⟩
  have i : ∀ d, d + 8 ≤ 32 → InRegions (s₀.rd ++ s₀.wr) (off (kp s₀) d) 8 :=
    fun d hd => ⟨_, by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      contains_off hd (by omega)⟩
  have o0 := o 0 (by omega); have o8 := o 8 (by omega); have o16 := o 16 (by omega)
  have o24 := o 24 (by omega); have o32 := o 32 (by omega); have o40 := o 40 (by omega)
  have o48 := o 48 (by omega)
  have i0 := i 0 (by omega); have i8 := i 8 (by omega); have i16 := i 16 (by omega)
  have i24 := i 24 (by omega)
  simp only [off, st, kp] at o0 o8 o16 o24 o32 o40 o48 i0 i8 i16 i24
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, readSrc32, State.store64, State.load64, State.setReg, State.setReg32, o0, o8, o16,
    o24, o32, o40, o48, i0, i8, i16, i24, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, fun r h₁ h₂ h₃ h₄ => ?_⟩
  simp [h₁, h₂, h₃, h₄]

theorem initMem_frame (m : Mem) (st key : Addr) : Frame [sR st] m (initMem m st key) := by
  have c : ∀ d, d + 8 ≤ 128 → (sR st).Contains (off st d) (64 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [initMem]
  refine ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 24 ?_)).writeW
    (List.mem_singleton_self _) _ (c 32 ?_)).writeW (List.mem_singleton_self _) _ (c 40 ?_)).writeW
    (List.mem_singleton_self _) _ (c 48 ?_)).writeW (List.mem_singleton_self _) _ (c 0 ?_)).writeW
    (List.mem_singleton_self _) _ (c 8 ?_) |>.writeW (List.mem_singleton_self _) _ (c 16 ?_) <;> omega

theorem initMem_word (m : Mem) (st key : Addr) {j : Nat} (hj : j < 4) :
    (initMem m st key).readW (off st (24 + 8 * j)) 64 = m.readW (off key (8 * j)) 64 := by
  simp only [initMem]
  interval_cases j <;>
  simp (config := {decide := true}) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one,
    Mem.readW_writeW_self64, readW_writeW_off]

theorem initMem_acc (m : Mem) (st key : Addr) {d : Nat} (hd : d < 24) (h8 : d % 8 = 0) :
    (initMem m st key).readW (off st d) 64 = 0 := by
  simp only [initMem]
  obtain rfl | rfl | rfl : d = 0 ∨ d = 8 ∨ d = 16 := by omega
  all_goals simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW_writeW_off]

theorem init_correct {s₀ : State} (hp : IPre s₀) :
    WP isa init s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.initX86_64.post s₀ s' := by
  refine WP.mono (init_exec hp) fun s' ⟨hm, hg⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hg r (by rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide)
      (by rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide)
      (by rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide)
      (by rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide)
  · rw [hm]
    exact (initMem_frame _ _ _).readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · rfl
  · rw [hm, ← off_24, bytesAt_32, bytesAt_32, off_off, off_off, off_off, off_off,
      initMem_word _ _ _ (j := 0) (by omega), initMem_word _ _ _ (j := 1) (by omega),
      initMem_word _ _ _ (j := 2) (by omega), initMem_word _ _ _ (j := 3) (by omega)]
  · rw [hm, leNum_acc, initMem_acc _ _ _ (by omega) (by omega), initMem_acc _ _ _ (by omega) (by omega),
      initMem_acc _ _ _ (by omega) (by omega)]
    rfl

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 128⟩]

theorem init_verified :
    Verified X86_64.target Impl.Poly1305.X86_64.init Proof.Poly1305.initX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hs
    obtain ⟨t, s', he, h⟩ := init_correct ⟨h1, h2, h3, h4⟩
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · refine ⟨initSat, rfl, rfl, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, initSat] at h₁ h₂
      bv_omega

end VG.Proof.Poly1305.X86_64
