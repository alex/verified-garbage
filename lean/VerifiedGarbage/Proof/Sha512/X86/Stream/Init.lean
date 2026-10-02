import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Impl.Sha512.X86.Stream
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86.Lit

/-!
# Streaming SHA-512 on x86 (32-bit): `init`

One proof for every initial hash value `iv`.
-/

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Impl.Sha512.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha512.Word64 (lo hi)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_store wp_movm contains_addr)
open VG.Spec.Sha512 (HashValue stateAt)

/-- After the first `n` words of `iv`, with `eax` = `state`. -/
structure IInv (iv : HashValue) (s₀ : State) (st : BitVec 32) (n : Nat) (s : State) : Prop where
  eax : s.gpr .eax = st
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨st.setWidth 64, 192⟩] s₀.mem s.mem
  words : ∀ k < n, rd64 s.mem st (8 * k) = iv[k]!

theorem initW_ok (iv : HashValue) {s₀ : State} {st : BitVec 32} (hfit : st.toNat + 192 ≤ 2 ^ 32)
    (hR : ⟨st.setWidth 64, 192⟩ ∈ s₀.wr) {n : Nat} (hn : n < 8) {s : State} (h : IInv iv s₀ st n s) :
    WP isa (.block (initW iv n)) s (IInv iv s₀ st (n + 1)) := by
  have c : ∀ o, o + 4 ≤ 192 → (⟨st.setWidth 64, 192⟩ : Region).Contains (addr st o) (32 / 8) :=
    fun o ho => contains_addr ho (by decide) hfit
  have o : ∀ o, o + 4 ≤ 192 → InRegions s.wr (addr st o) 4 :=
    fun o ho => ⟨_, by rw [h.wr]; exact hR, c o ho⟩
  simp only [initW]
  refine wp_movi fun s₁ u₁ => wp_store (a := addr st (8 * n))
    (by rw [ea_of (u₁.other _ (by decide) |>.trans h.eax)]) (by rw [u₁.wr]; exact o _ (by omega))
    fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
  refine wp_store (a := addr st (8 * n + 4))
    (by rw [ea_of ((u₃.other _ (by decide)).trans (by rw [u₂.gpr, u₁.other _ (by decide), h.eax]))])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o _ (by omega)) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = write64 s.mem st (8 * n) iv[n]! := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
    rfl
  refine ⟨?_, fun r h₁ h₂ => ?_, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], ?_, fun k hk => ?_⟩
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.eax]
  · rw [u₄.gpr, u₃.other _ h₂, u₂.gpr, u₁.other _ h₂, h.gpr r h₁ h₂]
  · rw [hm]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
      (List.mem_singleton_self _) _ (c _ (by omega))
  · rw [hm]
    by_cases hkn : k = n
    · subst hkn; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne _ _ (by omega) (by omega) (by omega)]
      exact h.words k (by omega)

theorem init_all (iv : HashValue) {s₀ : State} {st : BitVec 32} (hfit : st.toNat + 192 ≤ 2 ^ 32)
    (hR : ⟨st.setWidth 64, 192⟩ ∈ s₀.wr) {s : State} (h : IInv iv s₀ st 0 s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (initW iv))) s (IInv iv s₀ st n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact initW_ok iv hfit hR (by omega) h

theorem init_correct (iv : HashValue) {s₀ : State} (hp : (Proof.Sha512.initX86 iv).pre s₀) :
    WP isa (init iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha512.initX86 iv).post s₀ s' := by
  obtain ⟨hrd, hwr, -, hret, hfit, -⟩ := hp
  set st := arg s₀ 0 with hst
  have hR : ⟨st.setWidth 64, 192⟩ ∈ s₀.wr := by simp [hwr]
  refine wp_movm (a := addr (s₀.gpr .esp) 4) rfl
    ⟨⟨argAddr s₀ 0, 4⟩, by simp [hrd], Region.contains_self _ _⟩ fun s₁ u₁ => ?_
  refine WP.mono (init_all iv hfit hR ⟨u₁.gpr, fun r h _ => u₁.other r h, u₁.rd, u₁.wr,
    by rw [u₁.mem]; exact Frame.refl _ _, fun _ h => absurd h (by omega)⟩ 8 (Nat.le_refl _))
    fun s h => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · refine h.gpr r ?_ ?_ <;>
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · exact h.frame.readW (Region.contains_self _ _) (by simpa using hret) (by decide)
  · refine Proof.Sha512.Stream.repr_nil (stateAt_ext (by rw [← hst]; omega) fun k hk => ?_)
    rw [h.words k hk, getElem!_pos iv k hk]

/-- Memory holding the argument `0x1000` at `0x4004`. -/
def initSatMem : Mem := fun a => if a = 0x4005 then 0x10 else 0

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := initSatMem
  rd := [⟨0x4004, 4⟩]
  wr := [⟨0x1000, 192⟩]

theorem initSat_pre (iv : HashValue) : (Proof.Sha512.initX86 iv).pre initSat := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have e : argAddr initSat 0 = 0x4004 := by decide
  simp only [Proof.Sha512.initX86, a0, e]
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The initial taint: the argument is public, and the word holding `state`
is the base address of the writable region. -/
def initτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [192], argLen := 8, argBases := [(4, 0)] }

theorem init_agree₀ (iv : HashValue) {s₁ s₂ : State} (h₁ : (Proof.Sha512.initX86 iv).pre s₁)
    (h₂ : (Proof.Sha512.initX86 iv).pre s₂) (hpub : (Proof.Sha512.initX86 iv).pub s₁ s₂) :
    VG.X86.Taint.Agree initτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  have wf : ∀ s, (Proof.Sha512.initX86 iv).pre s → VG.X86.Taint.Wf initτ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, hr, hfit, hsp⟩ := hs
    refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hw, initτ₀], by simp [hw], ?_⟩,
      fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
      fun _ => ⟨hsp, ?_⟩, ?_⟩
    · simp only [hw, List.mem_singleton]
      rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
    · simp only [hw, List.mem_singleton]
      rintro r rfl
      exact VG.X86.Taint.frame_disjoint (n := 4) (by omega) hr hd
    · intro p hp'
      simp only [initτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
      subst hp'; refine ⟨by decide, ?_⟩
      simp [VG.X86.Taint.region, hw, addr, arg, argAddr]
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf _ h₁, wf _ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [initτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1, a0]
  · simp only [initτ₀] at hk
    rw [show VG.X86.Taint.depth initτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq h₁.2.2.2.2.2 h4 hk, VG.X86.Taint.argByte_eq h₂.2.2.2.2.2 h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega)),
      show (k - 4) / 4 = 0 by omega]
    exact congrArg _ a0

/-- The hint for `init 0`, which is also one for `init iv`. -/
abbrev initHint : VG.Taint.Hint taint.T := VG.Taint.hintOf taint initτ₀ (init 0)

/-- The taint check never looks at an immediate, so the kernel evaluates it on
`init iv` for any `iv`. -/
theorem init_check (iv : HashValue) : (taint.check initτ₀ (init iv) initHint).isSome = true := by
  kernel_rfl

theorem init_verified (iv : HashValue) :
    Verified X86.target (init iv) (Proof.Sha512.initX86 iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, initSat_pre iv⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct iv hs
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) initτ₀ (fun _ _ h₁ h₂ hp => init_agree₀ iv h₁ h₂ hp)
      (init_check iv)

end VG.Proof.Sha512.X86.Stream
