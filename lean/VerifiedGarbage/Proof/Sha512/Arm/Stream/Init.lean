import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Impl.Sha512.Arm.Stream
import VerifiedGarbage.Proof.Sha512.Arm.Lit

/-!
# Streaming SHA-512 on ARMv7: `init`

Untrusted: everything here is checked by Lean. One proof for every initial
hash value `iv`.
-/

namespace VG.Proof.Sha512.Arm.Stream

open VG VG.Arm VG.Impl.Sha512.Arm.Stream
open VG.Impl.Sha512.Arm (lo hi)
open VG.Proof.MdStream.Arm (Upd Mupd wp_str)
open VG.Spec.Sha512 (HashValue stateAt)

/-- After the first `n` words of `iv`. -/
structure IInv (iv : HashValue) (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  words : ∀ k < n, rd64 s.mem (s₀.gpr .r0) (8 * k) = iv[k]!

theorem initW_ok (iv : HashValue) {s₀ : State} (hfit : (s₀.gpr .r0).toNat + 192 ≤ 2 ^ 32)
    (hR : Reg64 s₀.wr (s₀.gpr .r0) 192) {n : Nat} (hn : n < 8) {s : State} (h : IInv iv s₀ n s) :
    WP isa (.block (initW iv n)) s (IInv iv s₀ (n + 1)) := by
  have h0 : s.gpr .r0 = s₀.gpr .r0 := h.gpr _ (by decide)
  have hR' : Reg64 s.wr (s₀.gpr .r0) 192 := h.wr ▸ hR
  simp only [initW]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
  refine wp_str (a := A (s₀.gpr .r0) (8 * n)) (by omega)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h0]) (by rw [u₂.wr, u₁.wr]; exact (hR' _ (by omega)).1)
    fun s₃ u₃ => wp_movw fun s₄ u₄ => wp_movt fun s₅ u₅ => ?_
  refine wp_str (a := A (s₀.gpr .r0) (8 * n + 4)) (by omega)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h0])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact (hR' _ (by omega)).2)
    fun s₆ u₆ => WP.block_nil ⟨fun r hr => ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [u₆.gpr, u₅.other r hr, u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr, h.gpr r hr]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  · have hm : s₆.mem = write64 s.mem (s₀.gpr .r0) (8 * n) iv[n]! := by
      rw [u₆.mem, u₅.gpr, u₄.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, movw_movt,
        movw_movt]
      rfl
    rw [hm]
    by_cases hkn : k = n
    · subst hkn; exact rd64_write64_self _ _ (by omega)
    · rw [rd64_write64_ne (b := s₀.gpr .r0) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
        (by omega)]
      exact h.words k (by omega)

theorem init_all (iv : HashValue) {s₀ : State} (hfit : (s₀.gpr .r0).toNat + 192 ≤ 2 ^ 32)
    (hR : Reg64 s₀.wr (s₀.gpr .r0) 192) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (initW iv))) s₀ (IInv iv s₀ n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact initW_ok iv hfit hR (by omega) h

theorem init_correct {s₀ : State} (iv : HashValue) (hp : (Proof.Sha512.initArm iv).pre s₀) :
    WP isa (init iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha512.initArm iv).post s₀ s' := by
  obtain ⟨-, hwr, hfit⟩ := hp
  refine WP.mono (init_all iv hfit (Reg64.of_mem (by simp [hwr]) hfit) 8 (Nat.le_refl _)) fun s h => ⟨⟨?_, h.sp⟩, ?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    exact h.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · refine Proof.Sha512.Stream.repr_nil (stateAt_ext (by omega) fun k hk => ?_)
    rw [h.words k hk, getElem!_pos iv k hk]

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 192⟩]

/-- The hint for `init 0`, which is also one for `init iv`. -/
abbrev initHint : VG.Taint.Hint taint.T := VG.Taint.hintOf taint (Taint.ofRegs [.r0]) (init 0)

/-- The taint check never looks at an immediate, so its result on `init iv`
is its result on `init 0`, which is decided. -/
theorem init_check (iv : HashValue) :
    (taint.check (Taint.ofRegs [.r0]) (init iv) initHint).isSome = true := by
  have h : (taint.check (Taint.ofRegs [.r0]) (init 0) initHint).isSome = true := by taint_decide
  rw [show taint.check (Taint.ofRegs [.r0]) (init iv) initHint =
    taint.check (Taint.ofRegs [.r0]) (init 0) initHint from rfl]
  exact h

theorem init_verified (iv : HashValue) : Verified Arm.target (init iv) (Proof.Sha512.initArm iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, by decide⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct iv hs
    exact ⟨t, s', he, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0]) (fun _ _ _ _ hp => ?_) (init_check iv)
    exact Taint.agree_ofRegs fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp

end VG.Proof.Sha512.Arm.Stream
