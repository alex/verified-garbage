import VerifiedGarbage.Proof.Poly1305.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract

/-!
# Poly1305 on AArch64: `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr leBytes)

/-- The 32 bytes at `p` as four little-endian words. -/
theorem bytesAt_32 (m : Mem) (p : Addr) :
    bytesAt m p 32 = leBytes 8 (m.readW (off p 0) 64).toNat ++ leBytes 8 (m.readW (off p 8) 64).toNat ++
      leBytes 8 (m.readW (off p 16) 64).toNat ++ leBytes 8 (m.readW (off p 24) 64).toNat := by
  rw [show 32 = 8 + (8 + (8 + 8)) from rfl, Poly1305.bytesAt_add, Poly1305.bytesAt_add,
    Poly1305.bytesAt_add, Poly1305.bytesAt_leBytes_64, Poly1305.bytesAt_leBytes_64,
    Poly1305.bytesAt_leBytes_64, Poly1305.bytesAt_leBytes_64]
  simp only [off, add_ofNat_zero, BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc]

/-- The memory `init` leaves. -/
def initMem (m : Mem) (st key : Addr) : Mem :=
  ((((((m.writeW (off st 24) (m.readW (off key 0) 64)).writeW (off st 32) (m.readW (off key 8) 64)).writeW
    (off st 40) (m.readW (off key 16) 64)).writeW (off st 48) (m.readW (off key 24) 64)).writeW
    (off st 0) (((0 : BitVec 16).setWidth 64) <<< (16 * 0))).writeW (off st 8)
    (((0 : BitVec 16).setWidth 64) <<< (16 * 0))).writeW (off st 16) (((0 : BitVec 16).setWidth 64) <<< (16 * 0))

section
variable (s₀ : State)
abbrev kp : Addr := s₀.gpr .x1
end

structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨kp s₀, 32⟩]
  wr : s₀.wr = [sR (st s₀)]
  st_key : (sR (st s₀)).Disjoint ⟨kp s₀, 32⟩

set_option simprocs false in
theorem init_exec {s₀ : State} (hp : IPre s₀) :
    WP isa init s₀ fun s' => s'.mem = initMem s₀.mem (st s₀) (kp s₀) := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s₀.wr (off (st s₀) d) 8 :=
    fun d hd => ⟨_, by rw [hp.wr]; exact List.mem_singleton_self _, contains_off hd (by omega)⟩
  have i : ∀ d, d + 8 ≤ 32 → InRegions (s₀.rd ++ s₀.wr) (off (kp s₀) d) 8 :=
    fun d hd => ⟨_, by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      contains_off hd (by omega)⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  have o24 := o 24 (by decide); have o32 := o 32 (by decide); have o40 := o 40 (by decide)
  have o48 := o 48 (by decide)
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide)
  simp only [off, st, kp] at o0 o8 o16 o24 o32 o40 o48 i0 i8 i16 i24
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, State.load, State.store, State.read, State.write, Size.bits, BitVec.setWidth_eq,
    Option.bind_some, Option.map_some, o0, o8, o16, o24, o32, o40, o48, i0, i8, i16, i24, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  rfl

theorem initMem_frame (m : Mem) (st key : Addr) : Frame [sR st] m (initMem m st key) := by
  have c : ∀ d, d + 8 ≤ 128 → (sR st).Contains (off st d) (64 / 8) :=
    fun d hd => contains_off hd (by omega)
  simp only [initMem]
  refine ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 24 ?_)).writeW
    (List.mem_singleton_self _) _ (c 32 ?_)).writeW (List.mem_singleton_self _) _ (c 40 ?_)).writeW
    (List.mem_singleton_self _) _ (c 48 ?_)).writeW (List.mem_singleton_self _) _ (c 0 ?_)).writeW
    (List.mem_singleton_self _) _ (c 8 ?_) |>.writeW (List.mem_singleton_self _) _ (c 16 ?_)
  all_goals decide

set_option simprocs false in
theorem initMem_word (m : Mem) (st key : Addr) {j : Nat} (hj : j < 4) :
    (initMem m st key).readW (off st (24 + 8 * j)) 64 = m.readW (off key (8 * j)) 64 := by
  simp only [initMem]
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  all_goals simp (config := {decide := true}) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one,
    Mem.readW_writeW_self64, readW_writeW_off]

set_option simprocs false in
theorem initMem_acc (m : Mem) (st key : Addr) :
    leNum (bytesAt (initMem m st key) st 24) = 0 := by
  rw [leNum_acc]
  simp (config := {decide := true}) only [w64, initMem, Mem.readW_writeW_self64, readW_writeW_off]

theorem init_correct {s₀ : State} (hp : IPre s₀) :
    WP isa init s₀ fun s' => Proof.Poly1305.initAArch64.post s₀ s' := by
  refine WP.mono (init_exec hp) fun s' hm => ⟨rfl, ?_, ?_⟩
  · rw [← off_24, hm, bytesAt_32, bytesAt_32, off_off, off_off, off_off, off_off,
      initMem_word _ _ _ (j := 0) (by decide), initMem_word _ _ _ (j := 1) (by decide),
      initMem_word _ _ _ (j := 2) (by decide), initMem_word _ _ _ (j := 3) (by decide)]
  · rw [hm, initMem_acc]
    rfl

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 128⟩]

theorem init_untouched : Untouched Impl.Poly1305.AArch64.init :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; lit_decide)

theorem init_ok (s : State) (hs : Proof.Poly1305.initAArch64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.AArch64.init s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.initAArch64.post s s' := by
  obtain ⟨h1, h2, h3⟩ := hs
  obtain ⟨t, s', he, h⟩ := init_correct ⟨h1, h2, h3⟩
  exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (init_untouched r hr) he, Exec.sp he⟩, h⟩

theorem init_ct : ConstantTime isa Proof.Poly1305.initAArch64.pre Proof.Poly1305.initAArch64.pub
    Impl.Poly1305.AArch64.init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

theorem init_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.init (Spec.Poly1305.initContract AArch64.abi) :=
  Verified.of_correct init_ok init_ct (by
    sig_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig, Proof.Poly1305.initAArch64,
      AArch64.abi, AArch64.argRegs] [Proof.Poly1305.AArch64.initSat] using
      Proof.Poly1305.AArch64.initSat)

end VG.Proof.Poly1305.AArch64
