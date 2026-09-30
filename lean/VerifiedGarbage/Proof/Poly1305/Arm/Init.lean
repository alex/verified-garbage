import VerifiedGarbage.Proof.Poly1305.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Poly1305 on 32-bit ARM: `init`

Untrusted: everything here is checked by Lean. The key is copied to
`[24, 56)` of the state, a word at a time, and the accumulator's six words
are zeroed.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

/-- The precondition of `init`, by field. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨State.addr (s₀.gpr .r1), 32⟩]
  wr : s₀.wr = [stR (s₀.gpr .r0)]
  st_key : (stR (s₀.gpr .r0)).Disjoint ⟨State.addr (s₀.gpr .r1), 32⟩
  st_fit : (s₀.gpr .r0).toNat + 128 ≤ 2 ^ 32
  key_fit : (s₀.gpr .r1).toNat + 32 ≤ 2 ^ 32

/-- After copying `i` words of the key. -/
structure KI (s₀ : State) (i : Nat) (s : State) : Prop where
  words : ∀ j < i, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (24 + 4 * j)) 32 =
    s₀.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * j)) 32
  keeps : KeepsF [.r2] [stR (s₀.gpr .r0)] s₀ s

theorem key_step {s₀ : State} (hp : IPre s₀) (i : Nat) (s : State) (hi : i < 8) (h : KI s₀ i s) :
    WP isa (.block [.ldr .r2 .r1 (4 * i), .str .r2 .r0 (24 + 4 * i)]) s (KI s₀ (i + 1)) := by
  have hkd : ∀ r' ∈ [stR (s₀.gpr .r0)],
      (⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r' := by
    simp only [List.mem_singleton, forall_eq]
    exact (hp.st_key.sub_right (sub_base _ (by omega) (by decide))).symm
  have h1 : s.gpr .r1 = s₀.gpr .r1 := h.keeps.gpr _ (by decide)
  have h0 : s.gpr .r0 = s₀.gpr .r0 := h.keeps.gpr _ (by decide)
  refine wp_ldr (a := State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * i)) (by omega)
    (by rw [h1]; exact addr_add (by have := hp.key_fit; omega))
    (by rw [h.keeps.rd, hp.rd]; exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
      contains_base _ (by omega) (by decide)⟩) fun s1 u1 => ?_
  refine wp_str (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (24 + 4 * i)) (by omega)
    (by rw [u1.other _ (by decide), h0]; exact ea hp.st_fit (by omega))
    (by rw [u1.wr, h.keeps.wr]; exact outSt (by rw [hp.wr]; exact List.mem_singleton_self _) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun j hj => ?_, ?_⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
    · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega), u1.mem]; exact h.words j h'
    · rw [Mem.readW_writeW_self32, u1.gpr, h.keeps.frame.readW (Region.contains_self _ _) hkd (by decide)]
  · refine h.keeps.trans ⟨fun r hr => ?_, ?_, u2.rd.trans u1.rd, u2.wr.trans u1.wr, u2.sp.trans u1.sp⟩
    · rw [u2.gpr, u1.other _ (by simpa using hr)]
    · rw [u2.mem, u1.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))

/-- After zeroing `i` words of the accumulator. -/
structure ZI (s₀ : State) (i : Nat) (s : State) : Prop where
  zero : ∀ j < i, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * j)) 32 = 0
  key : ∀ j < 8, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (24 + 4 * j)) 32 =
    s₀.mem.readW (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 (4 * j)) 32
  r2 : s.gpr .r2 = 0
  keeps : KeepsF [.r2] [stR (s₀.gpr .r0)] s₀ s

theorem zero_step {s₀ : State} (hp : IPre s₀) (i : Nat) (s : State) (hi : i < 6) (h : ZI s₀ i s) :
    WP isa (.block [.str .r2 .r0 (4 * i)]) s (ZI s₀ (i + 1)) := by
  have h0 : s.gpr .r0 = s₀.gpr .r0 := h.keeps.gpr _ (by decide)
  refine wp_str (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * i)) (by omega)
    (by rw [h0]; exact ea hp.st_fit (by omega))
    (by rw [h.keeps.wr]; exact outSt (by rw [hp.wr]; exact List.mem_singleton_self _) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun j hj => ?_, fun j hj => ?_, by rw [u2.gpr, h.r2], ?_⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | rfl
    · rw [readW_writeW_off _ _ _ (by omega) (by omega) (by omega)]; exact h.zero j h'
    · rw [Mem.readW_writeW_self32, h.r2]
  · rw [u2.mem, readW_writeW_off _ _ _ (by omega) (by omega) (by omega)]; exact h.key j hj
  · refine h.keeps.trans ⟨fun r _ => by rw [u2.gpr], ?_, u2.rd, u2.wr, u2.sp⟩
    rw [u2.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))

theorem accumulate_nil (r : Nat) : accumulate r [] = 0 := rfl

theorem init_correct {s₀ : State} (hp : IPre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.initArm.post s₀ s' := by
  unfold init
  rw [← List.append_nil ((List.range 6).flatMap _)]
  refine WP.append (wp_range_flatMap (M := isa) (KI s₀) (key_step hp) 8 (Nat.le_refl _) s₀
    ⟨fun _ h => absurd h (by omega), (Keeps.refl _ _).keepsF _⟩) fun s₁ h₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (ZI s₀) (zero_step hp) 6 (Nat.le_refl _) s₂
    ⟨fun _ h => absurd h (by omega), fun j hj => by rw [u₂.mem]; exact h₁.words j hj, u₂.gpr,
      h₁.keeps.trans ⟨fun r hr => u₂.other r (by simpa using hr), by rw [u₂.mem]; exact Frame.refl _ _,
        u₂.rd, u₂.wr, u₂.sp⟩⟩) fun s' h' => ⟨⟨fun r hr => ?_, h'.keeps.sp⟩, ?_, ?_, ?_⟩
  · exact h'.keeps.gpr r fun e => by simp only [List.mem_singleton] at e; subst e; simp [preserved] at hr
  · rfl
  · show bytesAt s'.mem (State.addr (s₀.gpr .r0) + 24) 32 = bytesAt s₀.mem (State.addr (s₀.gpr .r1)) 32
    rw [show (32 : Nat) = 4 * 8 from rfl]
    refine bytesAt_eq_of_words fun j hj => ?_
    rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, off_add]
    exact h'.key j hj
  · show leNum (bytesAt s'.mem (State.addr (s₀.gpr .r0)) 24) = accumulate _ []
    rw [accumulate_nil, leNum_bytesAt_24, h'.zero 0 (by decide), h'.zero 1 (by decide),
      h'.zero 2 (by decide), h'.zero 3 (by decide), h'.zero 4 (by decide), h'.zero 5 (by decide)]
    rfl

theorem IPre.of (s : State) (h : Proof.Poly1305.initArm.pre s) : IPre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 128⟩]

theorem init_ok (s : State) (hs : Proof.Poly1305.initArm.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.Arm.init s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.initArm.post s s' := by
  exact init_correct (IPre.of s hs)

theorem init_ct : ConstantTime isa Proof.Poly1305.initArm.pre Proof.Poly1305.initArm.pub
    Impl.Poly1305.Arm.init := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

theorem init_verified :
    Verified Arm.target Impl.Poly1305.Arm.init (Spec.Poly1305.initContract Arm.abi) :=
  Verified.of_correct init_ok init_ct (by
    sig_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig, Proof.Poly1305.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.Poly1305.Arm.initSat,
      Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Poly1305.Arm.initSat)

end VG.Proof.Poly1305.Arm
