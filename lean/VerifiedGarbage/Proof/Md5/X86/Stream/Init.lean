import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Md5.Stream
import VerifiedGarbage.Proof.Md5.StateMem
import VerifiedGarbage.Proof.Md5.X86.Contract
import VerifiedGarbage.Impl.Md5.X86.Stream
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Md5.X86.Lit

/-!
# Streaming MD5 on x86 (32-bit): `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Md5.X86.Stream

open VG VG.X86 VG.Impl.Md5.X86.Stream
open VG.Impl.Md5.X86 (at_)
open VG.Proof.MdStream.X86 (wp_movi wp_movm wp_store contains_addr)
open VG.Spec.Md5 (stateAt H0)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The two instructions storing the word `x` at `[eax + 4 * k]`. -/
def word (x : BitVec 32) (k : Nat) : List Instr := [.mov .ecx (.imm x), .store (at_ .eax (4 * k)) .ecx]

theorem init_eq : init = .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.block (word H0[0] 0 ++ word H0[1] 1 ++ word H0[2] 2 ++ word H0[3] 3)) := rfl

theorem word_ok {x : BitVec 32} {k : Nat} {rest : List Instr} {s : State} {Q : State → Prop}
    {st : BitVec 32} (heax : s.gpr .eax = st) (hout : InRegions s.wr (addr st (4 * k)) 4)
    (kk : ∀ s', s'.gpr .eax = st → (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → s'.mem = s.mem.writeW (addr st (4 * k)) x → WP isa (.block rest) s' Q) :
    WP isa (.block (word x k ++ rest)) s Q := by
  simp only [word, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_store (a := addr st (4 * k))
    (by rw [ea_at, u₁.other _ (by decide), heax]) (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
  refine kk s₂ (by rw [u₂.gpr, u₁.other _ (by decide), heax]) (fun r hr => by rw [u₂.gpr, u₁.other r hr])
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) ?_
  rw [u₂.mem, u₁.gpr, u₁.mem]

theorem init_correct {s₀ : State} (hp : Proof.Md5.initX86.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Md5.initX86.post s₀ s' := by
  obtain ⟨hrd, hwr, hargs, hret, hfit, hsp⟩ := hp
  set st := arg s₀ 0 with hst
  have o : ∀ k, k < 4 → InRegions s₀.wr (addr st (4 * k)) 4 :=
    fun k hk => ⟨⟨st.setWidth 64, 80⟩, by simp [hwr], contains_addr (by omega) (by omega) hfit⟩
  rw [init_eq]
  refine WP.seq (wp_movm (a := addr (s₀.gpr .esp) 4) (ea_at _ _ _)
    ⟨⟨argAddr s₀ 0, 4⟩, by simp [hrd], Region.contains_self _ _⟩ fun s₁ u₁ => WP.block_nil ?_)
  have e1 : s₁.gpr .eax = st := u₁.gpr
  have w1 : s₁.wr = s₀.wr := u₁.wr
  rw [← List.append_nil (_ ++ word H0[3] 3)]
  simp only [List.append_assoc]
  refine word_ok e1 (by rw [w1]; exact o 0 (by omega)) fun s2 a2 g2 _ wr2 m2 => ?_
  refine word_ok a2 (by rw [wr2, w1]; exact o 1 (by omega)) fun s3 a3 g3 _ wr3 m3 => ?_
  refine word_ok a3 (by rw [wr3, wr2, w1]; exact o 2 (by omega)) fun s4 a4 g4 _ wr4 m4 => ?_
  refine word_ok a4 (by rw [wr4, wr3, wr2, w1]; exact o 3 (by omega))
    fun s5 _ g5 _ _ m5 => WP.block_nil ?_
  have k5 : ∀ r, r ≠ .ecx → r ≠ .eax → s5.gpr r = s₀.gpr r := fun r h h' => by
    rw [g5 r h, g4 r h, g3 r h, g2 r h, u₁.other r h']
  have ha : ∀ k, k < 4 → addr st (4 * k) = st.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
    fun k hk => addr_eq (by omega)
  have hm : s5.mem = Proof.Md5.StateMem.writeState s₀.mem (st.setWidth 64) H0 := by
    rw [m5, m4, m3, m2, u₁.mem, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega)]
    rfl
  have hf : Frame [⟨st.setWidth 64, 80⟩] s₀.mem s5.mem := by
    rw [m5, m4, m3, m2, u₁.mem]
    have c : ∀ k, k < 4 → (⟨st.setWidth 64, 80⟩ : Region).Contains (addr st (4 * k)) (32 / 8) :=
      fun k hk => contains_addr (by omega) (by omega) hfit
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega))).writeW (List.mem_singleton_self _) _ (c 3 (by omega))
  refine ⟨⟨fun r hr => k5 r ?_ ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)
  · show Spec.Md5.Repr s5.mem (st.setWidth 64) []
    rw [hm]
    exact Proof.Md5.Stream.repr_nil (Proof.Md5.StateMem.stateAt_writeState _ _ _)

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
  wr := [⟨0x1000, 80⟩]

theorem initSat_pre : Proof.Md5.initX86.pre initSat := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have e : argAddr initSat 0 = 0x4004 := by decide
  simp only [Proof.Md5.initX86, a0, e]
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, initSat] at h₁ h₂
    bv_omega

/-- The initial taint: the argument is public. -/
def initτ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 8 }

theorem init_agree₀ {s₁ s₂ : State} (h₁ : Proof.Md5.initX86.pre s₁) (h₂ : Proof.Md5.initX86.pre s₂)
    (hpub : Proof.Md5.initX86.pub s₁ s₂) : VG.X86.Taint.Agree initτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  have wf : ∀ s, Proof.Md5.initX86.pre s → VG.X86.Taint.Wf initτ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, hr, -, hsp⟩ := hs
    refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
      fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hsp, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
    simp only [hw, List.mem_singleton]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 4) (by omega) hr hd
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf _ h₁, wf _ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [initτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · simp only [initτ₀] at hk
    rw [show VG.X86.Taint.depth initτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq h₁.2.2.2.2.2 h4 hk, VG.X86.Taint.argByte_eq h₂.2.2.2.2.2 h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega)),
      show (k - 4) / 4 = 0 by omega]
    exact congrArg _ a0

theorem init_verified : Verified X86.target init Proof.Md5.initX86 := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, initSat_pre⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) initτ₀ (fun _ _ h₁ h₂ hp => init_agree₀ h₁ h₂ hp)
      (by taint_decide)

end VG.Proof.Md5.X86.Stream
