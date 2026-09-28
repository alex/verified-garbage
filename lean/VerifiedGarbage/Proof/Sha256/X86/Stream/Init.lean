import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Sha256.AArch64.Compress
import VerifiedGarbage.Spec.Sha256.X86

/-!
# Streaming SHA-256 on x86 (32-bit): `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.X86.Stream

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Impl.Sha256.X86 (at_)
open VG.Spec.Sha256 (stateAt H0)

/-- The two instructions storing the word `x` at `[eax + 4 * k]`. -/
def word (x : BitVec 32) (k : Nat) : List Instr := [.mov .ecx (.imm x), .store (at_ .eax (4 * k)) .ecx]

theorem init_eq : init = .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.block (word H0[0] 0 ++ word H0[1] 1 ++ word H0[2] 2 ++ word H0[3] 3 ++ word H0[4] 4 ++
      word H0[5] 5 ++ word H0[6] 6 ++ word H0[7] 7)) := rfl

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

set_option maxHeartbeats 4000000 in
theorem init_correct {s₀ : State} (hp : Spec.Sha256.initX86.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Spec.Sha256.initX86.post s₀ s' := by
  obtain ⟨hrd, hwr, hargs, hret, hfit, hsp⟩ := hp
  set st := arg s₀ 0 with hst
  have o : ∀ k, k < 8 → InRegions s₀.wr (addr st (4 * k)) 4 :=
    fun k hk => ⟨⟨st.setWidth 64, 96⟩, by simp [hwr], contains_addr (by omega) (by omega) hfit⟩
  rw [init_eq]
  refine WP.seq (wp_movm (a := addr (s₀.gpr .esp) 4) (ea_at _ _ _)
    ⟨⟨argAddr s₀ 0, 4⟩, by simp [hrd], Region.contains_self _ _⟩ fun s₁ u₁ => WP.block_nil ?_)
  have e1 : s₁.gpr .eax = st := u₁.gpr
  have w1 : s₁.wr = s₀.wr := u₁.wr
  rw [← List.append_nil (_ ++ word H0[7] 7)]
  simp only [List.append_assoc]
  refine word_ok e1 (by rw [w1]; exact o 0 (by omega)) fun s2 a2 g2 _ wr2 m2 => ?_
  refine word_ok a2 (by rw [wr2, w1]; exact o 1 (by omega)) fun s3 a3 g3 _ wr3 m3 => ?_
  refine word_ok a3 (by rw [wr3, wr2, w1]; exact o 2 (by omega)) fun s4 a4 g4 _ wr4 m4 => ?_
  refine word_ok a4 (by rw [wr4, wr3, wr2, w1]; exact o 3 (by omega)) fun s5 a5 g5 _ wr5 m5 => ?_
  refine word_ok a5 (by rw [wr5, wr4, wr3, wr2, w1]; exact o 4 (by omega)) fun s6 a6 g6 _ wr6 m6 => ?_
  refine word_ok a6 (by rw [wr6, wr5, wr4, wr3, wr2, w1]; exact o 5 (by omega))
    fun s7 a7 g7 _ wr7 m7 => ?_
  refine word_ok a7 (by rw [wr7, wr6, wr5, wr4, wr3, wr2, w1]; exact o 6 (by omega))
    fun s8 a8 g8 _ wr8 m8 => ?_
  refine word_ok a8 (by rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, w1]; exact o 7 (by omega))
    fun s9 _ g9 _ _ m9 => WP.block_nil ?_
  have k9 : ∀ r, r ≠ .ecx → r ≠ .eax → s9.gpr r = s₀.gpr r := fun r h h' => by
    rw [g9 r h, g8 r h, g7 r h, g6 r h, g5 r h, g4 r h, g3 r h, g2 r h, u₁.other r h']
  have ha : ∀ k, k < 8 → addr st (4 * k) = st.setWidth 64 + BitVec.ofNat 64 (4 * k) :=
    fun k hk => addr_eq (by omega)
  have hm : s9.mem = Proof.Sha256.AArch64.writeState s₀.mem (st.setWidth 64) H0 := by
    rw [m9, m8, m7, m6, m5, m4, m3, m2, u₁.mem, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega),
      ha 3 (by omega), ha 4 (by omega), ha 5 (by omega), ha 6 (by omega), ha 7 (by omega)]
    rfl
  have hf : Frame [⟨st.setWidth 64, 96⟩] s₀.mem s9.mem := by
    rw [m9, m8, m7, m6, m5, m4, m3, m2, u₁.mem]
    have c : ∀ k, k < 8 → (⟨st.setWidth 64, 96⟩ : Region).Contains (addr st (4 * k)) (32 / 8) :=
      fun k hk => contains_addr (by omega) (by omega) hfit
    exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega))).writeW (List.mem_singleton_self _) _ (c 3 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega))).writeW (List.mem_singleton_self _) _
      (c 5 (by omega))).writeW (List.mem_singleton_self _) _ (c 6 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 7 (by omega))
  refine ⟨⟨fun r hr => k9 r ?_ ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)
  · show Spec.Sha256.Repr s9.mem (st.setWidth 64) []
    rw [hm]
    exact Proof.Sha256.Stream.repr_nil (Proof.Sha256.AArch64.stateAt_writeState _ _ _)

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
  wr := [⟨0x1000, 96⟩]

theorem initSat_pre : Spec.Sha256.initX86.pre initSat := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have e : argAddr initSat 0 = 0x4004 := by decide
  simp only [Spec.Sha256.initX86, a0, e]
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, initSat] at h₁ h₂
    bv_omega

/-- The initial taint: the argument is public, and the word holding `state`
is the base address of the writable region. -/
def initτ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 8 }

theorem init_agree₀ {s₁ s₂ : State} (h₁ : Spec.Sha256.initX86.pre s₁) (h₂ : Spec.Sha256.initX86.pre s₂)
    (hpub : Spec.Sha256.initX86.pub s₁ s₂) : VG.X86.Taint.Agree initτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0⟩ := hpub
  have wf : ∀ s, Spec.Sha256.initX86.pre s → VG.X86.Taint.Wf initτ₀ s := by
    intro s hs
    obtain ⟨-, hw, hd, hr, -, hsp⟩ := hs
    refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
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
    rw [VG.X86.Taint.argByte_eq h₁.2.2.2.2.2 h4 hk, VG.X86.Taint.argByte_eq h₂.2.2.2.2.2 h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega)),
      show (k - 4) / 4 = 0 by omega]
    exact congrArg _ a0

set_option maxHeartbeats 0 in
theorem init_verified : Verified X86.target init Spec.Sha256.initX86 := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, initSat_pre⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct hs
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) initτ₀ (fun _ _ h₁ h₂ hp => init_agree₀ h₁ h₂ hp)
      (by taint_decide)

end VG.Proof.Sha256.X86.Stream
