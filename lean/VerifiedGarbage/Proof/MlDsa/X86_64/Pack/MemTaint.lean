import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Taint tracking over memory both runs agree on (x86-64)

The x86-64 counterpart of ML-KEM's AArch64 `memTaint`
(`Proof/MlKem/AArch64/MemTaint.lean`).

The taint analysis (`Proof/Framework/X86_64/Taint.lean`) treats memory as
secret. `memTaint` is one for code that runs from states whose permitted
memory both runs agree on (`MemEq`): every byte load (`movzx8`) and 32-bit
load (`mov32` from memory) it makes is then public, and a byte or 32-bit
store keeps the agreement if it stores a public value at a public address.
It proves constant time for code whose branches and addresses depend on the
contents of such memory: `vg_mldsa_hint_bit_pack` and
`vg_mldsa_hint_bit_unpack`, which may leak their input (the only memory
they read) once they have zeroed their output (the only memory they
write).
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64
open VG.X86_64.Taint (T pub dstOf exec_nonstore memPub)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The registers `τ` agree, and the permissions and the memory they permit. -/
def MAgree (τ : T) (s₁ s₂ : State) : Prop :=
  X86_64.Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- The loads whose value the analysis makes public, and the register they
write. -/
def loadDst : Instr → Option Reg
  | .movzx8 d _ => some d
  | .mov32 d (.mem _) => some d
  | _ => none

/-- Loads are public; byte and 32-bit stores must store public values; other
instructions that write memory are not analysed. -/
def mstep (τ : T) (i : Instr) : Option T :=
  match loadDst i with
  | some d => (X86_64.Taint.step τ i).map fun τ' => { τ' with regs := τ'.regs.insert d }
  | none => match i with
    | .store8 _ r | .store32 _ r => if pub τ r then X86_64.Taint.step τ i else none
    | _ => if (dstOf i).isSome then X86_64.Taint.step τ i else none

theorem MemEq.read {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) {a : Addr} {n : Nat}
    (hi : InRegions rs a n) (hn : n < 2 ^ 64) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := hi
  exact Mem.read_congr fun i hi' =>
    h _ ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hi')⟩

theorem MemEq.writeW {rs : List Region} {m₁ m₂ : Mem} (h : MemEq rs m₁ m₂) (a : Addr) {w : Nat}
    (v : BitVec w) : MemEq rs (m₁.writeW a v) (m₂.writeW a v) := fun x hx => by
  simp only [Mem.writeW, Mem.write]
  split
  · rfl
  · exact h x hx

/-- A register made public, whose values agree. -/
theorem agree_insert {τ : T} {s₁ s₂ : State} (ha : X86_64.Taint.Agree τ s₁ s₂) {d : Reg}
    (hd : s₁.gpr d = s₂.gpr d) : X86_64.Taint.Agree { τ with regs := τ.regs.insert d } s₁ s₂ :=
  ⟨⟨fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact hd
      · exact ha.rf.1 r hr, ha.rf.2⟩, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots, ha.lo⟩

theorem memPub_of_step {τ τ' : T} {i : Instr} {d : Reg} {m : MemOp}
    (hi : i = .movzx8 d m ∨ i = .mov32 d (.mem m)) (hs : X86_64.Taint.step τ i = some τ') :
    memPub τ m = true := by
  cases hmp : memPub τ m
  · rcases hi with rfl | rfl <;> simp [X86_64.Taint.step, X86_64.Taint.srcOk, hmp] at hs
  · rfl

theorem mstep_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : MAgree τ s₁ s₂)
    (hs : mstep τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ MAgree τ' s₁' s₂' := by
  unfold mstep at hs
  split at hs
  · -- A load.
    rename_i d hd
    obtain ⟨τ₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨hadd, ht⟩ := X86_64.Taint.step_sound ha.1 h₀ e₁ e₂
    have hdst : dstOf i = some d := by
      cases i <;> simp only [loadDst, reduceCtorEq] at hd
      · rename_i src; cases src <;> simp only [reduceCtorEq, Option.some.injEq] at hd; subst hd; rfl
      · simp only [Option.some.injEq] at hd; subst hd; rfl
    obtain ⟨r₁, w₁, m₁, -⟩ := exec_nonstore hdst e₁
    obtain ⟨r₂, w₂, m₂, -⟩ := exec_nonstore hdst e₂
    refine ⟨hadd, agree_insert ht ?_, by rw [r₁, r₂, ha.2.1], by rw [w₁, w₂, ha.2.2.1], by
      rw [m₁, m₂, r₁, w₁]; exact ha.2.2.2⟩
    cases i <;> simp only [loadDst, reduceCtorEq] at hd
    · rename_i d' src
      cases src <;> simp only [reduceCtorEq, Option.some.injEq] at hd
      subst hd
      rename_i m
      have hm := memPub_of_step (.inr rfl) h₀
      have ea := ha.1.ea hm
      simp only [exec, readSrc32, State.load32, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨v₁, l₁, rfl⟩ := e₁; obtain ⟨v₂, l₂, rfl⟩ := e₂
      split at l₁ <;> [rename_i hi; cases l₁]
      split at l₂ <;> [skip; cases l₂]
      cases l₁; cases l₂
      simp only [State.setReg32, State.setReg, ite_true, Mem.readW, ← ea, ha.2.2.2.read hi (by decide)]
    · rename_i m
      simp only [Option.some.injEq] at hd; subst hd
      have hm := memPub_of_step (.inl rfl) h₀
      have ea := ha.1.ea hm
      simp only [exec, State.load8, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨v₁, l₁, rfl⟩ := e₁; obtain ⟨v₂, l₂, rfl⟩ := e₂
      split at l₁ <;> [rename_i hi; cases l₁]
      split at l₂ <;> [skip; cases l₂]
      cases l₁; cases l₂
      simp only [State.setReg, ite_true, ← ea, ha.2.2.2 _ hi]
  · split at hs
    · -- A store.
      rename_i m r _
      split at hs <;> [rename_i hr; cases hs]
      obtain ⟨hadd, ht⟩ := X86_64.Taint.step_sound ha.1 hs e₁ e₂
      have hm : memPub τ m = true := by
        cases hmp : memPub τ m
        · simp [X86_64.Taint.step, X86_64.Taint.storeStep, hmp] at hs
        · rfl
      have ea := ha.1.ea hm
      simp only [exec, State.store8] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      refine ⟨hadd, ht, ha.2.1, ha.2.2.1, ?_⟩
      rw [ea, ha.1.reg hr]
      exact ha.2.2.2.writeW _ _
    · rename_i m r _
      split at hs <;> [rename_i hr; cases hs]
      obtain ⟨hadd, ht⟩ := X86_64.Taint.step_sound ha.1 hs e₁ e₂
      have hm : memPub τ m = true := by
        cases hmp : memPub τ m
        · simp [X86_64.Taint.step, X86_64.Taint.storeStep, hmp] at hs
        · rfl
      have ea := ha.1.ea hm
      simp only [exec, State.store32] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      refine ⟨hadd, ht, ha.2.1, ha.2.2.1, ?_⟩
      rw [ea, ha.1.reg hr]
      exact ha.2.2.2.writeW _ _
    · -- An instruction that writes one register.
      split at hs <;> [rename_i hd; cases hs]
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hd
      obtain ⟨hadd, ht⟩ := X86_64.Taint.step_sound ha.1 hs e₁ e₂
      obtain ⟨r₁, w₁, m₁, -⟩ := exec_nonstore hd e₁
      obtain ⟨r₂, w₂, m₂, -⟩ := exec_nonstore hd e₂
      exact ⟨hadd, ht, by rw [r₁, r₂, ha.2.1], by rw [w₁, w₂, ha.2.2.1], by
        rw [m₁, m₂, r₁, w₁]; exact ha.2.2.2⟩

/-- Taint tracking over memory both runs agree on, for x86-64. -/
def memTaint : VG.Taint isa where
  T := T
  Agree := MAgree
  step := mstep
  step_sound := mstep_sound
  condPub τ _ := τ.flags
  cond_sound ha hc := X86_64.Taint.cond_sound ha.1 hc
  meet := X86_64.Taint.meet
  meet_left h := ⟨X86_64.Taint.meet_left h.1, h.2⟩
  meet_right h := ⟨X86_64.Taint.meet_right h.1, h.2⟩
  le := X86_64.Taint.leK
  le_sound hle h := ⟨X86_64.Taint.le_sound (X86_64.Taint.leK_eq ▸ hle) h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

end VG.Proof.MlDsa.X86_64.Pack
