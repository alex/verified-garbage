import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Constant time of code that leaks memory both runs agree on (ARMv7)

Untrusted: everything here is checked by Lean. The ARMv7 counterpart of the
x86-64 `memTaint` of ML-DSA (`Proof/MlDsa/X86_64/Pack/MemTaint.lean`), for
`vg_mldsa_hint_bit_pack` and `vg_mldsa_hint_bit_unpack`, which branch and
index memory on their input, which they load from memory.

The taint analysis (`Proof/Framework/Arm/Taint.lean`) treats loaded memory as
secret. `memTaint` is one for code that runs from states whose permitted
memory both runs agree on (`MemEq`): every load (`ldr`, `ldrb`) it makes is
then public, and a store keeps the agreement if it stores a public value at a
public address.

On ARMv7 these functions run in a frame, which holds the callee-saved
registers of each run, which differ; the analysis would take them for
public. So the code that needs it runs from states narrowed to the regions it
accesses (`RelCT.narrow`): a run with fewer permissions is the actual run
(`Exec.widen` and determinism). What is left of the frame, the instructions
that only access the stack (`spOnly`), leaks only addresses computed from
the stack pointer (`RelCT.spBlock`).
-/

namespace VG.Proof.MlDsa.Arm.Pack.Hint

open VG VG.Arm
open VG.Arm.Taint (T pub)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The taint agrees, and the permissions and the memory they permit. -/
def MAgree (τ : T) (s₁ s₂ : State) : Prop :=
  VG.Arm.Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- Loads are public; stores must store public values; the stack and frames
are not analysed. -/
def mstep (τ : T) : Instr → Option T
  | .ldr t n off => (VG.Arm.Taint.stepK τ (.ldr t n off)).map fun τ' => { τ' with regs := τ'.regs.insert t }
  | .ldrb t n off => (VG.Arm.Taint.stepK τ (.ldrb t n off)).map fun τ' => { τ' with regs := τ'.regs.insert t }
  | .str t n off => if pub τ t then VG.Arm.Taint.stepK τ (.str t n off) else none
  | .strb t n off => if pub τ t then VG.Arm.Taint.stepK τ (.strb t n off) else none
  | .ldrSp .. | .push _ | .pop .. => none
  | i => VG.Arm.Taint.stepK τ i

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
theorem agree_insert {τ : T} {s₁ s₂ : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂) {d : Reg}
    (hd : s₁.gpr d = s₂.gpr d) : VG.Arm.Taint.Agree { τ with regs := τ.regs.insert d } s₁ s₂ :=
  ⟨⟨fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact hd
      · exact ha.rf.1 r hr, ha.rf.2⟩, ha.wr, ⟨ha.wf₁.lens, ha.wf₁.bases, ha.wf₁.args, ha.wf₁.argBases⟩,
    ⟨ha.wf₂.lens, ha.wf₂.bases, ha.wf₂.args, ha.wf₂.argBases⟩, ha.ok, ha.slots, ha.sp, ha.argMem⟩

/-- The instructions that neither access memory nor change the stack. -/
theorem exec_pure {i : Instr} (hi : ∀ t n off, i ≠ .ldr t n off ∧ i ≠ .ldrb t n off ∧ i ≠ .str t n off ∧
      i ≠ .strb t n off ∧ i ≠ .ldrSp t off)
    {s s' : State} (h : exec i s = some s') : s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | ldr t n off => exact absurd rfl (hi t n off).1
  | ldrb t n off => exact absurd rfl (hi t n off).2.1
  | str t n off => exact absurd rfl (hi t n off).2.2.1
  | strb t n off => exact absurd rfl (hi t n off).2.2.2.1
  | ldrSp t off => exact absurd rfl (hi t t off).2.2.2.2
  | push => simp only [exec, reduceCtorEq] at h
  | pop | alloc | free => simp only [exec, reduceCtorEq] at h
  | addSp d imm =>
    simp only [exec] at h
    split at h <;> cases h
    exact ⟨rfl, rfl, rfl⟩
  | _ =>
    simp only [exec, Option.map_eq_some_iff, Option.some.injEq] at h
    first
    | (obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩)
    | (subst h; exact ⟨rfl, rfl, rfl⟩)

theorem mstep_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : MAgree τ s₁ s₂)
    (hs : mstep τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ MAgree τ' s₁' s₂' := by
  obtain ⟨hA, hrd, hwr, hm⟩ := ha
  -- Instructions the base analysis handles, which keep the memory.
  have base : ∀ {j : Instr}, (∀ t n off, j ≠ .ldr t n off ∧ j ≠ .ldrb t n off ∧ j ≠ .str t n off ∧
      j ≠ .strb t n off ∧ j ≠ .ldrSp t off) → VG.Arm.Taint.stepK τ j = some τ' → exec j s₁ = some s₁' →
      exec j s₂ = some s₂' → addrs j s₁ = addrs j s₂ ∧ MAgree τ' s₁' s₂' := fun hj hs' e₁ e₂ => by
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound ⟨hA.rf, hA.wr, hA.wf₁, hA.wf₂, hA.ok, hA.slots, hA.sp, hA.argMem⟩
      (VG.Arm.Taint.stepK_eq ▸ hs') e₁ e₂
    obtain ⟨m₁, r₁, w₁⟩ := exec_pure hj e₁
    obtain ⟨m₂, r₂, w₂⟩ := exec_pure hj e₂
    exact ⟨hadd, ht, by rw [r₁, r₂, hrd], by rw [w₁, w₂, hwr], by rw [m₁, m₂, r₁, w₁]; exact hm⟩
  cases i with
  | ldr t n off =>
    simp only [mstep, Option.map_eq_some_iff] at hs
    obtain ⟨τ₀, h₀, rfl⟩ := hs
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ h₀) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load32] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [rename_i hi; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    refine ⟨by simp only [addrs, hadd], agree_insert ht ?_, hrd, hwr, hm⟩
    simp only [State.setReg, ite_true, Mem.readW, ← hadd, hm.read hi (by decide)]
  | ldrb t n off =>
    simp only [mstep, Option.map_eq_some_iff] at hs
    obtain ⟨τ₀, h₀, rfl⟩ := hs
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ h₀) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [exec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true, Option.map_eq_some_iff, State.load8] at e₁ e₂
    obtain ⟨x₁, hx₁, rfl⟩ := e₁; obtain ⟨x₂, hx₂, rfl⟩ := e₂
    split at hx₁ <;> [rename_i hi; cases hx₁]
    split at hx₂ <;> [skip; cases hx₂]
    cases hx₁; cases hx₂
    refine ⟨by simp only [addrs, hadd], agree_insert ht ?_, hrd, hwr, hm⟩
    simp only [State.setReg, ite_true, ← hadd, hm _ hi]
  | str t n off =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hp; cases hs]
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ hs) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [exec, State.store32] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    refine ⟨by simp only [addrs, hadd], ht, hrd, hwr, ?_⟩
    rw [hadd, hA.reg hp]
    exact hm.writeW _ _
  | strb t n off =>
    simp only [mstep] at hs
    split at hs <;> [rename_i hp; cases hs]
    obtain ⟨hadd, ht⟩ := VG.Arm.Taint.step_sound hA (VG.Arm.Taint.stepK_eq ▸ hs) e₁ e₂
    simp only [addrs, List.cons.injEq, and_true] at hadd
    simp only [exec, State.store8] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hoff
    simp only [hoff, ite_true] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    refine ⟨by simp only [addrs, hadd], ht, hrd, hwr, ?_⟩
    rw [hadd, hA.reg hp]
    exact hm.writeW _ _
  | ldrSp => simp only [mstep, reduceCtorEq] at hs
  | push => simp only [mstep, reduceCtorEq] at hs
  | pop => simp only [mstep, reduceCtorEq] at hs
  | mov => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | dp => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | adds => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | adc => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | subs => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | cmp => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | movw => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | movt => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | rev => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | mul => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | addSp => exact base (fun _ _ _ => by simp) hs e₁ e₂
  | alloc | free => simp only [exec, reduceCtorEq] at e₁

/-- Taint tracking over memory both runs agree on, for ARMv7. -/
def memTaint : VG.Taint isa where
  T := T
  Agree := MAgree
  step := mstep
  step_sound := mstep_sound
  condPub τ _ := τ.flags
  cond_sound ha hc := VG.Arm.Taint.cond_sound ha.1 hc
  meet := VG.Arm.Taint.meet
  meet_left h := ⟨VG.Arm.Taint.meet_left h.1, h.2⟩
  meet_right h := ⟨VG.Arm.Taint.meet_right h.1, h.2⟩
  le := VG.Arm.Taint.leK
  le_sound hle h := ⟨VG.Arm.Taint.le_sound (VG.Arm.Taint.leK_eq ▸ hle) h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

/-! ## Narrowing the permissions -/

/-- Two runs of `c` leak the same trace if its runs from the states narrowed
to the regions `rd`, `wr` do, and exist. -/
theorem RelCT.narrow {c : Prog isa} {P : State → State → Prop} (rd wr : State → List Region)
    (hc : ∀ a b, P a b → Covers (rd a ++ wr a) (a.rd ++ a.wr) ∧ Covers (wr a) a.wr ∧
      Covers (rd b ++ wr b) (b.rd ++ b.wr) ∧ Covers (wr b) b.wr)
    (hrun : ∀ a b, P a b → (∃ t s', Exec isa c (a.withRegions (rd a) (wr a)) t s') ∧
      ∃ t s', Exec isa c (b.withRegions (rd b) (wr b)) t s')
    (hct : RelCT isa (fun a' b' => ∃ a b, P a b ∧ a' = a.withRegions (rd a) (wr a) ∧
      b' = b.withRegions (rd b) (wr b)) c fun _ _ => True) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨c₁, w₁, c₂, w₂⟩ := hc _ _ hp
  obtain ⟨⟨u₁, n₁, f₁⟩, ⟨u₂, n₂, f₂⟩⟩ := hrun _ _ hp
  have g₁ := Exec.widen f₁ (rd := s₁.rd) (wr := s₁.wr) (by simpa using c₁) (by simpa using w₁)
  have g₂ := Exec.widen f₂ (rd := s₂.rd) (wr := s₂.wr) (by simpa using c₂) (by simpa using w₂)
  simp only [State.withRegions_withRegions, State.withRegions_self] at g₁ g₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ g₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ g₂
  exact ⟨(hct _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ f₁ f₂).1, trivial⟩

/-! ## Instructions that only access the stack -/

/-- The instructions whose addresses depend only on the stack pointer. -/
def spOnly : Instr → Bool
  | .ldr .. | .str .. | .ldrb .. | .strb .. | .push _ | .pop .. => false
  | _ => true

theorem addrs_spOnly {i : Instr} (hi : spOnly i = true) {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp) :
    addrs i s₁ = addrs i s₂ := by
  cases i <;> simp_all [spOnly, addrs]

theorem execBlock_spOnly {is : List Instr} (h : is.all spOnly = true) {s₁ s₂ s₁' s₂' : State}
    {t₁ t₂ : List Leak} (hsp : s₁.sp = s₂.sp) (e₁ : execBlock isa is s₁ = some (s₁', t₁))
    (e₂ : execBlock isa is s₂ = some (s₂', t₂)) : t₁ = t₂ := by
  induction is generalizing s₁ s₂ t₁ t₂ with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    rw [← e₁.2, ← e₂.2]
  | cons i is ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> [cases e₁; skip]
    split at e₂ <;> [cases e₂; skip]
    rename_i a₁ x₁ _ a₂ x₂
    simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at e₁ e₂
    obtain ⟨_, u₁, f₁, rfl, rfl⟩ := e₁
    obtain ⟨_, u₂, f₂, rfl, rfl⟩ := e₂
    have ha : addrs i s₁ = addrs i s₂ := addrs_spOnly h.1 hsp
    rw [ha, ih h.2 (by rw [exec_sp x₁, exec_sp x₂, hsp]) f₁ f₂]

/-- A block of instructions that only access the stack leaks the same trace
from states with the same stack pointer. -/
theorem RelCT.spBlock {is : List Instr} (h : is.all spOnly = true) {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp) : RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | block e₁ =>
    cases e₂ with
    | block e₂ => exact ⟨execBlock_spOnly h (hsp _ _ hp) e₁ e₂, trivial⟩

/-! ## Helpers -/

theorem relct_wp {c : Prog isa} {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa P c fun _ _ => True) (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa P c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

theorem covers_of_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  fun _ _ ⟨r, hr, hc⟩ => ⟨r, h r hr, hc⟩

end VG.Proof.MlDsa.Arm.Pack.Hint
