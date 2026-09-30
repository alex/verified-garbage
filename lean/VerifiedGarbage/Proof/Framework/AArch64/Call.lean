import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# Calls and frames (AArch64)

Untrusted: everything here is checked by Lean.

A call (`bl`) stores nothing in memory: it leaves unknown values in `x30`
(the return address), `x16`, `x17` and PSTATE.C (`State.callEntry`). `WP.call` runs a
call of verified code from the callee's `Verified` proof, as `WP.inline` does
for inlined code; the callee may have calls of its own, but no frames.

A frame (`str xr, [sp, #-16]!` … `ldr xr', [sp], #16`) runs its body from
`pushed r s` and ends in `popped r' s₂` (`WP.frame`). `WP.narrow` runs code
without frames that was proven on narrower permissions, such as the body of a
frame proven without the frame's region.
-/

namespace VG.AArch64

/-- The state a called function starts in: `x30`, `x16` and `x17` hold the
next three unknown values, and a bit of the fourth supplies PSTATE.C. -/
def State.callEntry (s : State) : State :=
  { s with
    gpr := fun r =>
      if r = .x30 then s.unknowns 0 else if r = .x16 then s.unknowns 1
      else if r = .x17 then s.unknowns 2 else s.gpr r
    c := (s.unknowns 3).getLsbD 0
    unknowns := fun n => s.unknowns (n + 4) }

theorem call_callEntry (s : State) : isa.call s = some s.callEntry := rfl

@[simp] theorem State.callEntry_rd (s : State) : s.callEntry.rd = s.rd := rfl
@[simp] theorem State.callEntry_wr (s : State) : s.callEntry.wr = s.wr := rfl
@[simp] theorem State.callEntry_sp (s : State) : s.callEntry.sp = s.sp := rfl
@[simp] theorem State.callEntry_mem (s : State) : s.callEntry.mem = s.mem := rfl

theorem State.callEntry_gpr (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r := by
  simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [State.callEntry, h.1, h.2.1, h.2.2]

theorem State.callEntry_withRegions (s : State) (rd wr : List Region) :
    (s.withRegions rd wr).callEntry = s.callEntry.withRegions rd wr := rfl

/-- Calls change none of the callee-saved registers but `x30`. -/
theorem preserved_not_link : ∀ r ∈ preserved, r ≠ .x30 → r ∉ linkRegs := by decide

/-- Calling verified code: from a state `s` in which the callee's
precondition holds on entry, once its permissions are narrowed to `rd` and
`wr`, the call terminates in a state satisfying the callee's postcondition
(on the narrowed states), which has the permissions and stack pointer of
`s`, differs from it in memory only within `wr`, and keeps the callee-saved
registers other than `x30` and every register other than `linkRegs` that no
instruction of the callee writes. -/
theorem WP.call {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      (∀ r, r ∉ linkRegs → (∀ i ∈ instrs c, dstOf i ≠ some r) → s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noFrames = true := by decide +kernel) : WP isa (.call name c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, -, hf⟩ := Exec.regions he hn
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  have e₀ : (s.callEntry.withRegions rd wr).withRegions s.rd s.wr = s.callEntry := rfl
  rw [e₀] at he'
  have h30 : s₁.gpr .x30 = s.callEntry.gpr .x30 := habi.1 .x30 (by simp [preserved])
  have hret : isa.ret s.callEntry (s₁.withRegions s.rd s.wr) = some (s₁.withRegions s.rd s.wr) := by
    simp only [isa, ret, State.withRegions_gpr, h30, ite_true]
  refine ⟨_, _, Exec.call (call_callEntry s) he' hret, hQ _ rfl rfl ?_ hf ?_ ?_ ?_⟩
  · simp only [State.withRegions_sp]; exact habi.2
  · intro r hr' h30'
    have hl : r ∉ linkRegs := preserved_not_link r hr' h30'
    simp only [State.withRegions_gpr]
    rw [habi.1 r hr', State.withRegions_gpr, State.callEntry_gpr s hl]
  · intro r hl hd
    rw [Exec.gpr hd he' (.inr hl), State.callEntry_gpr s hl]
  · have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
    rw [this]; exact hpost

/-- The state a frame's body starts in, after `str xr, [sp, #-16]!`. -/
def pushed (r : Reg) (s : State) : State :=
  { s with sp := s.sp - 16, mem := s.mem.write (s.sp - 16) 8 (s.gpr r),
           wr := ⟨s.sp - 16, 16⟩ :: s.wr }

/-- The state after a frame's `ldr xr, [sp], #16`, from the state `s` its
body ends in. -/
def popped (r : Reg) (s : State) : State :=
  { s.write .x r (s.mem.read s.sp 8) with sp := s.sp + 16, wr := s.wr.tail }

theorem push_pushed {r : Reg} {s : State} (h : 16 ≤ s.sp.toNat) :
    isa.push (.push r) s = some (pushed r s) := by
  show push (.push r) s = some (pushed r s)
  unfold push
  exact ite_eq_left_of_eq_true _ _ (eq_true h) |>.trans rfl

/-- A frame: its body runs from `pushed r s`, and the pop leads to
`popped r' s₂`. -/
theorem WP.frame {r r' : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hsp : 16 ≤ s.sp.toNat) (hb : WP isa body (pushed r s) fun s₂ => Q (popped r' s₂)) :
    WP isa (.frame (.push r) body (.pop r')) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := hb
  obtain ⟨-, hw, hp⟩ := Exec.rdwr he
  have hpop : isa.pop (.pop r') (pushed r s) s₂ = some (popped r' s₂) := by
    show pop (.pop r') (pushed r s) s₂ = some (popped r' s₂)
    unfold pop
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hp, hw, rfl⟩) |>.trans rfl
  exact ⟨_, _, Exec.frame (push_pushed hsp) he hpop, hq⟩

/-- Running code without frames that was proven on narrower permissions: if,
from `s` with its permissions narrowed to `rd` and `wr`, the code terminates
in a state satisfying `P`, then from `s` it terminates in a state that has
the permissions and stack pointer of `s`, differs from it in memory only
within `wr`, and, narrowed likewise, satisfies `P`. -/
theorem WP.narrow {c : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (h : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      P (s'.withRegions rd wr) → Q s')
    (hn : c.noFrames = true := by decide +kernel) : WP isa c s Q := by
  obtain ⟨t, s₁, he, hp⟩ := h
  obtain ⟨hr, hwr, hsp, hf⟩ := Exec.regions he hn
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.withRegions_sp] at hr hwr hf hsp
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨t, _, he', hQ _ rfl rfl hsp hf ?_⟩
  have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  rw [this]; exact hp

theorem read_write_self (m : Mem) (a : Addr) (v : BitVec (8 * 8)) : (m.write a 8 v).read a 8 = v :=
  Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega), hi, ite_true]

/-! ## Callees with frames -/

/-- The `n` bytes below `sp`. -/
abbrev below (sp : Addr) (n : Nat) : Region := ⟨sp - BitVec.ofNat 64 n, n⟩

theorem ofNat_split {a b : Nat} (hab : a ≤ b) :
    BitVec.ofNat 64 b = BitVec.ofNat 64 a + BitVec.ofNat 64 (b - a) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem below_sub {sp : Addr} {a b : Nat} (hab : a ≤ b) (hb : b < 2 ^ 64) :
    Region.Sub (below sp a) (below sp b) := by
  exact Offset.below_mono sp hab hb

/-- A frame's 16 bytes are in the `n + 16` bytes below the stack pointer. -/
theorem below_frame (sp : Addr) (n : Nat) (hn : n + 16 < 2 ^ 64) :
    Region.Sub ⟨sp - 16, 16⟩ (below sp (n + 16)) := by
  have := below_sub (sp := sp) (a := 16) (b := n + 16) (by omega) hn
  simpa using this

theorem below_frame_contains (sp : Addr) (n : Nat) (hn : n + 16 < 2 ^ 64) :
    (below sp (n + 16)).Contains (sp - 16) 8 := by
  simp only [Region.Contains]
  rw [show sp - 16 - (sp - BitVec.ofNat 64 (n + 16)) = BitVec.ofNat 64 n from
    (Offset.sub_ofNat_sub_sub_ofNat sp (a := 16) (by omega)).trans (by rw [Nat.add_sub_cancel]),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The stack a frame's body uses is below the frame. -/
theorem below_body (sp : Addr) (n : Nat) : Region.Sub (below (sp - 16) n) (below sp (n + 16)) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 (n + 16)) = x - (sp - 16 - BitVec.ofNat 64 n) by
    rw [BitVec.sub_sub (sp : Addr) 16, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 n)]; rfl]
  omega

theorem Frame.below_mono {wr : List Region} {sp : Addr} {a b : Nat} {m m' : Mem}
    (h : Frame (wr ++ [below sp a]) m m') (hab : a ≤ b) (hb : b < 2 ^ 64) :
    Frame (wr ++ [below sp b]) m m' :=
  Frame.sub h fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub hab hb⟩

theorem push_mem {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ v, s₁.mem = s.mem.write (s.sp - 16) 8 v ∧ s₁.wr = ⟨s.sp - 16, 16⟩ :: s.wr ∧ s₁.sp = s.sp - 16 := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  split at h <;> cases h; exact ⟨_, rfl, rfl, rfl⟩

theorem pop_mem {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : s'.mem = s₂.mem := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h; rfl

/-- Code changes memory only within the regions it may write and within
`16 * fdepth` bytes below the stack pointer (its frames). -/
theorem Exec.frameSp {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hd : 16 * c.fdepth < 2 ^ 64) :
    Frame (s.wr ++ [below s.sp (16 * c.fdepth)]) s.mem s'.mem := by
  induction h with
  | block h => exact Frame.mono (execBlock_regions h).2.2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    simp only [Code.fdepth] at hd ⊢
    have f₁ := Frame.below_mono (ih₁ (by omega)) (b := 16 * max c₁.fdepth c₂.fdepth) (by omega)
      (by omega)
    have f₂ := Frame.below_mono (ih₂ (by omega)) (b := 16 * max c₁.fdepth c₂.fdepth) (by omega)
      (by omega)
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    rw [w₁, p₁] at f₂
    exact Frame.trans f₁ f₂
  | iteT _ _ ih =>
    simp only [Code.fdepth] at hd ⊢
    exact Frame.below_mono (ih (by omega)) (by omega) (by omega)
  | iteF _ _ ih =>
    simp only [Code.fdepth] at hd ⊢
    exact Frame.below_mono (ih (by omega)) (by omega) (by omega)
  | loopExit _ _ ih => exact ih hd
  | loopNext h₁ _ _ ih₁ ih₂ =>
    have f₂ := ih₂ hd
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    rw [w₁, p₁] at f₂
    exact Frame.trans (ih₁ hd) f₂
  | call hc _ hr ih =>
    simp only [Code.fdepth] at hd ⊢
    obtain ⟨-, w₁, p₁, m₁, -⟩ := call_eq hc
    rw [ret_eq hr]
    have := ih hd
    rwa [w₁, p₁, m₁] at this
  | @frame _ _ b s₀ s₁ s₂ _ _ hp _ hq ih =>
    simp only [Code.fdepth] at hd ⊢
    rw [show 16 * (b.fdepth + 1) = 16 * b.fdepth + 16 by omega] at hd ⊢
    obtain ⟨v, m₁, w₁, p₁⟩ := push_mem hp
    rw [pop_mem hq]
    have f₁ := ih (by omega)
    rw [w₁, p₁, m₁] at f₁
    have f₀ : Frame (s₀.wr ++ [below s₀.sp (16 * b.fdepth + 16)]) s₀.mem
        (s₀.mem.write (s₀.sp - 16) 8 v) :=
      Frame.write (Frame.refl _ _) (List.mem_append_right _ (List.mem_singleton_self _)) _
        (below_frame_contains s₀.sp _ hd)
    refine Frame.trans f₀ (Frame.sub f₁ fun r hr => ?_)
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr | rfl
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_frame s₀.sp _ hd⟩
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_body s₀.sp _⟩

/-- Calling verified code that may have frames: as `WP.call`, but the
callee may also change the `16 * fdepth` bytes below the stack pointer. -/
theorem WP.callF {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [below s.sp (16 * c.fdepth)]) s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hd : 16 * c.fdepth < 2 ^ 64 := by decide +kernel) : WP isa (.call name c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  have hf := Exec.frameSp he hd
  obtain ⟨hr, hwr, -⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.withRegions_sp, State.callEntry_mem, State.callEntry_sp] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  have e₀ : (s.callEntry.withRegions rd wr).withRegions s.rd s.wr = s.callEntry := rfl
  rw [e₀] at he'
  have h30 : s₁.gpr .x30 = s.callEntry.gpr .x30 := habi.1 .x30 (by simp [preserved])
  have hret : isa.ret s.callEntry (s₁.withRegions s.rd s.wr) = some (s₁.withRegions s.rd s.wr) := by
    simp only [isa, ret, State.withRegions_gpr, h30, ite_true]
  refine ⟨_, _, Exec.call (call_callEntry s) he' hret, hQ _ rfl rfl ?_ hf ?_ ?_⟩
  · simp only [State.withRegions_sp]; exact habi.2
  · intro r hr' h30'
    have hl : r ∉ linkRegs := preserved_not_link r hr' h30'
    simp only [State.withRegions_gpr]
    rw [habi.1 r hr', State.withRegions_gpr, State.callEntry_gpr s hl]
  · have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
    rw [this]; exact hpost

/-- Running code that was proven on narrower permissions: if, from `s` with
its permissions narrowed to `rd` and `wr`, the code terminates in a state
satisfying `P`, then from `s` it terminates in a state that has the
permissions and stack pointer of `s`, differs from it in memory only within
`wr` and the `16 * fdepth` bytes below the stack pointer, and, narrowed
likewise, satisfies `P`. -/
theorem WP.narrowF {c : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (h : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [below s.sp (16 * c.fdepth)]) s.mem s'.mem → P (s'.withRegions rd wr) → Q s')
    (hd : 16 * c.fdepth < 2 ^ 64) : WP isa c s Q := by
  obtain ⟨t, s₁, he, hp⟩ := h
  have hf := Exec.frameSp he hd
  obtain ⟨hr, hwr, hsp⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.withRegions_sp] at hr hwr hf hsp
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at he'
  refine ⟨t, _, he', hQ _ rfl rfl hsp hf ?_⟩
  have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
    rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
  rw [this]; exact hp

/-- The bytes a frame's register is stored in are not below the frame. -/
theorem frame_not_below (sp : Addr) {n : Nat} (hn : n + 16 < 2 ^ 64) :
    Region.Disjoint ⟨sp - 16, 16⟩ (below (sp - 16) n) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have e : x - (sp - 16 - BitVec.ofNat 64 n) = (x - (sp - 16)) + BitVec.ofNat 64 n :=
    Offset.sub_sub_eq _ _ _
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
    Nat.mod_eq_of_lt (by omega)] at h₂
  omega

/-- A frame saving `r` around `main`: `main` runs from `s₀` with the stack
pointer moved down by 16 and `r` stored there, in the permissions of `s₀`
(the frame's region must be disjoint from the regions `s₀` may write), and
the pop restores `r` and the stack pointer. -/
theorem WP.frameReg {r : Reg} {main : Prog isa} {s₀ : State} {Q : State → Prop}
    (hsp : 16 ≤ s₀.sp.toNat) (hd : ∀ R ∈ s₀.wr, Region.Disjoint ⟨s₀.sp - 16, 16⟩ R)
    (hmain : WP isa main { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr r) }
      fun s₂ => Q { s₂.write .x r (s₀.gpr r) with sp := s₀.sp })
    (hn : 16 * main.fdepth + 16 < 2 ^ 64 := by decide +kernel) :
    WP isa (.frame (.push r) main (.pop r)) s₀ Q := by
  refine WP.frame hsp (WP.narrowF (rd := s₀.rd) (wr := s₀.wr) hmain ?_ ?_ ?_ (by omega))
  · intro a n hi
    exact InRegions_append_cons.mpr (.inr hi)
  · intro a n hi
    exact InRegions_append_cons (xs := []).mpr (.inr hi)
  · intro s' hrd hwr hsp' hf hq
    have hread : s'.mem.read s'.sp 8 = s₀.gpr r := by
      rw [hsp', show (pushed r s₀).sp = s₀.sp - 16 from rfl,
        hf.read (r := ⟨s₀.sp - 16, 16⟩) (by simp [Region.Contains]) (fun R hR => ?_) (by decide)]
      · exact read_write_self _ _ _
      · rcases List.mem_append.mp hR with hR | hR
        · exact hd R hR
        · simp only [List.mem_singleton] at hR; subst hR
          exact frame_not_below s₀.sp hn
    have e : popped r s' = { (s'.withRegions s₀.rd s₀.wr).write .x r (s₀.gpr r) with sp := s₀.sp } := by
      simp only [popped, hread]
      simp only [hsp', hwr, pushed, List.tail_cons, BitVec.sub_add_cancel]
      cases s'
      simp only [pushed] at hrd
      subst hrd
      rfl
    rw [e]; exact hq

end VG.AArch64
