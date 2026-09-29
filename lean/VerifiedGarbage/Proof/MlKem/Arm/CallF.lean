import VerifiedGarbage.Proof.Framework.Arm.Frame

/-!
# Calls of code with frames (ARMv7)

Untrusted: everything here is checked by Lean. `WP.call` and
`WP.callCalls` (`Proof/Framework/Arm/`) are for callees without frames. A
callee with frames also stores below the stack pointer: at most
`stackUse c` bytes (the frames' pushes, nested), so it changes memory only
within the regions it may write and those bytes (`Exec.frameSp`), and
`WP.callF` runs a call of it from its proof of `Verified`.
-/

namespace VG.Arm

/-- The bytes of stack below the stack pointer that the frames of `c` (and
of the functions it calls) use. -/
def stackUse : Prog isa → Nat
  | .block _ => 0
  | .seq a b => max (stackUse a) (stackUse b)
  | .ite _ a b => max (stackUse a) (stackUse b)
  | .loop b _ => stackUse b
  | .call _ b => stackUse b
  | .frame (.push rs) b _ => 4 * rs.length + stackUse b
  | .frame _ b _ => stackUse b

/-- The `n` bytes below `sp`. -/
def belowA (sp : BitVec 32) (n : Nat) : Region := ⟨State.addr sp - BitVec.ofNat 64 n, n⟩

theorem addr_toNat' (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

theorem belowA_sub {sp : BitVec 32} {a b : Nat} (hab : a ≤ b) :
    Region.Sub (belowA sp a) (belowA sp b) := by
  intro x hx
  have := addr_toNat' sp
  have := sp.isLt
  simp only [belowA, Region.Contains] at hx ⊢
  bv_omega

/-- The bytes below a pushed stack pointer are below the stack pointer. -/
theorem belowA_push {sp : BitVec 32} {k a : Nat} (h : k + a ≤ sp.toNat) :
    Region.Sub (belowA (sp - BitVec.ofNat 32 k) a) (belowA sp (k + a)) := by
  intro x hx
  have := addr_toNat' sp
  have := addr_toNat' (sp - BitVec.ofNat 32 k)
  have := sp.isLt
  simp only [belowA, Region.Contains] at hx ⊢
  bv_omega

/-- A frame's region is below the stack pointer. -/
theorem frame_belowA {sp : BitVec 32} {k a : Nat} (h : k + a ≤ sp.toNat) :
    Region.Sub ⟨State.addr (sp - BitVec.ofNat 32 k), k⟩ (belowA sp (k + a)) := by
  intro x hx
  have := addr_toNat' sp
  have := addr_toNat' (sp - BitVec.ofNat 32 k)
  have := sp.isLt
  simp only [belowA, Region.Contains] at hx ⊢
  bv_omega

theorem storeWords_frame (m : Mem) (a : BitVec 32) (vs : List (BitVec 32)) (h : a.toNat + 4 * vs.length ≤ 2 ^ 32) :
    Frame [⟨State.addr a, 4 * vs.length⟩] m (storeWords m a vs) := by
  induction vs generalizing m a with
  | nil => exact Frame.refl _ _
  | cons v vs ih =>
    simp only [storeWords, List.length_cons] at h ⊢
    have f₁ : Frame [⟨State.addr a, 4 * (vs.length + 1)⟩] m (m.writeW (State.addr a) v) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    refine f₁.trans ((ih _ (a + 4) (by bv_omega)).sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton] at hr; subst hr
    intro x hx
    have := addr_toNat' a
    have := addr_toNat' (a + 4)
    simp only [Region.Contains] at hx ⊢
    bv_omega

theorem pop_mem' {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : s'.mem = s₂.mem := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  split at h <;> cases h; rfl

theorem push_pushed' {rs : List Reg} {s a : State} (h : isa.push (.push rs) s = some a) :
    a = pushed rs s ∧ 4 * rs.length ≤ s.sp.toNat := by
  simp only [isa, push] at h
  split at h
  · rename_i hc; exact ⟨(Option.some.inj h).symm, hc.2⟩
  · cases h

/-- Code changes memory only within the regions it may write and within
`stackUse c` bytes below the stack pointer (its frames). -/
theorem Exec.frameSp {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hd : stackUse c ≤ s.sp.toNat) :
    Frame (s.wr ++ [belowA s.sp (stackUse c)]) s.mem s'.mem := by
  induction h with
  | block h => exact Frame.mono (execBlock_regions h).2.2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    simp only [stackUse] at hd ⊢
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    have f₁ := ih₁ (by omega)
    have f₂ := ih₂ (by rw [p₁]; omega)
    rw [w₁, p₁] at f₂
    refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega)⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega)⟩
  | iteT _ _ ih =>
    simp only [stackUse] at hd ⊢
    refine (ih (by omega)).sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega)⟩
  | iteF _ _ ih =>
    simp only [stackUse] at hd ⊢
    refine (ih (by omega)).sub fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega)⟩
  | loopExit _ _ ih => exact ih hd
  | loopNext h₁ _ _ ih₁ ih₂ =>
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    have f₂ := ih₂ (by rw [p₁]; exact hd)
    rw [w₁, p₁] at f₂
    exact (ih₁ hd).trans f₂
  | call hc _ hr ih =>
    simp only [stackUse] at hd ⊢
    obtain ⟨-, w₁, p₁, m₁, -⟩ := call_eq hc
    rw [ret_eq hr]
    have := ih (by rw [p₁]; exact hd)
    rwa [w₁, p₁, m₁] at this
  | @frame i j b s₀ s₁ s₂ _ _ hp _ hq ih =>
    rw [pop_mem' hq]
    cases i with
    | push rs =>
      simp only [stackUse] at hd ⊢
      obtain ⟨rfl, hk⟩ := push_pushed' hp
      have f₁ := ih (by rw [pushed_sp]; have := s₀.sp.isLt; bv_omega)
      rw [pushed_wr, pushed_sp] at f₁
      have f₀ : Frame [⟨State.addr (s₀.sp - BitVec.ofNat 32 (4 * rs.length)), 4 * (rs.map s₀.gpr).length⟩] s₀.mem
          (pushed rs s₀).mem := storeWords_frame _ _ _ (by
        rw [List.length_map]; have := s₀.sp.isLt; bv_omega)
      rw [List.length_map] at f₀
      refine (f₀.sub fun r hr => ?_).trans (f₁.sub fun r hr => ?_)
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), frame_belowA hd⟩
      · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | hr | rfl
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), frame_belowA hd⟩
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_push hd⟩
    | _ => simp only [isa, push, reduceCtorEq] at hp

/-- Calling verified code that may have frames: as `WP.callCalls`, but the
callee may also change the `stackUse c` bytes below the stack pointer. -/
theorem WP.callF {name : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) (hsu : stackUse c ≤ s.sp.toNat)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [belowA s.sp (stackUse c)]) s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call name c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  have hf := Exec.frameSp he (by simpa using hsu)
  obtain ⟨hr, hwr, -⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.withRegions_sp, State.callEntry_mem, State.callEntry_sp] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  have hret : isa.ret s.callEntry (s₁.withRegions s.rd s.wr) = some (s₁.withRegions s.rd s.wr) := by
    have h := habi.1 .lr (by decide)
    simp only [State.withRegions_gpr] at h
    simp only [isa, ret, State.withRegions_gpr, h, ite_true]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl ?_ hf (fun r hr' hlr => ?_) ?_⟩
  · simp only [State.withRegions_sp]; exact habi.2
  · simp only [State.withRegions_gpr]
    rw [habi.1 r hr', State.withRegions_gpr, State.callEntry_gpr s (preserved_not_link r hr' hlr)]
  · have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
    rw [this]; exact hpost

end VG.Arm
