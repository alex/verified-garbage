import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Calls of functions with frames (ARMv7)

Untrusted: everything here is checked by Lean.

`WP.call` and `WP.callCalls` run a call of code without frames, which
changes memory only within the regions it may write. Code with frames (the
callee pushes its own callees' stack arguments) also changes the stack below
the stack pointer: at most `armStack c` bytes of it (`Exec.frameSp`), which
`WP.callF` lets the call change, as on AArch64 and x86
(`Proof/Framework/AArch64/Call.lean`, `Proof/Framework/X86/Call.lean`).
-/

namespace VG.Arm.FrameStack

/-- The bytes below the stack pointer that the frames of `c`, and of the
functions it calls, use (a call keeps its return address in `lr`). -/
def armStack : Prog isa → Nat
  | .block _ => 0
  | .seq a b => max (armStack a) (armStack b)
  | .ite _ t e => max (armStack t) (armStack e)
  | .loop b _ => armStack b
  | .call _ b => armStack b
  | .frame (.push rs) b _ => armStack b + 4 * rs.length
  | .frame (.alloc n) b _ => armStack b + n
  | .frame _ b _ => armStack b

/-- The `n` bytes below `sp`. -/
abbrev belowA (sp : BitVec 32) (n : Nat) : Region := ⟨State.addr (sp - BitVec.ofNat 32 n), n⟩

/-- `x - k` (for `k ≤ x`) widened to 64 bits. -/
theorem addr_sub' {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) :
    State.addr (x - BitVec.ofNat 32 k) = State.addr x - BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    show 2 ^ 32 - k + x.toNat = 2 ^ 32 + (x.toNat - k) by omega, Nat.add_mod_left,
    show 2 ^ 64 - k + x.toNat = 2 ^ 64 + (x.toNat - k) by omega, Nat.add_mod_left]
  omega

theorem sub_toNat' {sp : BitVec 32} {k : Nat} (h : k ≤ sp.toNat) :
    (sp - BitVec.ofNat 32 k).toNat = sp.toNat - k := by
  have := sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  rw [show 2 ^ 32 - k + sp.toNat = (sp.toNat - k) + 2 ^ 32 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- The `a` bytes below `sp - k` are among the `b` bytes below `sp`. -/
theorem belowA_inner {sp : BitVec 32} {a b k : Nat} (h : a + k ≤ b) (hb : b ≤ sp.toNat) :
    Region.Sub (belowA (sp - BitVec.ofNat 32 k) a) (belowA sp b) := by
  have hk : a ≤ (sp - BitVec.ofNat 32 k).toNat := by rw [sub_toNat' (by omega)]; omega
  show Region.Sub ⟨State.addr (sp - BitVec.ofNat 32 k - BitVec.ofNat 32 a), a⟩
    ⟨State.addr (sp - BitVec.ofNat 32 b), b⟩
  rw [addr_sub' hk, addr_sub' hb, addr_sub' (k := k) (by omega), BitVec.sub_sub, ← BitVec.ofNat_add]
  exact fun x hx => Offset.below_mono _ (a := k + a) (by omega) (by omega) x
    (Region.sub_prefix (by omega) x hx)

theorem belowA_sub {sp : BitVec 32} {a b : Nat} (h : a ≤ b) (hb : b ≤ sp.toNat) :
    Region.Sub (belowA sp a) (belowA sp b) := by
  have := belowA_inner (sp := sp) (a := a) (k := 0) (by omega) hb
  simpa using this

theorem Frame.belowA_mono {wr : List Region} {sp : BitVec 32} {a b : Nat} {m m' : Mem}
    (h : Frame (wr ++ [belowA sp a]) m m') (hab : a ≤ b) (hb : b ≤ sp.toNat) :
    Frame (wr ++ [belowA sp b]) m m' :=
  Frame.sub h fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub hab hb⟩

/-- Storing words changes memory only where they are stored. -/
theorem storeWords_frame : ∀ (vs : List (BitVec 32)) (m : Mem) (a : BitVec 32),
    a.toNat + 4 * vs.length ≤ 2 ^ 32 → Frame [⟨State.addr a, 4 * vs.length⟩] m (storeWords m a vs)
  | [], m, _, _ => Frame.refl _ _
  | [v], m, a, _ => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, List.length_cons, List.length_nil]; omega)
  | v :: w :: vs, m, a, h => by
    simp only [List.length_cons] at h
    have h4 : a.toNat + 4 < 2 ^ 32 := by omega
    have ih := storeWords_frame (w :: vs) (m.writeW (State.addr a) v) (a + 4) (by
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := 4) (by omega), Nat.mod_eq_of_lt h4]; simp only [List.length_cons]; omega)
    have e : State.addr (a + 4) = State.addr a + BitVec.ofNat 64 4 := addr_add (k := 4) h4
    rw [e] at ih
    refine Frame.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_) (Frame.sub ih fun r hr => ?_)
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, List.length_cons]; omega
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by simp only [List.length_cons]; omega)⟩

/-- A frame's push changes memory only in the frame. -/
theorem pushed_frameA {rs : List Reg} {s : State} (hn : 4 * rs.length ≤ s.sp.toNat) :
    Frame [belowA s.sp (4 * rs.length)] s.mem (pushed rs s).mem := by
  have := storeWords_frame (rs.map s.gpr) s.mem (s.sp - BitVec.ofNat 32 (4 * rs.length)) (by
    rw [List.length_map, sub_toNat' hn]; have := s.sp.isLt; omega)
  rwa [List.length_map] at this

theorem pop_memA {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') : s'.mem = s₂.mem := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  all_goals split at h <;> cases h
  all_goals rfl

/-- Code changes memory only within the regions it may write, and within the
`armStack` bytes below the stack pointer (its frames). -/
theorem Exec.frameSp {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hd : armStack c ≤ s.sp.toNat) :
    Frame (s.wr ++ [belowA s.sp (armStack c)]) s.mem s'.mem := by
  induction h with
  | block h => exact Frame.mono (execBlock_regions h).2.2.2 fun r hr => List.mem_append_left _ hr
  | @seq c₁ c₂ _ s₂ _ _ _ h₁ _ ih₁ ih₂ =>
    simp only [armStack] at hd ⊢
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    have f₁ := Frame.belowA_mono (ih₁ (by omega)) (b := max (armStack c₁) (armStack c₂)) (by omega) hd
    have f₂ := Frame.belowA_mono (ih₂ (by rw [p₁]; omega)) (b := max (armStack c₁) (armStack c₂))
      (by omega) (by rw [p₁]; exact hd)
    rw [w₁, p₁] at f₂
    exact Frame.trans f₁ f₂
  | iteT _ _ ih =>
    simp only [armStack] at hd ⊢
    exact Frame.belowA_mono (ih (by omega)) (by omega) hd
  | iteF _ _ ih =>
    simp only [armStack] at hd ⊢
    exact Frame.belowA_mono (ih (by omega)) (by omega) hd
  | loopExit _ _ ih => exact ih hd
  | loopNext h₁ _ _ ih₁ ih₂ =>
    obtain ⟨-, w₁, p₁⟩ := Exec.rdwr h₁
    have f₂ := ih₂ (by rw [p₁]; exact hd)
    rw [w₁, p₁] at f₂
    exact Frame.trans (ih₁ hd) f₂
  | call hc _ hr ih =>
    simp only [armStack] at hd ⊢
    obtain ⟨-, w₁, p₁, m₁, -⟩ := call_eq hc
    rw [ret_eq hr]
    have := ih (by rw [p₁]; exact hd)
    rwa [w₁, p₁, m₁] at this
  | @frame i _ b s₀ s₁ s₂ _ _ hp _ hq ih =>
    rw [pop_memA hq]
    cases i <;> simp only [isa, push, reduceCtorEq] at hp
    case push rs =>
      split at hp <;> [rename_i hc; cases hp]
      cases hp
      simp only [armStack] at hd ⊢
      have hn := hc.2
      have f₁ := ih (by show armStack b ≤ (s₀.sp - BitVec.ofNat 32 (4 * rs.length)).toNat
                        rw [sub_toNat' hn]; omega)
      simp only at f₁
      refine Frame.trans (Frame.sub (pushed_frameA (rs := rs) (s := s₀) hn) fun r hr => ?_)
        (Frame.sub f₁ fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_sub (by omega) hd⟩
      · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | hr | rfl
        · refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
          exact belowA_sub (sp := s₀.sp) (a := 4 * rs.length) (by omega) hd
        · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_inner (by omega) hd⟩
    case alloc bytes =>
      split at hp <;> [rename_i hc; cases hp]
      cases hp
      simp only [armStack] at hd ⊢
      have hn := hc.2.2.2
      have f₁ := ih (by show armStack b ≤ (s₀.sp - BitVec.ofNat 32 bytes).toNat
                        rw [sub_toNat' hn]; omega)
      simp only at f₁
      refine Frame.sub f₁ fun r hr => ?_
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | hr | rfl
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          belowA_sub (sp := s₀.sp) (a := bytes) (by omega) hd⟩
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), belowA_inner (by omega) hd⟩

/-- Calling verified code that may have frames: as `WP.callCalls`, but the
callee may also change the `armStack` bytes below the stack pointer. -/
theorem WP.callF {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) (hd : armStack c ≤ s.sp.toNat)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame (wr ++ [belowA s.sp (armStack c)]) s.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, habi, hpost⟩ := hv _ hpre
  have hf := Exec.frameSp he (by simpa using hd)
  obtain ⟨hr, hwr, -⟩ := Exec.rdwr he
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.withRegions_sp,
    State.callEntry_mem, State.callEntry_sp] at hr hwr hf
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

end VG.Arm.FrameStack
