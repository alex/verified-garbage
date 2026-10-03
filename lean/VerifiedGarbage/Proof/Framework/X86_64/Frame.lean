import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# Frames (x86-64)

A frame's push stores its registers below `rsp` (`pushed`) and makes those
bytes a writable region; its pop reloads one register and removes the
region (`popped`). `WP.frame` runs a frame whose body leaves `rsp` and the
writable regions as the push left them, and `RelCT.frame` relates two runs of
one.
-/

namespace VG.X86_64

/-- The state after a frame's push of `rs`. -/
def pushed (rs : List Reg) (s : State) : State :=
  { pushRegs s rs with wr := ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length), 8 * rs.length⟩ :: s.wr }

/-- The state after a frame's `pop r` (`k` times), from the state `s` its
body ends in. -/
def popped (r : Reg) (k : Nat) (s : State) : State := { popReg s r k with wr := s.wr.tail }

theorem push_pushed {rs : List Reg} {s : State} (hne : rs ≠ []) (hrs : .rsp ∉ rs)
    (hn : 8 * rs.length ≤ (s.gpr .rsp).toNat) : isa.push (.push rs) s = some (pushed rs s) := by
  simp only [isa, push, ne_eq, hne, not_false_eq_true, hrs, hn, and_self, ite_true]
  rfl

theorem push_some {rs : List Reg} {s s₁ : State} (h : isa.push (.push rs) s = some s₁) :
    s₁ = pushed rs s := by
  simp only [isa, push] at h
  split at h <;> [skip; cases h]
  cases h
  rfl

@[simp] theorem pushed_rd (rs : List Reg) (s : State) : (pushed rs s).rd = s.rd :=
  (pushRegs_eq s rs).1
@[simp] theorem pushed_wr (rs : List Reg) (s : State) :
    (pushed rs s).wr = ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length), 8 * rs.length⟩ :: s.wr := rfl
theorem pushed_rsp (rs : List Reg) (s : State) :
    (pushed rs s).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length) := (pushRegs_eq s rs).2.2.1
theorem pushed_gpr (rs : List Reg) (s : State) {r : Reg} (h : r ≠ .rsp) :
    (pushed rs s).gpr r = s.gpr r := (pushRegs_eq s rs).2.2.2 r h

@[simp] theorem pushed_mxcsr (rs : List Reg) (s : State) : (pushed rs s).mxcsr = s.mxcsr :=
  pushRegs_mxcsr s rs

theorem popReg_mem (s : State) (d : Reg) (k : Nat) : (popReg s d k).mem = s.mem := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

@[simp] theorem popped_rd (r : Reg) (k : Nat) (s : State) : (popped r k s).rd = s.rd :=
  (popReg_eq s r k).1
@[simp] theorem popped_wr (r : Reg) (k : Nat) (s : State) : (popped r k s).wr = s.wr.tail := rfl
@[simp] theorem popped_mem (r : Reg) (k : Nat) (s : State) : (popped r k s).mem = s.mem :=
  popReg_mem s r k
@[simp] theorem popped_mxcsr (r : Reg) (k : Nat) (s : State) : (popped r k s).mxcsr = s.mxcsr :=
  popReg_mxcsr s r k
theorem popped_rsp (r : Reg) (k : Nat) (s : State) :
    (popped r k s).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 (8 * k) := (popReg_eq s r k).2.2.1
theorem popped_gpr (r : Reg) (k : Nat) (s : State) {r' : Reg} (h : r' ≠ .rsp) (h' : r' ≠ r) :
    (popped r k s).gpr r' = s.gpr r' := (popReg_eq s r k).2.2.2 r' h h'

theorem toNat_sub_ofNat {a : Addr} {k : Nat} (h : k ≤ a.toNat) :
    (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have := a.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    show 2 ^ 64 - k + a.toNat = (a.toNat - k) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- `push r` for each of `rs` stores `rs[j]` at `rsp - 8 (j + 1)`, and nothing
outside the `8 * rs.length` bytes below `rsp`. -/
theorem pushRegs_mem (s : State) (rs : List Reg) (hrs : .rsp ∉ rs)
    (hn : 8 * rs.length ≤ (s.gpr .rsp).toNat) :
    Frame [⟨s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length), 8 * rs.length⟩] s.mem (pushRegs s rs).mem ∧
      ∀ j (hj : j < rs.length),
        (pushRegs s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr rs[j] := by
  induction rs generalizing s with
  | nil => exact ⟨Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | cons x xs ih =>
    simp only [List.mem_cons, not_or] at hrs
    simp only [List.length_cons] at hn ⊢
    let s₁ : State := { s.setReg .rsp (s.gpr .rsp - 8) with
      mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) }
    have hs₁ : s₁ = { s.setReg .rsp (s.gpr .rsp - 8) with
      mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) } := rfl
    have hsp₁ : s₁.gpr .rsp = s.gpr .rsp - 8 := by simp [hs₁, State.setReg]
    have hg₁ : ∀ r, r ≠ .rsp → s₁.gpr r = s.gpr r := fun r h => by simp [hs₁, State.setReg, h]
    have hm₁ : s₁.mem = s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) := rfl
    have e₁ : (s₁.gpr .rsp).toNat = (s.gpr .rsp).toNat - 8 := by
      rw [hsp₁]; have := (s.gpr .rsp).isLt; bv_omega
    obtain ⟨ih₁, ih₂⟩ := ih s₁ hrs.2 (by omega)
    have hp : pushRegs s (x :: xs) = pushRegs s₁ xs := rfl
    generalize hS : s.gpr .rsp = S at *
    generalize hT : s₁.gpr .rsp = T at *
    subst hsp₁
    clear ih
    refine ⟨fun y hy => ?_, fun j hj => ?_⟩
    · have hy' := hy _ (List.mem_singleton_self _)
      simp only [Region.Contains] at hy'
      rw [hp, ih₁ y (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains]; bv_omega), hm₁]
      apply Mem.write_apply
      bv_omega
    · rw [hp]
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [show S - BitVec.ofNat 64 (8 * (0 + 1)) = S - 8 from rfl,
          ← Mem.readW_writeW_self64 s.mem (S - 8) (s.gpr x), ← hm₁]
        refine Mem.readW_congr fun t ht => ih₁ _ fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains]
        simp only [Nat.reduceDiv] at ht
        bv_omega
      | succ j =>
        simp only [List.getElem_cons_succ]
        have := ih₂ j (by omega)
        rw [hg₁ _ (fun h => hrs.2 (h ▸ List.getElem_mem _))] at this
        rw [← this]
        congr 1
        bv_omega

/-- A frame: its body runs from `pushed rs s`, ends with `rsp` and the
writable regions as the push left them, and the pop of the `rs.length`
words leads to `popped r rs.length s₂`. -/
theorem WP.frame {rs : List Reg} {r : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hne : rs ≠ []) (hrs : .rsp ∉ rs) (hr : r ≠ .rsp) (hn : 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (pushed rs s) fun s₂ => s₂.gpr .rsp = (pushed rs s).gpr .rsp ∧
      s₂.wr = (pushed rs s).wr ∧ Q (popped r rs.length s₂)) :
    WP isa (.frame (.push rs) body (.pop r rs.length)) s Q := by
  obtain ⟨t, s₂, he, hsp, hw, hq⟩ := hb
  have hpop : isa.pop (.pop r rs.length) (pushed rs s) s₂ = some (popped r rs.length s₂) := by
    simp only [isa, pop]
    refine ite_eq_left ⟨by simpa using hne, hr, hsp, hw, ?_⟩
    rw [pushed_wr, pushed_rsp]; rfl
  exact ⟨_, _, Exec.frame (push_pushed hne hrs hn) he hpop, hq⟩

/-- Two runs of a frame leak the same trace when `rsp` agrees and the runs of
its body, from the states after the push, do. -/
theorem RelCT.frame {rs : List Reg} {r : Reg} {k : Nat} {body : Prog isa}
    {P R : State → State → Prop} (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed rs s₁ ∧ b = pushed rs s₂) body R) :
    RelCT isa P (.frame (.push rs) body (.pop r k)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := push_some p₁
      obtain rfl := push_some p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      have g₁ := (pop_eq q₁).2.2.2.2.1
      have g₂ := (pop_eq q₂).2.2.2.2.1
      rw [pushed_rsp] at g₁ g₂
      have e := hsp _ _ hp
      refine ⟨?_, trivial⟩
      simp only [addrs, g₁, g₂, e]

end VG.X86_64
