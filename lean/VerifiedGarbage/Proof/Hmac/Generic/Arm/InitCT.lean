import VerifiedGarbage.Proof.Hmac.Generic.Arm.Init

/-!
# HMAC over any streaming hash function on 32-bit ARM: `init`, constant time

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Hmac/Generic/AArch64/InitCT.lean`). The prologue loads `scratch`
from the stack, so its taint check starts with the stack argument public
(`argTaint`).
-/

namespace VG.Proof.Hmac.Generic.Arm.Init

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash scrAt)
open VG.Proof.Hmac.Generic.Arm

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.r4, .r5, .r11]

/-- The argument registers. -/
abbrev args : List Reg := [.r0, .r1, .r2, .r3]

/-- The block that sets up a call of `update` from `st`, at offset `o`. -/
abbrev updBlock (H : Hash) (st : Reg) (o : Nat) : List Instr :=
  [.mov .r0 (.reg st)] ++ scrAt .r1 o ++ [.movw .r7 (BitVec.ofNat 16 H.B), .mov .r10 (.reg .r11),
    .movw .r2 (BitVec.ofNat 16 0), .mov .r3 (.imm 0)]

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  keys : ∃ hc, (VG.Taint.check taint (argTaint args 4) H.initKeys hc).isSome = true
  argI : ∀ st ∈ [Reg.r4, .r5], ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block [.mov .r0 (.reg st)]) hc).isSome = true
  argU₁ : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H .r4 H.buf)) hc).isSome = true
  argU₂ : ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H .r5 (H.buf + H.B))) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r4, h'.r4, inn, inn, hq.r0]
  · rw [h.r5, h'.r5, out, out, hq.r1]
  · rw [h.r11, h'.r11, scr, scr, hq.a0]

/-- The stack argument lies outside the writable regions. -/
theorem args_wf {t : State} (h : Pre (H := H) sc t) :
    t.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4⟩ r := by
  have e : (⟨State.addr t.sp, 4⟩ : Region) = argR t := by simp [stackArgAddr]
  refine ⟨h.spf, ?_⟩
  simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact h.a_i
  · exact h.a_o
  · exact h.a_s

include hH hc hp hp' hq

/-- A call of `init` on the state in `st` (`r4` for `inner`, `r5` for `outer`). -/
theorem callInit_rel {st : Reg} (hst : st = .r4 ∨ st = .r5) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (H.callInit st)
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  -- The state's address, the same in both runs.
  let p : BitVec 32 := if st = .r4 then inn s₀ else out s₀
  have hpR : p = inn s₀ ∨ p = out s₀ := by by_cases h : st = .r4 <;> simp [p, h]
  have hpR' : p = inn s₀' ∨ p = out s₀' := by
    show p = s₀'.gpr .r0 ∨ p = s₀'.gpr .r1; rw [← hq.r0, ← hq.r1]; exact hpR
  have hs : ∀ {t : State}, KR (H := H) s₀ t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.r4]
    · simp [p, h.r5]
  have hs' : ∀ {t : State}, KR (H := H) s₀' t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.r4, hq.r0]
    · simp [p, h.r5, hq.r1]
  obtain ⟨_, _, np⟩ := state_disj hp hpR
  have ha : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block [.mov .r0 (.reg st)])
      fun s s' => (KR (H := H) s₀ s ∧ s.gpr .r0 = p ∧ True) ∧ (KR (H := H) s₀' s' ∧ s'.gpr .r0 = p ∧ True) :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.argI st (by rcases hst with rfl | rfl <;> simp))
      (fun _ h => WP.mono (initArgs_ok h (hs h)) fun _ ⟨k, d, _⟩ => ⟨k, d, trivial⟩)
      (fun _ h => WP.mono (initArgs_ok h (hs' h)) fun _ ⟨k, d, _⟩ => ⟨k, d, trivial⟩)
  refine ha.seq (rel_wp (F := fun s => KR (H := H) s₀ s ∧ s.gpr .r0 = p ∧ True)
    (F' := fun s => KR (H := H) s₀' s ∧ s.gpr .r0 = p ∧ True)
    (init_rel hH (st := p) fun s s' h => ?_)
    (fun _ ⟨k, d, _⟩ => initCall_ok hH hp k d hpR fun _ k' _ _ => k')
    (fun _ ⟨k, d, _⟩ => initCall_ok hH hp' k d hpR' fun _ k' _ _ => k'))
  obtain ⟨⟨k, d, _⟩, ⟨k', d', _⟩⟩ := h
  exact ⟨d, d', np, by rw [k.wr]; exact covers_one (state_in hp hpR),
    by rw [k'.wr]; exact covers_one (state_in hp' hpR')⟩

omit hc in
/-- A call of `update` on the state in `st`, with the bytes at `scratch + o`. -/
theorem callUpd_rel {st : Reg} (hst : st = .r4 ∨ st = .r5) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    (hck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H st o)) hc).isSome = true) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (H.callUpd [.mov .r0 (.reg st)] 0 o H.B)
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  let p : BitVec 32 := if st = .r4 then inn s₀ else out s₀
  have hpR : p = inn s₀ ∨ p = out s₀ := by by_cases h : st = .r4 <;> simp [p, h]
  have hpR' : p = inn s₀' ∨ p = out s₀' := by
    show p = s₀'.gpr .r0 ∨ p = s₀'.gpr .r1; rw [← hq.r0, ← hq.r1]; exact hpR
  have hs : ∀ {t : State}, KR (H := H) s₀ t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.r4]
    · simp [p, h.r5]
  have hs' : ∀ {t : State}, KR (H := H) s₀' t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.r4, hq.r0]
    · simp [p, h.r5, hq.r1]
  have e8' : scr s₀' = scr s₀ := hq.a0.symm
  have e8 : dO s₀' o = dO s₀ o := by rw [dO, dO, e8']
  have ha : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block (updBlock H st o))
      fun s s' => (KR (H := H) s₀ s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ count s = BitVec.ofNat 64 0) ∧
        (KR (H := H) s₀' s' ∧ UpdArgs hH s' p (dO s₀ o) (scr s₀) H.B ∧ count s' = BitVec.ofNat 64 0) :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck
      (fun _ h => WP.mono (updArgs_ok hH hp h (hs h) hpR ho) fun _ ⟨k, a, c, _⟩ => ⟨k, a, c⟩)
      (fun _ h => WP.mono (updArgs_ok hH hp' h (hs' h) hpR' ho) fun _ ⟨k, a, c, _⟩ =>
        ⟨k, e8 ▸ e8' ▸ a, c⟩)
  refine ha.seq (rel_wp
    (F := fun s => KR (H := H) s₀ s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ count s = BitVec.ofNat 64 0)
    (F' := fun s => KR (H := H) s₀' s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ count s = BitVec.ofNat 64 0)
    (upd_rel hH (sp := s₀.sp) (st := p) (d := dO s₀ o) (sc := scr s₀) (len := H.B)
    fun s s' ⟨⟨k, a, c⟩, ⟨k', a', c'⟩⟩ => ⟨a, a', by rw [c, c'], k.sp, by rw [k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, c⟩ => updCall_ok hH hp k hpR a c fun _ k' _ _ => k')
    (fun _ ⟨k, a, c⟩ => updCall_ok hH hp' k hpR' (e8.symm ▸ e8'.symm ▸ a) c fun _ k' _ _ => k'))

theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.init fun _ _ => True := by
  have keys : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.initKeys
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
    rel_agree (argTaint args 4) (fun s s' e e' => by
        subst e e'
        refine agree_argTaint (fun r hr => ?_) hq.sp (args_wf hp) (args_wf hp')
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega]; exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.keys
      (fun _ e => by subst e; exact WP.mono (keys_ok sc hp) fun _ h => h.kr)
      (fun _ e => by subst e; exact WP.mono (keys_ok sc hp') fun _ h => h.kr)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h =>
      Taint.agree_ofRegs (kr_agree hq h.1 h.2)) hr
  exact keys.seq ((callInit_rel hH hc hp hp' hq (.inl rfl)).seq
    ((callUpd_rel hH hp hp' hq (.inl rfl) (.inl rfl) hc.argU₁).seq
    ((callInit_rel hH hc hp hp' hq (.inr rfl)).seq
    ((callUpd_rel hH hp hp' hq (.inr rfl) (.inr rfl) hc.argU₂).seq restore))))

end VG.Proof.Hmac.Generic.Arm.Init

namespace VG.Proof.Hmac.Generic.Arm.Init

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)

/-- `init` is verified against `initG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + 2 * H.B ≤ 8 * sc) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified Arm.target H.init (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH sc hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH hc (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.Arm.Init
