import VerifiedGarbage.Proof.Hmac.Generic.Arm.Init
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Hashes
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any streaming hash function on 32-bit ARM: `init`, constant time

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Hmac/Generic/AArch64/Instances.lean`). The prologue loads `scratch`
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
  ([.mov .r0 (.reg st)] : List Instr) ++ scrAt .r1 o ++ ([.movw .r7 (BitVec.ofNat 16 H.B), .mov .r10 (.reg .r11),
    .movw .r2 (BitVec.ofNat 16 0), .mov .r3 (.imm 0)] : List Instr)

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
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega_nat]; exact hq.a0)
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

/-!
# HMAC over any streaming hash function on 32-bit ARM: `finalize`, constant time

Untrusted: everything here is checked by Lean. As for `init` (above).
-/

namespace VG.Proof.Hmac.Generic.Arm.Finalize

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy scrAt)
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Hmac.Generic.Arm.Init (args)

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.r4, .r5, .r6, .r11]

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Hash) : List Instr :=
  ([.mov .r0 (.reg .r4)] : List Instr) ++ [] ++ scrAt .r1 H.buf ++ ([.mov .r12 (.reg .r11)] : List Instr)

/-- The block that sets up the second call of `finalize`. -/
abbrev fin2Block (H : Hash) : List Instr :=
  ([.mov .r0 (.reg .r4)] : List Instr) ++ ([.movw .r2 (BitVec.ofNat 16 (H.B + H.D)), .mov .r3 (.imm 0)] : List Instr) ++
    scrAt .r1 H.buf ++ ([.mov .r12 (.reg .r11)] : List Instr)

/-- The block that sets up the call of `update`. -/
abbrev updBlock (H : Hash) : List Instr :=
  ([.mov .r0 (.reg .r4)] : List Instr) ++ scrAt .r1 H.buf ++ ([.movw .r7 (BitVec.ofNat 16 H.D), .mov .r10 (.reg .r11),
    .movw .r2 (BitVec.ofNat 16 H.B), .mov .r3 (.imm 0)] : List Instr)

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint args 8) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (fin1Block H)) hc).isSome = true
  copy1 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (copy .r5 0 .r4 0 H.S) hc).isSome = true
  upd : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H)) hc).isSome = true
  fin2 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (fin2Block H)) hc).isSome = true
  copy2 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (copy .r11 H.buf .r6 0 H.D) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The checks of the parts of `finalize` that do not depend on the size of
the digest carry over to a hash function of the same sizes but that one. -/
theorem Checks.of_sizes {H H' : Hash} (hB : H.B = H'.B) (hS : H.S = H'.S) (hW : H.W = H'.W) (h : Checks H)
    (upd : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H')) hc).isSome = true)
    (fin2 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (fin2Block H')) hc).isSome = true)
    (copy2 : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (copy .r11 H'.buf .r6 0 H'.D) hc).isSome = true) :
    Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hW; subst hB hS hW
  exact ⟨h.pro, h.fin1, h.copy1, upd, fin2, copy2, h.restore⟩

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, inn, inn, hq.r0]
  · rw [h.r5, h'.r5, outer, outer, hq.r1]
  · rw [h.r6, h'.r6, op, op, hq.a0]
  · rw [h.r11, h'.r11, scr, scr, hq.a1]

/-- The stack arguments lie outside the writable regions. -/
theorem args_wf {t : State} (h : Pre (H := H) sc t) :
    t.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 8⟩ r := by
  have e : (⟨State.addr t.sp, 8⟩ : Region) = argR t := by simp [stackArgAddr]
  refine ⟨h.spf, ?_⟩
  simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact h.a_i
  · exact h.a_p
  · exact h.a_s

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ tO (H := H) s₀' = tO (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.r0.symm, by rw [tO, tO, scr, scr, hq.a1], hq.a1.symm⟩

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {c : Prog isa} (hck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) t₀ s → WP isa c s (KR (H := H) t₀)) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') c
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
  rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ pubRegs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) ∧ count t = c)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (tO (H := H) s₀') (scr s₀') ∧ count t = c) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.frame (.push fin2) (.call H.finN H.finC) (.pop .r1 8)))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) ∧
      count t = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) ∧ count t = c)
    pubRegs hag hck (fun s h => hb s h)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, x1⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
  refine ha.seq (rel_wp (fin_rel hH (sp := s₀.sp) (st := inn s₀) (o := tO (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], k.sp, by rw [k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.finalize fun _ _ => True := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have hcnt : count s₀ = count s₀' := by rw [count, count, hq.r2, hq.r3]
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue)
      fun s s' => (KR (H := H) s₀ s ∧ count s = count s₀) ∧ (KR (H := H) s₀' s' ∧ count s' = count s₀') :=
    rel_agree (argTaint args 8) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (args_wf hp) (args_wf hp')
          (argMem_of (j := 2) hq.sp hp.spf fun i hi => by
            rcases (show i = 0 ∨ i = 1 by omega_nat) with rfl | rfl
            · exact hq.a0
            · exact hq.a1)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, _, x, _⟩ => ⟨k, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, _, x, _⟩ => ⟨k, x⟩)
  have fin1 := fin_rel' hH hp hp' hq (c := count s₀)
    (F := fun s => KR (H := H) s₀ s ∧ count s = count s₀)
    (F' := fun s => KR (H := H) s₀' s ∧ count s = count s₀') hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, x⟩ => WP.mono (fin1Args_ok hH hp k) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1.trans x⟩)
    (fun s ⟨k, x⟩ => WP.mono (fin1Args_ok hH hp' k) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1.trans (x.trans hcnt.symm)⟩)
  have fin2 := fin_rel' hH hp hp' hq (c := BitVec.ofNat 64 (H.B + H.D)) (F := KR (H := H) s₀)
    (F' := KR (H := H) s₀') hc.fin2
    (fun _ _ h h' => kr_agree hq h h')
    (fun s k => WP.mono (fin2Args_ok hH hp k) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s k => WP.mono (fin2Args_ok hH hp' k) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
  have upd : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s')
      (H.callUpd [.mov .r0 (.reg .r4)] H.B H.buf H.D) fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
    have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧
        UpdArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) H.D ∧ count t = BitVec.ofNat 64 H.B)
      (G' := fun t => KR (H := H) s₀' t ∧
        UpdArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) H.D ∧ count t = BitVec.ofNat 64 H.B)
      pubRegs (fun _ _ h h' => kr_agree hq h h') hc.upd
      (fun s h => WP.mono (updArgs_ok hH hp h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
      (fun s h => WP.mono (updArgs_ok hH hp' h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
    exact ha.seq (rel_wp (upd_rel hH (sp := s₀.sp) (st := inn s₀) (d := tO (H := H) s₀) (sc := scr s₀)
      (len := H.D)
      fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], k.sp, by rw [k'.sp, hq.sp]⟩)
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))
  have c1 := kr_rel hp hp' hq hc.copy1 fun hp s k => WP.mono (copy1_ok hp k) fun _ h => h.1
  have c2 := kr_rel hp hp' hq hc.copy2 fun hp s k => WP.mono (copy2_ok hp k) fun _ h => h.1
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h =>
      Taint.agree_ofRegs (kr_agree hq h.1 h.2)) hr
  exact pro.seq (fin1.seq (c1.seq (upd.seq (fin2.seq (c2.seq restore)))))

end VG.Proof.Hmac.Generic.Arm.Finalize

namespace VG.Proof.Hmac.Generic.Arm.Finalize

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)

/-- `finalize` is verified against `finG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.F ≤ 8 * sc) (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified Arm.target H.finalize (finG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6, h7⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.Arm.Finalize

/-!
# HMAC over the streaming hash functions on 32-bit ARM: the instances

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Hmac/Generic/AArch64/Instances.lean`): the generic proofs at each hash
function of `Hashes.lean`, moved to the shared contracts of
`Spec/Hmac/Generic.lean` (`sig_implies`), which the artifacts are emitted with.
-/

namespace VG.Proof.Hmac.Generic.Arm.Instances

open VG.Arm
open VG.Proof.Hmac.Generic.Arm

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key); `scratch`, at `0x4000`,
is the stack argument. -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x3000, 1⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x1000, S⟩, ⟨0x2000, S⟩, ⟨0x4000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space; `out`, at `0x3000`,
and `scratch`, at `0x4000`, are the stack arguments. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x30 else if a = 0x6005 then 0x40 else 0
  rd := [⟨0x2000, S⟩, ⟨0x6000, 8⟩]
  wr := [⟨0x1000, S⟩, ⟨0x3000, D⟩, ⟨0x4000, 8 * sc⟩]

/-- `finG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem finImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.finalizeContract S W Arm.abi 16).pre s) :
    (finG S W).Implies (Spec.Hmac.finalizeContract S W Arm.abi 16) := by
  generic_implies [
    Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, finG, below, count, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using h

/-! ## SHA-1 -/

theorem sha1_initChecks : Init.Checks sha1H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha1_finChecks : Finalize.Checks sha1H where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha1_finImp : (finG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha1S 56 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, finG, below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 84 20 56)

theorem sha1_finalize : Verified Arm.target sha1H.finalize (Spec.Hmac.sha1I.finalizeContract Arm.abi 16) :=
  (Finalize.verified sha1OK sha1_finChecks (by decide) sha1_finImp.sat_left).of_implies sha1_finImp

/-! ## MD5 -/

theorem md5_initChecks : Init.Checks md5H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem md5_finChecks : Finalize.Checks md5H where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem md5_finImp : (finG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.md5S 48 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.md5S, Spec.Hmac.md5, finG, below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 80 16 48)

theorem md5_finalize : Verified Arm.target md5H.finalize (Spec.Hmac.md5I.finalizeContract Arm.abi 16) :=
  (Finalize.verified md5OK md5_finChecks (by decide) md5_finImp.sat_left).of_implies md5_finImp

/-- `Init.Checks` looks at the sizes of a hash function but its digest's. -/
theorem Init.Checks.of_eq {H H' : Impl.Hmac.Generic.Arm.Hash} (hB : H.B = H'.B) (hS : H.S = H'.S)
    (hW : H.W = H'.W) (h : Init.Checks H) : Init.Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hW; subst hB hS hW
  exact ⟨h.keys, h.argI, h.argU₁, h.argU₂, h.restore⟩

/-! ## SHA-384 -/

theorem sha384_initChecks : Init.Checks sha384H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha384_finChecks : Finalize.Checks sha384H where
  pro := ⟨_, by taint_decide⟩
  fin1 := ⟨_, by taint_decide⟩
  copy1 := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin2 := ⟨_, by taint_decide⟩
  copy2 := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha384_finImp : (finG Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha384S 234 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, finG, below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 192 48 234)

theorem sha384_finalize : Verified Arm.target sha384H.finalize (Spec.Hmac.sha384I.finalizeContract Arm.abi 16) :=
  (Finalize.verified sha384OK sha384_finChecks (by decide) sha384_finImp.sat_left).of_implies sha384_finImp

/-! ## SHA-512 -/

theorem sha512_initChecks : Init.Checks sha512H' :=
  Init.Checks.of_eq (H := sha384H) rfl rfl rfl sha384_initChecks

theorem sha512_finChecks : Finalize.Checks sha512H' :=
  Finalize.Checks.of_sizes (H := sha384H) rfl rfl rfl sha384_finChecks ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩

theorem sha512_finImp : (finG Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha512S 234 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, finG, below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 192 64 234)

theorem sha512_finalize : Verified Arm.target sha512H'.finalize (Spec.Hmac.sha512I.finalizeContract Arm.abi 16) :=
  (Finalize.verified sha512OK sha512_finChecks (by decide) sha512_finImp.sat_left).of_implies sha512_finImp

/-! ## SHA-512/224 -/

theorem sha512_224_initChecks : Init.Checks sha512_224H :=
  Init.Checks.of_eq (H := sha384H) rfl rfl rfl sha384_initChecks

theorem sha512_224_finChecks : Finalize.Checks sha512_224H :=
  Finalize.Checks.of_sizes (H := sha384H) rfl rfl rfl sha384_finChecks ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩

theorem sha512_224_finImp : (finG Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha512_224S 234 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, finG, below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 192 28 234)

theorem sha512_224_finalize : Verified Arm.target sha512_224H.finalize (Spec.Hmac.sha512_224I.finalizeContract Arm.abi 16) :=
  (Finalize.verified sha512_224OK sha512_224_finChecks (by decide) sha512_224_finImp.sat_left).of_implies sha512_224_finImp

/-! ## SHA-512/256 -/

theorem sha512_256_initChecks : Init.Checks sha512_256H :=
  Init.Checks.of_eq (H := sha384H) rfl rfl rfl sha384_initChecks

theorem sha512_256_finChecks : Finalize.Checks sha512_256H :=
  Finalize.Checks.of_sizes (H := sha384H) rfl rfl rfl sha384_finChecks ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩

theorem sha512_256_finImp : (finG Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha512_256S 234 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, finG, below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 192 32 234)

theorem sha512_256_finalize : Verified Arm.target sha512_256H.finalize (Spec.Hmac.sha512_256I.finalizeContract Arm.abi 16) :=
  (Finalize.verified sha512_256OK sha512_256_finChecks (by decide) sha512_256_finImp.sat_left).of_implies sha512_256_finImp

end VG.Proof.Hmac.Generic.Arm.Instances
