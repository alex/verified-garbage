import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Init
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.Implies

/-!
# HMAC over any streaming hash function on AArch64: `init`, constant time

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Hmac/Generic/X86_64/Instances.lean`): two runs are related (`RelCT`);
correctness determines the registers `KR` fixes from the public arguments,
so they agree between the calls, where the taint analysis checks each piece
of code (`Checks`, evaluated for each hash function, since the code depends
on its sizes); the calls are constant time by the callees' own proofs.
-/

namespace VG.Proof.Hmac.Generic.AArch64.Init

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.Hmac.Generic.Common (covers_one)

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x23]

/-- The argument registers. -/
abbrev args : List Reg := [.x0, .x1, .x2, .x3, .x4]

/-- The block that sets up a call of `update` from `st`, at offset `o`. -/
abbrev updBlock (H : Hash) (st : Reg) (o : Nat) : List Instr :=
  [mov .x0 st] ++ ([.movz .x .x1 (BitVec.ofNat 16 0) 0, .addImm .x .x2 .x23 o,
    .movz .x .x3 (BitVec.ofNat 16 H.B) 0, mov .x4 .x23] : List Instr)

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  keys : ∃ hc, (Taint.check taint (Taint.ofRegs args) H.initKeys hc).isSome = true
  argI : ∀ st ∈ [Reg.x19, .x20], ∃ hc,
    (Taint.check taint (Taint.ofRegs pubRegs) (.block [mov .x0 st]) hc).isSome = true
  argU₁ : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H .x19 H.buf)) hc).isSome = true
  argU₂ : ∃ hc,
    (Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H .x20 (H.buf + H.B))) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : s₀.gpr .x2 = s₀'.gpr .x2
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.x19, h'.x19, inn, inn, hq.x0]
  · rw [h.x20, h'.x20, out, out, hq.x1]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]

include hH hc hp hp' hq

/-- A call of `init` on the state in `st` (`x19` for `inner`, `x20` for `outer`). -/
theorem callInit_rel {st : Reg} (hst : st = .x19 ∨ st = .x20) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (H.callInit st)
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  -- The state's address, the same in both runs.
  let p : Addr := if st = .x19 then inn s₀ else out s₀
  have hpR : p = inn s₀ ∨ p = out s₀ := by by_cases h : st = .x19 <;> simp [p, h]
  have hpR' : p = inn s₀' ∨ p = out s₀' := by
    show p = s₀'.gpr .x0 ∨ p = s₀'.gpr .x1; rw [← hq.x0, ← hq.x1]; exact hpR
  have hs : ∀ {t : State}, KR (H := H) s₀ t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.x19]
    · simp [p, h.x20]
  have hs' : ∀ {t : State}, KR (H := H) s₀' t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.x19, hq.x0]
    · simp [p, h.x20, hq.x1]
  have ha : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block [mov .x0 st])
      fun s s' => (KR (H := H) s₀ s ∧ s.gpr .x0 = p ∧ True) ∧ (KR (H := H) s₀' s' ∧ s'.gpr .x0 = p ∧ True) :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.argI st (by rcases hst with rfl | rfl <;> simp))
      (fun _ h => WP.mono (initArgs_ok h (hs h)) fun _ ⟨k, d, _⟩ => ⟨k, d, trivial⟩)
      (fun _ h => WP.mono (initArgs_ok h (hs' h)) fun _ ⟨k, d, _⟩ => ⟨k, d, trivial⟩)
  refine ha.seq (rel_wp (F := fun s => KR (H := H) s₀ s ∧ s.gpr .x0 = p ∧ True)
    (F' := fun s => KR (H := H) s₀' s ∧ s.gpr .x0 = p ∧ True)
    (init_rel hH (st := p) fun s s' h => ?_)
    (fun _ ⟨k, d, _⟩ => initCall_ok hH hp k d hpR fun _ _ k' _ _ => k')
    (fun _ ⟨k, d, _⟩ => initCall_ok hH hp' k d hpR' fun _ _ k' _ _ => k'))
  obtain ⟨⟨k, d, _⟩, ⟨k', d', _⟩⟩ := h
  exact ⟨d, d', by rw [k.wr]; exact covers_one (state_in hp hpR),
    by rw [k'.wr]; exact covers_one (state_in hp' hpR'), by rw [k.sp, k'.sp, hq.sp]⟩

omit hc in
/-- A call of `update` on the state in `st`, with the bytes at `scratch + o`. -/
theorem callUpd_rel {st : Reg} (hst : st = .x19 ∨ st = .x20) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H st o)) hc).isSome = true) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (H.callUpd [mov .x0 st] 0 o H.B)
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  let p : Addr := if st = .x19 then inn s₀ else out s₀
  have hpR : p = inn s₀ ∨ p = out s₀ := by by_cases h : st = .x19 <;> simp [p, h]
  have hpR' : p = inn s₀' ∨ p = out s₀' := by
    show p = s₀'.gpr .x0 ∨ p = s₀'.gpr .x1; rw [← hq.x0, ← hq.x1]; exact hpR
  have hs : ∀ {t : State}, KR (H := H) s₀ t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.x19]
    · simp [p, h.x20]
  have hs' : ∀ {t : State}, KR (H := H) s₀' t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.x19, hq.x0]
    · simp [p, h.x20, hq.x1]
  have e8 : dO s₀' o = dO s₀ o := by rw [dO, dO, scr, scr, hq.x4]
  have e8' : scr s₀' = scr s₀ := hq.x4.symm
  have ha : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block (updBlock H st o))
      fun s s' => (KR (H := H) s₀ s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ s.gpr .x1 = 0) ∧
        (KR (H := H) s₀' s' ∧ UpdArgs hH s' p (dO s₀ o) (scr s₀) H.B ∧ s'.gpr .x1 = 0) :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck
      (fun _ h => WP.mono (updArgs_ok hH hp h (hs h) hpR ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
      (fun _ h => WP.mono (updArgs_ok hH hp' h (hs' h) hpR' ho) fun _ ⟨k, a, x1, _⟩ =>
        ⟨k, e8 ▸ e8' ▸ a, x1⟩)
  refine ha.seq (rel_wp (F := fun s => KR (H := H) s₀ s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ s.gpr .x1 = 0)
    (F' := fun s => KR (H := H) s₀' s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ s.gpr .x1 = 0)
    (upd_rel hH (st := p) (d := dO s₀ o) (sc := scr s₀) (len := H.B)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, x1⟩ => updCall_ok hH hp k hpR a x1 fun _ _ k' _ _ => k')
    (fun _ ⟨k, a, x1⟩ => updCall_ok hH hp' k hpR' (e8'.symm ▸ a) x1 fun _ _ k' _ _ => k'))

theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.init fun _ _ => True := by
  have keys : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.initKeys
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
    rel_taint args (fun s s' e e' => by
        subst e e'
        refine ⟨hq.sp, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) hc.keys
      (fun _ e => by subst e; exact WP.mono (keys_ok sc hp) fun _ h => h.kr)
      (fun _ e => by subst e; exact WP.mono (keys_ok sc hp') fun _ h => h.kr)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact keys.seq ((callInit_rel hH hc hp hp' hq (.inl rfl)).seq
    ((callUpd_rel hH hp hp' hq (.inl rfl) (.inl rfl) hc.argU₁).seq
    ((callInit_rel hH hc hp hp' hq (.inr rfl)).seq
    ((callUpd_rel hH hp hp' hq (.inr rfl) (.inr rfl) hc.argU₂).seq restore))))

end VG.Proof.Hmac.Generic.AArch64.Init

namespace VG.Proof.Hmac.Generic.AArch64.Init

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)

/-- `init` is verified against `initG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + 2 * H.B ≤ 8 * sc) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified AArch64.target H.init (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH sc hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH hc (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.AArch64.Init

/-!
# HMAC over any streaming hash function on AArch64: `finalize`, constant time

Untrusted: everything here is checked by Lean. As for `init` (above).
-/

namespace VG.Proof.Hmac.Generic.AArch64.Finalize

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash copy)
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.Hmac.Generic.AArch64.Init (PubEq args)

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x23]

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Hash) : List Instr :=
  [] ++ [mov .x1 .x2] ++ ([.addImm .x .x2 .x23 H.buf, mov .x3 .x23] : List Instr)

/-- The block that sets up the second call of `finalize`. -/
abbrev fin2Block (H : Hash) : List Instr :=
  [mov .x0 .x19] ++ ([.movz .x .x1 (BitVec.ofNat 16 (H.B + H.D)) 0] : List Instr) ++ ([.addImm .x .x2 .x23 H.buf, mov .x3 .x23] : List Instr)

/-- The block that sets up the call of `update`. -/
abbrev updBlock (H : Hash) : List Instr :=
  [mov .x0 .x19] ++ ([.movz .x .x1 (BitVec.ofNat 16 H.B) 0, .addImm .x .x2 .x23 H.buf,
    .movz .x .x3 (BitVec.ofNat 16 H.D) 0, mov .x4 .x23] : List Instr)

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin1Block H)) hc).isSome = true
  copy1 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (copy .x20 0 .x19 0 H.S) hc).isSome = true
  upd : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H)) hc).isSome = true
  fin2 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin2Block H)) hc).isSome = true
  copy2 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (copy .x23 H.buf .x21 0 H.D) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The checks of the parts of `finalize` that do not depend on the size of
the digest carry over to a hash function of the same sizes but that one. -/
theorem Checks.of_sizes {H H' : Hash} (hB : H.B = H'.B) (hS : H.S = H'.S) (hW : H.W = H'.W) (h : Checks H)
    (upd : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H')) hc).isSome = true)
    (fin2 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin2Block H')) hc).isSome = true)
    (copy2 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (copy .x23 H'.buf .x21 0 H'.D) hc).isSome = true) :
    Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hW; subst hB hS hW
  exact ⟨h.pro, h.fin1, h.copy1, upd, fin2, copy2, h.restore⟩

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, inn, inn, hq.x0]
  · rw [h.x20, h'.x20, outer, outer, hq.x1]
  · rw [h.x21, h'.x21, op, op, hq.x3]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ T (H := H) s₀' = T (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.x0.symm, by show s₀'.gpr .x4 + _ = s₀.gpr .x4 + _; rw [hq.x4], hq.x4.symm⟩

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {c : Prog isa} (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) t₀ s → WP isa c s (KR (H := H) t₀)) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') c
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
  rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (T (H := H) s₀') (scr s₀') ∧ t.gpr .x1 = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
      t.gpr .x1 = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c)
    pubRegs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := inn s₀) (o := T (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ _ k' _ _ => k'))

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.finalize fun _ _ => True := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue)
      fun s s' => (KR (H := H) s₀ s ∧ s.gpr .x0 = inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2) ∧
        (KR (H := H) s₀' s' ∧ s'.gpr .x0 = inn s₀' ∧ s'.gpr .x2 = s₀'.gpr .x2) :=
    rel_taint args (fun s s' e e' => by
        rw [e, e']
        refine ⟨hq.sp, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  have fin1 := fin_rel' hH hp hp' hq (c := s₀.gpr .x2)
    (F := fun s => KR (H := H) s₀ s ∧ s.gpr .x0 = inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2)
    (F' := fun s => KR (H := H) s₀' s ∧ s.gpr .x0 = inn s₀' ∧ s.gpr .x2 = s₀'.gpr .x2) hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH hp' k d x) fun _ ⟨k, a, x1, m⟩ => ⟨k, a, x1.trans hq.x2.symm, m⟩)
  have fin2 := fin_rel' hH hp hp' hq (c := BitVec.ofNat 64 (H.B + H.D)) (F := KR (H := H) s₀)
    (F' := KR (H := H) s₀') hc.fin2
    (fun _ _ h h' => kr_agree hq h h')
    (fun s k => fin2Args_ok hH hp k) (fun s k => fin2Args_ok hH hp' k)
  have upd : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s')
      (H.callUpd [mov .x0 .x19] H.B H.buf H.D) fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
    have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧
        UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧ t.gpr .x1 = BitVec.ofNat 64 H.B)
      (G' := fun t => KR (H := H) s₀' t ∧
        UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧ t.gpr .x1 = BitVec.ofNat 64 H.B)
      pubRegs (fun _ _ h h' => kr_agree hq h h') hc.upd
      (fun s h => WP.mono (updArgs_ok hH hp h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
      (fun s h => WP.mono (updArgs_ok hH hp' h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
    exact ha.seq (rel_wp (upd_rel hH (st := inn s₀) (d := T (H := H) s₀) (sc := scr s₀) (len := H.D)
      fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ _ k' _ _ => k')
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ _ k' _ _ => k'))
  have c1 := kr_rel hp hp' hq hc.copy1 fun hp s k => WP.mono (copy1_ok hp k) fun _ h => h.1
  have c2 := kr_rel hp hp' hq hc.copy2 fun hp s k => WP.mono (copy2_ok hp k) fun _ h => h.1
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact pro.seq (fin1.seq (c1.seq (upd.seq (fin2.seq (c2.seq restore)))))

end VG.Proof.Hmac.Generic.AArch64.Finalize

namespace VG.Proof.Hmac.Generic.AArch64.Finalize

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)

/-- `finalize` is verified against `finG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.F ≤ 8 * sc) (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified AArch64.target H.finalize (finG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.AArch64.Finalize

/-!
# HMAC over the streaming hash functions on AArch64: toward the instances

Untrusted: everything here is checked by Lean. What moves the generic proofs
(above) to the shared contracts of `Spec/Hmac/Generic.lean` for any hash
function (`initImp`, `finImp`, from states satisfying the shared contracts),
and carries the taint checks over between hash functions of the same sizes.
Each hash function's instance is in `Proof/Pbkdf2/Md/AArch64/Hashes/`.
-/

namespace VG.Proof.Hmac.Generic.AArch64.Instances

open VG.AArch64
open VG.Proof.Hmac.Generic.AArch64

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key). -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x2 => 0x30000 | .x3 => 1 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩, ⟨0x40000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x3 => 0x30000 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩, ⟨0x40000, 8 * sc⟩]

/-- `initG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem initImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.initContract S W AArch64.abi 16).pre s) :
    (initG S W).Implies (Spec.Hmac.initContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Hmac.initContract, Spec.Hmac.initSig, initG, stk, AArch64.abi, AArch64.argRegs] using h

/-- `finG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem finImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.finalizeContract S W AArch64.abi 16).pre s) :
    (finG S W).Implies (Spec.Hmac.finalizeContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, finG, stk, AArch64.abi, AArch64.argRegs] using h

/-- `Init.Checks` looks at the sizes of a hash function but its digest's. -/
theorem Init.Checks.of_eq {H H' : Impl.Hmac.Generic.AArch64.Hash} (hB : H.B = H'.B) (hS : H.S = H'.S)
    (hW : H.W = H'.W) (h : Init.Checks H) : Init.Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hW; subst hB hS hW
  exact ⟨h.keys, h.argI, h.argU₁, h.argU₂, h.restore⟩

end VG.Proof.Hmac.Generic.AArch64.Instances
