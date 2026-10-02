import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Init
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.Implies

/-!
# HMAC over any streaming hash function on x86-64: `init`, constant time

As for scryptROMix (`Proof/Scrypt/X86_64/RoMixCT.lean`), two runs are related
(`RelCT`): correctness determines the registers `KR` fixes from the public
arguments, so they agree between the calls, where the taint analysis checks
each piece of code (`Checks`, evaluated for each hash function, since the code
depends on its sizes); the calls are constant time by the callees' own proofs.
-/

namespace VG.Proof.Hmac.Generic.X86_64.Init

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .r12, .r15, .rsp]

/-- The argument registers. -/
abbrev args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

/-- The block that sets up a call of `update` from `st`, at offset `o`. -/
abbrev updBlock (H : Hash) (st : Reg) (o : Nat) : List Instr :=
  ([.mov .rdi (.reg st)] : List Instr) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 0))] : List Instr) ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx o ++ ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.B)), .mov .r8 (.reg .r15)] : List Instr)

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  keys : ∃ hc, (Taint.check taint (Taint.ofRegs args) H.initKeys hc).isSome = true
  argI : ∀ st ∈ [Reg.rbx, .r12], ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block [.mov .rdi (.reg st)]) hc).isSome = true
  argU₁ : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (updBlock H .rbx H.buf)) hc).isSome = true
  argU₂ : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (updBlock H .r12 (H.buf + H.B))) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, inn, inn, hq.rdi]
  · rw [h.r12, h'.r12, out, out, hq.rsi]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hc hp hp' hq

/-- A call of `init` on the state in `st` (`rbx` for `inner`, `r12` for `outer`). -/
theorem callInit_rel {st : Reg} (hst : st = .rbx ∨ st = .r12) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (H.callInit st)
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  -- The state's address, the same in both runs.
  let p : Addr := if st = .rbx then inn s₀ else out s₀
  have hpR : p = inn s₀ ∨ p = out s₀ := by by_cases h : st = .rbx <;> simp [p, h]
  have hpR' : p = inn s₀' ∨ p = out s₀' := by
    show p = s₀'.gpr .rdi ∨ p = s₀'.gpr .rsi; rw [← hq.rdi, ← hq.rsi]; exact hpR
  have hs : ∀ {t : State}, KR (H := H) s₀ t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.rbx]
    · simp [p, h.r12]
  have hs' : ∀ {t : State}, KR (H := H) s₀' t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.rbx, hq.rdi]
    · simp [p, h.r12, hq.rsi]
  have ha : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block [.mov .rdi (.reg st)])
      fun s s' => (KR (H := H) s₀ s ∧ s.gpr .rdi = p ∧ True) ∧ (KR (H := H) s₀' s' ∧ s'.gpr .rdi = p ∧ True) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') (hc.argI st (by rcases hst with rfl | rfl <;> simp))
      (fun _ h => WP.mono (initArgs_ok h (hs h)) fun _ ⟨k, d, _⟩ => ⟨k, d, trivial⟩)
      (fun _ h => WP.mono (initArgs_ok h (hs' h)) fun _ ⟨k, d, _⟩ => ⟨k, d, trivial⟩)
  refine ha.seq (rel_wp (F := fun s => KR (H := H) s₀ s ∧ s.gpr .rdi = p ∧ True)
    (F' := fun s => KR (H := H) s₀' s ∧ s.gpr .rdi = p ∧ True)
    (init_rel hH (st := p) fun s s' h => ?_)
    (fun _ ⟨k, d, _⟩ => initCall_ok hH hp k d hpR fun _ k' _ _ => k')
    (fun _ ⟨k, d, _⟩ => initCall_ok hH hp' k d hpR' fun _ k' _ _ => k'))
  obtain ⟨⟨k, d, _⟩, ⟨k', d', _⟩⟩ := h
  obtain ⟨c, sk⟩ := initCall_args hp k hpR
  obtain ⟨c', sk'⟩ := initCall_args hp' k' hpR'
  exact ⟨d, d', c, c', sk, sk', by rw [k.rsp, k'.rsp, hq.rsp]⟩

omit hc in
/-- A call of `update` on the state in `st`, with the bytes at `scratch + o`. -/
theorem callUpd_rel {st : Reg} (hst : st = .rbx ∨ st = .r12) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (updBlock H st o)) hc).isSome = true) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (H.callUpd [.mov .rdi (.reg st)] 0 o H.B)
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  let p : Addr := if st = .rbx then inn s₀ else out s₀
  have hpR : p = inn s₀ ∨ p = out s₀ := by by_cases h : st = .rbx <;> simp [p, h]
  have hpR' : p = inn s₀' ∨ p = out s₀' := by
    show p = s₀'.gpr .rdi ∨ p = s₀'.gpr .rsi; rw [← hq.rdi, ← hq.rsi]; exact hpR
  have hs : ∀ {t : State}, KR (H := H) s₀ t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.rbx]
    · simp [p, h.r12]
  have hs' : ∀ {t : State}, KR (H := H) s₀' t → t.gpr st = p := fun h => by
    rcases hst with rfl | rfl
    · simp [p, h.rbx, hq.rdi]
    · simp [p, h.r12, hq.rsi]
  have e8 : dO s₀' o = dO s₀ o := by rw [dO, dO, scr, scr, hq.r8]
  have e8' : scr s₀' = scr s₀ := hq.r8.symm
  have ha : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block (updBlock H st o))
      fun s s' => (KR (H := H) s₀ s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ s.gpr .rsi = 0) ∧
        (KR (H := H) s₀' s' ∧ UpdArgs hH s' p (dO s₀ o) (scr s₀) H.B ∧ s'.gpr .rsi = 0) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hck
      (fun _ h => WP.mono (updArgs_ok hH hp h hst (hs h) hpR ho) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
      (fun _ h => WP.mono (updArgs_ok hH hp' h hst (hs' h) hpR' ho) fun _ ⟨k, a, si, _⟩ =>
        ⟨k, e8 ▸ e8' ▸ a, si⟩)
  refine ha.seq (rel_wp (F := fun s => KR (H := H) s₀ s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ s.gpr .rsi = 0)
    (F' := fun s => KR (H := H) s₀' s ∧ UpdArgs hH s p (dO s₀ o) (scr s₀) H.B ∧ s.gpr .rsi = 0)
    (upd_rel hH (st := p) (d := dO s₀ o) (sc := scr s₀) (len := H.B)
    fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun _ ⟨k, a, si⟩ => updCall_ok hH hp k hpR a si fun _ k' _ _ => k')
    (fun _ ⟨k, a, si⟩ => updCall_ok hH hp' k hpR' (e8'.symm ▸ a) si fun _ k' _ _ => k'))

theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.init fun _ _ => True := by
  have keys : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.initKeys
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
    rel_taint args (fun s s' e e' r hr => by
        subst e e'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.keys
      (fun _ e => by subst e; exact WP.mono (keys_ok sc hp) fun _ h => h.kr)
      (fun _ e => by subst e; exact WP.mono (keys_ok sc hp') fun _ h => h.kr)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs)
      (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1 h.2)) hr
  exact keys.seq ((callInit_rel hH hc hp hp' hq (.inl rfl)).seq
    ((callUpd_rel hH hp hp' hq (.inl rfl) (.inl rfl) hc.argU₁).seq
    ((callInit_rel hH hc hp hp' hq (.inr rfl)).seq
    ((callUpd_rel hH hp hp' hq (.inr rfl) (.inr rfl) hc.argU₂).seq restore))))

end VG.Proof.Hmac.Generic.X86_64.Init

namespace VG.Proof.Hmac.Generic.X86_64.Init

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)

/-- `init` is verified against `initG`, given the taint checks and the facts
about its code that the kernel checks for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + 2 * H.B ≤ 8 * sc) (hmx : H.init.allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified X86_64.target H.init (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH sc hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH hc (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.X86_64.Init

/-!
# HMAC over any streaming hash function on x86-64: `finalize`, constant time

As for `init` (above).
-/

namespace VG.Proof.Hmac.Generic.X86_64.Finalize

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash copy)
open VG.Proof.Hmac.Generic.X86_64
open VG.Proof.Hmac.Generic.X86_64.Init (PubEq args)

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Hash) : List Instr :=
  [] ++ ([.mov .rsi (.reg .rdx)] : List Instr) ++ VG.Impl.Hmac.Generic.X86_64.scr .rdx H.buf ++ ([.mov .rcx (.reg .r15)] : List Instr)

/-- The block that sets up the second call of `finalize`. -/
abbrev fin2Block (H : Hash) : List Instr :=
  ([.mov .rdi (.reg .rbx)] : List Instr) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 (H.B + H.D)))] : List Instr) ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx H.buf ++ ([.mov .rcx (.reg .r15)] : List Instr)

/-- The block that sets up the call of `update`. -/
abbrev updBlock (H : Hash) : List Instr :=
  ([.mov .rdi (.reg .rbx)] : List Instr) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 H.B))] : List Instr) ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx H.buf ++ ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D)), .mov .r8 (.reg .r15)] : List Instr)

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (fin1Block H)) hc).isSome = true
  copy1 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (copy .r12 0 .rbx 0 H.S) hc).isSome = true
  upd : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (updBlock H)) hc).isSome = true
  fin2 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (fin2Block H)) hc).isSome = true
  copy2 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (copy .r15 H.buf .r13 0 H.D) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.restore) hc).isSome = true

/-- The checks of the parts of `finalize` that do not depend on the size of
the digest carry over to a hash function of the same sizes but that one. -/
theorem Checks.of_sizes {H H' : Hash} (hB : H.B = H'.B) (hS : H.S = H'.S) (hW : H.W = H'.W) (h : Checks H)
    (upd : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (updBlock H')) hc).isSome = true)
    (fin2 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (fin2Block H')) hc).isSome = true)
    (copy2 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (copy .r15 H'.buf .r13 0 H'.D) hc).isSome = true) :
    Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hW; subst hB hS hW
  exact ⟨h.pro, h.fin1, h.copy1, upd, fin2, copy2, h.restore⟩

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, inn, inn, hq.rdi]
  · rw [h.r12, h'.r12, outer, outer, hq.rsi]
  · rw [h.r13, h'.r13, op, op, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ T (H := H) s₀' = T (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.rdi.symm, by show s₀'.gpr .r8 + _ = s₀.gpr .r8 + _; rw [hq.r8], hq.r8.symm⟩

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {c : Prog isa} (hck : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) t₀ s → WP isa c s (KR (H := H) t₀)) :
    RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') c
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' :=
  rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ kregs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (T (H := H) s₀') (scr s₀') ∧ t.gpr .rsi = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
      t.gpr .rsi = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c)
    kregs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, si⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := inn s₀) (o := T (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.finalize fun _ _ => True := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue)
      fun s s' => (KR (H := H) s₀ s ∧ s.gpr .rdi = inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx) ∧
        (KR (H := H) s₀' s' ∧ s'.gpr .rdi = inn s₀' ∧ s'.gpr .rdx = s₀'.gpr .rdx) :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  have fin1 := fin_rel' hH hp hp' hq (c := s₀.gpr .rdx)
    (F := fun s => KR (H := H) s₀ s ∧ s.gpr .rdi = inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx)
    (F' := fun s => KR (H := H) s₀' s ∧ s.gpr .rdi = inn s₀' ∧ s.gpr .rdx = s₀'.gpr .rdx) hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH hp' k d x) fun _ ⟨k, a, si, m⟩ => ⟨k, a, si.trans hq.rdx.symm, m⟩)
  have fin2 := fin_rel' hH hp hp' hq (c := BitVec.ofNat 64 (H.B + H.D)) (F := KR (H := H) s₀)
    (F' := KR (H := H) s₀') hc.fin2
    (fun _ _ h h' => kr_agree hq h h')
    (fun s k => fin2Args_ok hH hp k) (fun s k => fin2Args_ok hH hp' k)
  have upd : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s')
      (H.callUpd [.mov .rdi (.reg .rbx)] H.B H.buf H.D) fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
    have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧
        UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧ t.gpr .rsi = BitVec.ofNat 64 H.B)
      (G' := fun t => KR (H := H) s₀' t ∧
        UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧ t.gpr .rsi = BitVec.ofNat 64 H.B)
      kregs (fun _ _ h h' => kr_agree hq h h') hc.upd
      (fun s h => WP.mono (updArgs_ok hH hp h) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
      (fun s h => WP.mono (updArgs_ok hH hp' h) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, si⟩)
    exact ha.seq (rel_wp (upd_rel hH (st := inn s₀) (d := T (H := H) s₀) (sc := scr s₀) (len := H.D)
      fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))
  have c1 := kr_rel hp hp' hq hc.copy1 fun hp s k => WP.mono (copy1_ok hp k) fun _ h => h.1
  have c2 := kr_rel hp hp' hq hc.copy2 fun hp s k => WP.mono (copy2_ok hp k) fun _ h => h.1
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1 h.2)) hr
  exact pro.seq (fin1.seq (c1.seq (upd.seq (fin2.seq (c2.seq restore)))))

end VG.Proof.Hmac.Generic.X86_64.Finalize

namespace VG.Proof.Hmac.Generic.X86_64.Finalize

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)

/-- `finalize` is verified against `finG`, given the taint checks and the
facts about its code that the kernel checks for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.F ≤ 8 * sc) (hmx : H.finalize.allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified X86_64.target H.finalize (finG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH sc hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.X86_64.Finalize

/-!
# HMAC over the streaming hash functions on x86-64: toward the instances

What moves the generic proofs (above) to the shared contracts of
`Spec/Hmac/Generic.lean` for any hash function (`initImp`, `finImp`, from
states satisfying the shared contracts), and carries the taint checks over
between hash functions of the same sizes. Each hash function's instance is in
`Proof/Pbkdf2/Md/X86_64/Hashes/`.
-/

namespace VG.Proof.Hmac.Generic.X86_64.Instances

open VG.X86_64
open VG.Proof.Hmac.Generic.X86_64

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key). -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rdx => 0x30000 | .rcx => 1 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩, ⟨0x40000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩, ⟨0x40000, 8 * sc⟩]

/-- `initG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem initImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.initContract S W X86_64.abi 16).pre s) :
    (initG S W).Implies (Spec.Hmac.initContract S W X86_64.abi 16) := by
  generic_implies [
    Spec.Hmac.initContract, Spec.Hmac.initSig, initG, X86_64.abi, X86_64.argRegs] using h

/-- `finG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem finImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.finalizeContract S W X86_64.abi 16).pre s) :
    (finG S W).Implies (Spec.Hmac.finalizeContract S W X86_64.abi 16) := by
  generic_implies [
    Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, finG, X86_64.abi, X86_64.argRegs] using h

/-- The checks do not look at the functions `init` and `finalize` call, so
they hold for every hash function of the same sizes. -/
theorem Init.Checks.of_eq {H H' : Impl.Hmac.Generic.X86_64.Hash} (hB : H.B = H'.B) (hW : H.W = H'.W) (h : Init.Checks H) :
    Init.Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hW; subst hB hW
  exact ⟨h.keys, h.argI, h.argU₁, h.argU₂, h.restore⟩

theorem Finalize.Checks.of_eq {H H' : Impl.Hmac.Generic.X86_64.Hash} (hB : H.B = H'.B) (hS : H.S = H'.S) (hD : H.D = H'.D)
    (hW : H.W = H'.W) (h : Finalize.Checks H) : Finalize.Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hD hW; subst hB hS hD hW
  exact ⟨h.pro, h.fin1, h.copy1, h.upd, h.fin2, h.copy2, h.restore⟩

end VG.Proof.Hmac.Generic.X86_64.Instances
