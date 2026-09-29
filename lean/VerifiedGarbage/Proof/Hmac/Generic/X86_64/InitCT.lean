import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Init

/-!
# HMAC over any streaming hash function on x86-64: `init`, constant time

Untrusted: everything here is checked by Lean. As for scryptROMix
(`Proof/Scrypt/X86_64/RoMixCT.lean`), two runs are related (`RelCT`):
correctness determines the registers `KR` fixes from the public arguments,
so they agree between the calls, where the taint analysis checks each piece
of code (`Checks`, evaluated for each hash function, since the code depends
on its sizes); the calls are constant time by the callees' own proofs.
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
  [.mov .rdi (.reg st)] ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 0))] ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx o ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 H.B)), .mov .r8 (.reg .r15)]

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
