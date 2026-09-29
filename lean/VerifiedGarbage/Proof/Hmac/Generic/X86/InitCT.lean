import VerifiedGarbage.Proof.Hmac.Generic.X86.Init

/-!
# HMAC over any streaming hash function on x86 (32-bit): `init`, constant time

Untrusted: everything here is checked by Lean. As on the other targets
(`Proof/Hmac/Generic/Arm/InitCT.lean`): the pieces between the calls are
checked by the taint analysis, from the registers that hold our variables
and, where they read them, the arguments on the stack (`argTaint`); the
calls are related by `init_rel` and `upd_rel`.
-/

namespace VG.Proof.Hmac.Generic.X86.Init

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash)
open VG.Proof.Hmac.Generic.X86

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  keys : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) H.initKeys hc).isSome = true
  states : ∃ hc, (VG.Taint.check taint (argTaint [.ebp] (4 + 4 * 5)) (.block Hash.initStates) hc).isSome = true
  upd : ∀ o ∈ [H.buf, H.buf + H.B], ∃ hc,
    (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .esi]) (.block (updBlock H o)) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr [.ebp]) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 5, arg s₀ i = arg s₀' i

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre (H := H) sc t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(E t).setWidth 64, 4 + 20⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_i h.a_i
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_o h.a_o
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.a_s

include hH hp hp' hq

omit hH hp hp' hq in
theorem hpR {st : Reg} {p : BitVec 32} {t : State} (hst : st = .ebx ∧ p = inn t ∨ st = .esi ∧ p = out t) :
    p = inn t ∨ p = out t := by
  rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]

omit hH hp hp' in
theorem kr_agree {s s' : State} (h : KR (H := H) sc s₀ s) (h' : KR (H := H) sc s₀' s') :
    ∀ r ∈ [Reg.ebp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.ebp, h'.ebp, scr, scr, hq.args 4 (by decide)]

omit hH hp hp' in
theorem ks_agree {s s' : State} (h : KS (H := H) sc s₀ s) (h' : KS (H := H) sc s₀' s') :
    ∀ r ∈ [Reg.esp, .ebp, .ebx, .esi], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.esp, h'.esp, E, E, hq.esp]
  · rw [h.ebp, h'.ebp, scr, scr, hq.args 4 (by decide)]
  · rw [h.ebx, h'.ebx, inn, inn, hq.args 0 (by decide)]
  · rw [h.esi, h'.esi, out, out, hq.args 1 (by decide)]

/-- A call of `init` on the state in `st` (`ebx` for `inner`, `esi` for `outer`). -/
theorem callInit_rel {st : Reg} {p : BitVec 32} (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) :
    RelCT isa (fun s s' => KS (H := H) sc s₀ s ∧ KS (H := H) sc s₀' s') (H.callInit st)
      fun s s' => KS (H := H) sc s₀ s ∧ KS (H := H) sc s₀' s' := by
  have hst' : st = .ebx ∧ p = inn s₀' ∨ st = .esi ∧ p = out s₀' := by
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2, inn, inn, hq.args 0 (by decide)]⟩
    · exact .inr ⟨h1, by rw [h2, out, out, hq.args 1 (by decide)]⟩
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hpR' : p = inn s₀' ∨ p = out s₀' := by rcases hst' with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  refine rel_wp (F := KS (H := H) sc s₀) (F' := KS (H := H) sc s₀')
    (init_rel hH (sp := E s₀) (r := st) (st := p) fun s s' ⟨k, k'⟩ => ?_)
    (fun _ k => callInit_ok hH hp k hst fun _ k' _ _ => k')
    (fun _ k => callInit_ok hH hp' k hst' fun _ k' _ _ => k')
  obtain ⟨_, dK, _, np⟩ := state_disj hp hpR
  obtain ⟨_, dK', _, np'⟩ := state_disj hp' hpR'
  refine ⟨{ hst := ?_, hr := ?_, sp48 := ?_, cw := ?_, b_st := ?_, nst := np },
    { hst := ?_, hr := ?_, sp48 := ?_, cw := ?_, b_st := ?_, nst := np' }, k.esp, by rw [k'.esp, E, E, hq.esp]⟩
  · rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [k.ebx, k.esi]
  · rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · rw [k.esp]; exact hp.sp48
  · rw [k.wr]; exact covers_one (state_in hp hpR)
  · rw [stk_eq k.toKR]; exact dK
  · rcases hst' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [k'.ebx, k'.esi]
  · rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  · rw [k'.esp]; exact hp'.sp48
  · rw [k'.wr]; exact covers_one (state_in hp' hpR')
  · rw [stk_eq k'.toKR]; exact dK'

omit hc in
/-- A call of `update` on the state in `st`, with the bytes at `scratch + o`. -/
theorem callUpd_rel {st : Reg} {p : BitVec 32} (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) {o : Nat}
    (ho : o = H.buf ∨ o = H.buf + H.B)
    (hck : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .esi]) (.block (updBlock H o)) hc).isSome = true) :
    RelCT isa (fun s s' => KS (H := H) sc s₀ s ∧ KS (H := H) sc s₀' s') (H.callUpd [] st .edi 0 o H.B)
      fun s s' => KS (H := H) sc s₀ s ∧ KS (H := H) sc s₀' s' := by
  have hst' : st = .ebx ∧ p = inn s₀' ∨ st = .esi ∧ p = out s₀' := by
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2, inn, inn, hq.args 0 (by decide)]⟩
    · exact .inr ⟨h1, by rw [h2, out, out, hq.args 1 (by decide)]⟩
  have e4 : scr s₀' = scr s₀ := (hq.args 4 (by decide)).symm
  have e8 : dO s₀' o = dO s₀ o := by rw [dO, dO, e4]
  have ha : RelCT isa (fun s s' => KS (H := H) sc s₀ s ∧ KS (H := H) sc s₀' s') (.block (updBlock H o))
      fun s s' => (KS (H := H) sc s₀ s ∧ UpdArgs hH s .edi st p (dO s₀ o) (scr s₀) (BitVec.ofNat 32 0) H.B) ∧
        (KS (H := H) sc s₀' s' ∧ UpdArgs hH s' .edi st p (dO s₀ o) (scr s₀) (BitVec.ofNat 32 0) H.B) :=
    rel_agree (τr [.esp, .ebp, .ebx, .esi]) (fun _ _ h h' => agree_regs (ks_agree hq h h')) hck
      (fun _ h => WP.mono (updArgs_ok hH hp h hst ho) fun _ ⟨k, a, _⟩ => ⟨k, a⟩)
      (fun _ h => WP.mono (updArgs_ok hH hp' h hst' ho) fun _ ⟨k, a, _⟩ => ⟨k, e8 ▸ e4 ▸ a⟩)
  refine ha.seq (rel_wp
    (F := fun s => KS (H := H) sc s₀ s ∧ UpdArgs hH s .edi st p (dO s₀ o) (scr s₀) (BitVec.ofNat 32 0) H.B)
    (F' := fun s => KS (H := H) sc s₀' s ∧ UpdArgs hH s .edi st p (dO s₀ o) (scr s₀) (BitVec.ofNat 32 0) H.B)
    (upd_rel hH (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ => ⟨a, a', k.esp, by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, a⟩ => updCall_ok hH hp k (hpR hst) a fun _ k' _ _ => k')
    (fun _ ⟨k, a⟩ => updCall_ok hH hp' k (hpR hst') (e4.symm ▸ a) fun _ k' _ _ => k'))

include hc in
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.init fun _ _ => True := by
  have keys : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.initKeys
      fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s' :=
    rel_agree (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        subst e e'
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.keys
      (fun _ e => by subst e; exact WP.mono (keys_ok sc hp) fun _ h => h.kr)
      (fun _ e => by subst e; exact WP.mono (keys_ok sc hp') fun _ h => h.kr)
  have states : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s') (.block Hash.initStates)
      fun s s' => KS (H := H) sc s₀ s ∧ KS (H := H) sc s₀' s' :=
    rel_agree (argTaint [.ebp] (4 + 4 * 5)) (fun s s' k k' =>
        agree_argTaint (kr_agree hq k k') (by rw [k.esp, k'.esp, E, E, hq.esp]) (args_out hp k.esp k.wr)
          (args_out hp' k'.esp k'.wr) fun i hi => by rw [k.argEq hp hi, k'.argEq hp' hi, hq.args i hi]) hc.states
      (fun _ k => WP.mono (states_ok hp k) fun _ h => h.1)
      (fun _ k => WP.mono (states_ok hp' k) fun _ h => h.1)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KS (H := H) sc s₀ s ∧ KS (H := H) sc s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebp]) (fun _ _ h => agree_regs (kr_agree hq h.1.toKR h.2.toKR)) hr
  exact keys.seq (states.seq ((callInit_rel hH hp hp' hq (.inl ⟨rfl, rfl⟩)).seq
    ((callUpd_rel hH hp hp' hq (.inl ⟨rfl, rfl⟩) (.inl rfl) (hc.upd _ (by simp))).seq
    ((callInit_rel hH hp hp' hq (.inr ⟨rfl, rfl⟩)).seq
    ((callUpd_rel hH hp hp' hq (.inr ⟨rfl, rfl⟩) (.inr rfl) (hc.upd _ (by simp))).seq restore)))))

end VG.Proof.Hmac.Generic.X86.Init

namespace VG.Proof.Hmac.Generic.X86.Init

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash)
open VG.Proof.Hmac.Generic.X86

/-- `init` is verified against `initG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + 2 * H.B ≤ 8 * sc) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified X86.target H.init (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH sc hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2⟩ := hpub
    exact (ct hH hc (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `init` reads and writes, of those `initW` gives it. -/
def narrowRd (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (S sc : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 1).setWidth 64, S⟩, ⟨(arg s 4).setWidth 64, 8 * sc⟩]

/-- `init` is verified against `initW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + 2 * H.B ≤ 8 * sc) (hsat : ∃ s, (initW hH.SH sc).pre s) :
    Verified X86.target H.init (initW hH.SH sc) := by
  have pre : ∀ s, (initW hH.SH sc).pre s →
      (initG hH.SH sc).pre (s.withRegions (narrowRd s) (narrowWr hH.SH.stateBytes sc s)) := by
    intro s h
    obtain ⟨h0, _, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩ := h
    simp only [initG, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨h0, trivial, trivial, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩
  refine Verified.narrowTo (verified hH hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd) (narrowWr hH.SH.stateBytes sc) pre (fun s h => ?_) (fun s h => ?_)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨_, h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
        by simp, by simp⟩
  · obtain ⟨_, _, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

end VG.Proof.Hmac.Generic.X86.Init
