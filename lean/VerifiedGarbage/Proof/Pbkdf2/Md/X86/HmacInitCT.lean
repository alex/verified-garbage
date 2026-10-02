import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInit

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `init`, constant time

As `finalize` (`HmacFinCT.lean`): the pieces between the calls are checked
by the taint analysis, the prologue and the blocks, which read the arguments
on the stack, with them public (`argTaint`); the calls of the streaming
`init` are related by `init_rel`, those of the compression function by
`cmp_rel`. Then `init` is verified against the contract with the arguments
read only (`initG`), and with them writable (`initW`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initG initW argTaint ArgsOut agree_argTaint rel_agree rel_wp init_rel)

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block H.initPrologue) hc).isSome = true
  blocks : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .esi] (4 + 4 * 5)) H.blocks hc).isSome = true
  toOuter : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .esi]) (.block H.toOuter) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr [.ebp]) (.block H.st.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 5, arg s₀ i = arg s₀' i

variable {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
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

include hq in
theorem kr_agree {s s' : State} (h : KR (H := H) sc s₀ s) (h' : KR (H := H) sc s₀' s') :
    ∀ r ∈ [Reg.esp, .ebp, .esi], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.esp, h'.esp, E, E, hq.esp]
  · rw [h.ebp, h'.ebp, scr, scr, hq.args 4 (by decide)]
  · rw [h.esi, h'.esi, out, out, hq.args 1 (by decide)]

include hO hp hp' hq

/-- A call of the streaming `init` on the state in `st` (`ebx` for `inner`,
`esi` for `outer`), with `ebx` at `inner`. -/
theorem callInit_rel {st : Reg} {p : BitVec 32} (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) :
    RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀) ∧ (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀'))
      (H.st.callInit st)
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀) ∧ (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀') := by
  have hz := hO.sizes
  have hst' : st = .ebx ∧ p = inn s₀' ∨ st = .esi ∧ p = out s₀' := by
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2, inn, inn, hq.args 0 (by decide)]⟩
    · exact .inr ⟨h1, by rw [h2, out, out, hq.args 1 (by decide)]⟩
  have hsr : ∀ {t u : State}, KR (H := H) sc t u → u.gpr .ebx = inn t →
      (st = .ebx ∧ p = inn t ∨ st = .esi ∧ p = out t) → u.gpr st = p := fun k b h => by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact b
    · exact k.esi
  refine rel_wp (F := fun s => KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀)
    (F' := fun s => KR (H := H) sc s₀' s ∧ s.gpr .ebx = inn s₀')
    (init_rel hO.hH (sp := E s₀) (r := st) (st := p) fun s s' ⟨⟨k, b⟩, ⟨k', b'⟩⟩ =>
      ⟨initArgs hz hp k hst (hsr k b hst), initArgs hz hp' k' hst' (hsr k' b' hst'), k.esp,
        by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, b⟩ => callInit_ok hz hp hO k hst (hsr k b hst) fun _ k' b' _ _ => ⟨k', b'.trans b⟩)
    (fun _ ⟨k, b⟩ => callInit_ok hz hp' hO k hst' (hsr k b hst') fun _ k' b' _ _ => ⟨k', b'.trans b⟩)

/-- A compression of the buffer of the state at `p`, in `ebx`, with `eax`
at it. -/
theorem cmpS_rel {p p' : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) (hpR' : p' = inn s₀' ∨ p' = out s₀')
    (he : p' = p) :
    RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = p ∧ s.gpr .eax = p + BitVec.ofNat 32 H.N) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = p' ∧ s'.gpr .eax = p' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s' := by
  have hz := hO.sizes
  have hB : 0 < H.B := by have := hz.B4; omega
  have e4 : scr s₀' = scr s₀ := (hq.args 4 (by decide)).symm
  exact rel_wp (cmp_rel hO.comp hB (sp := E s₀) fun s s' ⟨⟨k, b, a⟩, ⟨k', b', a'⟩⟩ =>
      ⟨cmpArgs hz hp k hpR b a, by have := cmpArgs hz hp' k' hpR' b' a'; rwa [he, e4] at this, k.esp,
        by rw [k'.esp, E, E, hq.esp]⟩)
    (fun _ ⟨k, b, a⟩ => cmpS_ok hz hp hO k hpR b a fun _ k' _ _ _ => k')
    (fun _ ⟨k, b, a⟩ => cmpS_ok hz hp' hO k hpR' b a fun _ k' _ _ _ => k')

include hc in
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have hz := hO.sizes
  have e0 : inn s₀' = inn s₀ := (hq.args 0 (by decide)).symm
  have e1 : out s₀' = out s₀ := (hq.args 1 (by decide)).symm
  -- The prologue.
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀) ∧ (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀') :=
    rel_agree (argTaint [] (4 + 4 * 5)) (fun s s' e e' => by
        subst e e'
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
      (fun _ e => by subst e; exact pro_ok hz hp)
      (fun _ e => by subst e; exact pro_ok hz hp')
  -- The blocks.
  have blk : RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀')) H.blocks
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = inn s₀ ∧ s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = inn s₀' ∧ s'.gpr .eax = inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (argTaint [.ebp, .ebx, .esi] (4 + 4 * 5)) (fun s s' ⟨k, b⟩ ⟨k', b'⟩ =>
        agree_argTaint (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact kr_agree hq k k' _ (by simp)
            · rw [b, b', e0]
            · exact kr_agree hq k k' _ (by simp))
          (kr_agree hq k k' _ (by simp)) (args_out hp k.esp k.wr) (args_out hp' k'.esp k'.wr)
          fun i hi => by rw [k.argEq hp hi, k'.argEq hp' hi, hq.args i hi]) hc.blocks
      (fun _ ⟨k, b⟩ => blocks_ok hz hp k b)
      (fun _ ⟨k, b⟩ => blocks_ok hz hp' k b)
  -- From the inner state to the outer one.
  have tO : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s') (.block H.toOuter)
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .ebx = out s₀ ∧ s.gpr .eax = out s₀ + BitVec.ofNat 32 H.N) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .ebx = out s₀' ∧ s'.gpr .eax = out s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (τr [.esp, .ebp, .esi]) (fun _ _ k k' => agree_regs (kr_agree hq k k')) hc.toOuter
      (fun _ k => WP.mono (toOuter_ok k) fun _ ⟨k', b, a, _⟩ => ⟨k', b, a⟩)
      (fun _ k => WP.mono (toOuter_ok k) fun _ ⟨k', b, a, _⟩ => ⟨k', b, a⟩)
  -- The end.
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s') (.block H.st.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebp]) (fun _ _ h => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact kr_agree hq h.1 h.2 _ (by simp)) hr
  exact pro.seq ((callInit_rel hO hp hp' hq (.inl ⟨rfl, rfl⟩)).seq
    ((callInit_rel hO hp hp' hq (.inr ⟨rfl, rfl⟩)).seq
    (blk.seq ((cmpS_rel hO hp hp' hq (.inl rfl) (.inl rfl) e0).seq
    (tO.seq ((cmpS_rel hO hp hp' hq (.inr rfl) (.inr rfl) e1).seq restore))))))

end VG.Proof.Pbkdf2.Md.X86.HmacInit

namespace VG.Proof.Pbkdf2.Md.X86.HmacInit

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initG initW)

/-- `init` is verified against `initG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H) (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (initG hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacInit (initG hO.hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hO (pre_of sc hO hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2⟩ := hpub
    exact (ct hO hc (pre_of sc hO h₁ hfit) (pre_of sc hO h₂ hfit) ⟨h1, h2⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `init` reads and writes, of those `initW` gives it. -/
def narrowRd (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (S sc : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 1).setWidth 64, S⟩, ⟨(arg s 4).setWidth 64, 8 * sc⟩]

/-- `init` is verified against `initW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H) (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (initW hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacInit (initW hO.hH.SH sc) := by
  have pre : ∀ s, (initW hO.hH.SH sc).pre s →
      (initG hO.hH.SH sc).pre (s.withRegions (narrowRd s)
        (narrowWr hO.hH.SH.stateBytes sc s)) := by
    intro s h
    obtain ⟨h0, _, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩ := h
    simp only [initG, narrowRd, narrowWr, arg_withRegions,
      argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
    exact ⟨h0, trivial, trivial, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24⟩
  refine Verified.narrowTo (verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd) (narrowWr hO.hH.SH.stateBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨_, h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
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

end VG.Proof.Pbkdf2.Md.X86.HmacInit
