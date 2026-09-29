import VerifiedGarbage.Proof.Hmac.Generic.X86.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.X86.InitCT

/-!
# HMAC over any streaming hash function on x86 (32-bit): `finalize`, constant time

Untrusted: everything here is checked by Lean. As for `init`
(`Proof/Hmac/Generic/X86/InitCT.lean`): the pieces between the calls are
checked by the taint analysis, the prologue and the first call's arguments
reading the arguments on the stack (`argTaint`); the calls are related by
`fin_rel` and `upd_rel`.
-/

namespace VG.Proof.Hmac.Generic.X86.Finalize

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash copy)
open VG.Proof.Hmac.Generic.X86

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 6)) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .edi] (4 + 4 * 6))
    (.block ([] ++ Hash.count1 ++ Impl.Hmac.Generic.X86.scr .edx H.buf)) hc).isSome = true
  copy1 : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi, .esi]) (copy .esi 0 .ebx 0 H.S) hc).isSome = true
  upd : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi])
    (.block ([] ++ [.mov .eax (.imm 0), .mov .esi (.imm (BitVec.ofNat 32 H.B)),
      .mov .ecx (.imm (BitVec.ofNat 32 H.D))] ++ Impl.Hmac.Generic.X86.scr .edx H.buf)) hc).isSome = true
  fin2 : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi])
    (.block ([] ++ H.count2 ++ Impl.Hmac.Generic.X86.scr .edx H.buf)) hc).isSome = true
  copy2 : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi]) (copy .ebp H.buf .edi 0 H.D) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (τr [.ebp]) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 6, arg s₀ i = arg s₀' i

variable {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre (H := H) sc t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
    ArgsOut 6 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 6⟩ : Region) = ⟨(E t).setWidth 64, 4 + 24⟩ := by rw [hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_i h.a_i
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_p h.a_p
  · exact Taint.frame_disjoint (by have := h.spf; omega) h.r_s h.a_s

include hq in
theorem kr_agree {s s' : State} (h : KR (H := H) sc s₀ s) (h' : KR (H := H) sc s₀' s') :
    ∀ r ∈ [Reg.esp, .ebp, .ebx, .edi], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.esp, h'.esp, E, E, hq.esp]
  · rw [h.ebp, h'.ebp, scr, scr, hq.args 5 (by decide)]
  · rw [h.ebx, h'.ebx, inn, inn, hq.args 0 (by decide)]
  · rw [h.edi, h'.edi, op, op, hq.args 4 (by decide)]

theorem sub_regs {l l' : List Reg} (h : ∀ r ∈ l, r ∈ l') {s s' : State} (hs : ∀ r ∈ l', s.gpr r = s'.gpr r) :
    ∀ r ∈ l, s.gpr r = s'.gpr r := fun r hr => hs r (h r hr)

include hH hc hp hp' hq

theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.finalize fun _ _ => True := by
  have e5 : scr s₀' = scr s₀ := (hq.args 5 (by decide)).symm
  have e0 : inn s₀' = inn s₀ := (hq.args 0 (by decide)).symm
  have eT : tO (H := H) s₀' = tO (H := H) s₀ := by rw [tO, tO, e5]
  have e2 : arg s₀' 2 = arg s₀ 2 := (hq.args 2 (by decide)).symm
  have e3 : arg s₀' 3 = arg s₀ 3 := (hq.args 3 (by decide)).symm
  -- The prologue.
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue)
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧ (KR (H := H) sc s₀' s' ∧ s'.gpr .esi = outer s₀') :=
    rel_agree (argTaint [] (4 + 4 * 6)) (fun s s' e e' => by
        subst e e'
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
      (fun _ e => by subst e; exact WP.mono (pro_ok hp) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ e => by subst e; exact WP.mono (pro_ok hp') fun _ h => ⟨h.1, h.2.1⟩)
  -- The first call.
  have a1 : RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .esi = outer s₀'))
      (.block ([] ++ Hash.count1 ++ Impl.Hmac.Generic.X86.scr .edx H.buf))
      fun s s' => (KR (H := H) sc s₀ s ∧ FinArgs hH s .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧
          s.gpr .esi = outer s₀) ∧
        (KR (H := H) sc s₀' s' ∧ FinArgs hH s' .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧
          s'.gpr .esi = outer s₀') :=
    rel_agree (argTaint [.ebp, .ebx, .edi] (4 + 4 * 6)) (fun s s' ⟨k, _⟩ ⟨k', _⟩ =>
        agree_argTaint (sub_regs (by decide) (kr_agree hq k k')) (by rw [k.esp, k'.esp, E, E, hq.esp])
          (args_out hp k.esp k.wr) (args_out hp' k'.esp k'.wr)
          fun i hi => by rw [k.argEq hp hi, k'.argEq hp' hi, hq.args i hi]) hc.fin1
      (fun _ ⟨k, si⟩ => WP.mono (fin1Args_ok hH hp k) fun _ ⟨k₁, a, s₁, _⟩ => ⟨k₁, a, s₁.trans si⟩)
      (fun _ ⟨k, si⟩ => WP.mono (fin1Args_ok hH hp' k) fun _ ⟨k₁, a, s₁, _⟩ =>
        ⟨k₁, by rw [← e0, ← eT, ← e5, ← e2, ← e3]; exact a, s₁.trans si⟩)
  have c1 : RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧
        FinArgs hH s .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H) sc s₀' s' ∧ FinArgs hH s' .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧
          s'.gpr .esi = outer s₀'))
      (.frame (.push (fin5 .ebx)) (.call H.finN H.finC) (.pop .eax (fin5 .ebx).length))
      fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧ (KR (H := H) sc s₀' s' ∧ s'.gpr .esi = outer s₀') :=
    rel_wp (fin_rel hH (sp := E s₀) fun s s' ⟨⟨k, a, _⟩, ⟨k', a', _⟩⟩ =>
        ⟨a, a', k.esp, by rw [k'.esp, E, E, hq.esp]⟩)
      (fun _ ⟨k, a, si⟩ => finCall_ok hH hp k a fun _ k' si' _ _ => ⟨k', si'.trans si⟩)
      (fun _ ⟨k, a, si⟩ => finCall_ok hH hp' k (by rw [e0, eT, e5]; exact a)
        fun _ k' si' _ _ => ⟨k', si'.trans si⟩)
  -- The copy of the outer state.
  have cp1 : RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H) sc s₀' s' ∧ s'.gpr .esi = outer s₀')) (copy .esi 0 .ebx 0 H.S)
      fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s' :=
    rel_agree (τr [.esp, .ebp, .ebx, .edi, .esi]) (fun s s' ⟨k, si⟩ ⟨k', si'⟩ => agree_regs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · rw [si, si', outer, outer, hq.args 1 (by decide)]) hc.copy1
      (fun _ ⟨k, si⟩ => WP.mono (copy1_ok hp k si) fun _ h => h.1)
      (fun _ ⟨k, si⟩ => WP.mono (copy1_ok hp' k si) fun _ h => h.1)
  -- The call of `update`.
  have au : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s')
      (.block ([] ++ [.mov .eax (.imm 0), .mov .esi (.imm (BitVec.ofNat 32 H.B)),
        .mov .ecx (.imm (BitVec.ofNat 32 H.D))] ++ Impl.Hmac.Generic.X86.scr .edx H.buf))
      fun s s' => (KR (H := H) sc s₀ s ∧
          UpdArgs hH s .esi .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (BitVec.ofNat 32 H.B) H.D) ∧
        (KR (H := H) sc s₀' s' ∧
          UpdArgs hH s' .esi .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (BitVec.ofNat 32 H.B) H.D) :=
    rel_agree (τr [.esp, .ebp, .ebx, .edi]) (fun s s' k k' => agree_regs (kr_agree hq k k')) hc.upd
      (fun _ k => WP.mono (updArgs_ok hH hp k) fun _ ⟨k₁, a, _⟩ => ⟨k₁, a⟩)
      (fun _ k => WP.mono (updArgs_ok hH hp' k) fun _ ⟨k₁, a, _⟩ => ⟨k₁, by rw [← e0, ← eT, ← e5]; exact a⟩)
  have cu : RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧
          UpdArgs hH s .esi .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (BitVec.ofNat 32 H.B) H.D) ∧
        (KR (H := H) sc s₀' s' ∧
          UpdArgs hH s' .esi .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (BitVec.ofNat 32 H.B) H.D))
      (.frame (.push (upd6 .esi .ebx)) (.call H.updN H.updC) (.pop .eax (upd6 .esi .ebx).length))
      fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s' :=
    rel_wp (upd_rel hH (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ => ⟨a, a', k.esp, by rw [k'.esp, E, E, hq.esp]⟩)
      (fun _ ⟨k, a⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a⟩ => updCall_ok hH hp' k (by rw [e0, eT, e5]; exact a) fun _ k' _ _ => k')
  -- The second call of `finalize`.
  have a2 : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s')
      (.block ([] ++ H.count2 ++ Impl.Hmac.Generic.X86.scr .edx H.buf))
      fun s s' => (KR (H := H) sc s₀ s ∧
          FinArgs hH s .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (BitVec.ofNat 32 (H.B + H.D)) 0) ∧
        (KR (H := H) sc s₀' s' ∧
          FinArgs hH s' .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (BitVec.ofNat 32 (H.B + H.D)) 0) :=
    rel_agree (τr [.esp, .ebp, .ebx, .edi]) (fun s s' k k' => agree_regs (kr_agree hq k k')) hc.fin2
      (fun _ k => WP.mono (fin2Args_ok hH hp k) fun _ ⟨k₁, a, _⟩ => ⟨k₁, a⟩)
      (fun _ k => WP.mono (fin2Args_ok hH hp' k) fun _ ⟨k₁, a, _⟩ => ⟨k₁, by rw [← e0, ← eT, ← e5]; exact a⟩)
  have c2 : RelCT isa (fun s s' => (KR (H := H) sc s₀ s ∧
          FinArgs hH s .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (BitVec.ofNat 32 (H.B + H.D)) 0) ∧
        (KR (H := H) sc s₀' s' ∧
          FinArgs hH s' .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (BitVec.ofNat 32 (H.B + H.D)) 0))
      (.frame (.push (fin5 .ebx)) (.call H.finN H.finC) (.pop .eax (fin5 .ebx).length))
      fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s' :=
    rel_wp (fin_rel hH (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ => ⟨a, a', k.esp, by rw [k'.esp, E, E, hq.esp]⟩)
      (fun _ ⟨k, a⟩ => finCall_ok hH hp k a fun _ k' _ _ _ => k')
      (fun _ ⟨k, a⟩ => finCall_ok hH hp' k (by rw [e0, eT, e5]; exact a) fun _ k' _ _ _ => k')
  -- The copy of the MAC, and the end.
  have cp2 : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s') (copy .ebp H.buf .edi 0 H.D)
      fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s' :=
    rel_agree (τr [.esp, .ebp, .ebx, .edi]) (fun s s' k k' => agree_regs (kr_agree hq k k')) hc.copy2
      (fun _ k => WP.mono (copy2_ok hp k) fun _ h => h.1)
      (fun _ k => WP.mono (copy2_ok hp' k) fun _ h => h.1)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => KR (H := H) sc s₀ s ∧ KR (H := H) sc s₀' s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.ebp]) (fun _ _ h =>
      agree_regs (sub_regs (by decide) (kr_agree hq h.1 h.2))) hr
  exact pro.seq ((a1.seq c1).seq (cp1.seq ((au.seq cu).seq ((a2.seq c2).seq (cp2.seq restore)))))

end VG.Proof.Hmac.Generic.X86.Finalize

namespace VG.Proof.Hmac.Generic.X86.Finalize

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash)
open VG.Proof.Hmac.Generic.X86

/-- `finalize` is verified against `finG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.F ≤ 8 * sc) (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified X86.target H.finalize (finG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH sc hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2⟩ := hpub
    exact (ct hH hc (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `finalize` reads and writes, of those `finW` gives it. -/
def narrowRd (S : Nat) (s : State) : List Region := [⟨(arg s 1).setWidth 64, S⟩, ⟨argAddr s 0, 24⟩]
def narrowWr (S D sc : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 4).setWidth 64, D⟩, ⟨(arg s 5).setWidth 64, 8 * sc⟩]

/-- `finalize` is verified against `finW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.F ≤ 8 * sc) (hsat : ∃ s, (finW hH.SH sc).pre s) :
    Verified X86.target H.finalize (finW hH.SH sc) := by
  have pre : ∀ s, (finW hH.SH sc).pre s → (finG hH.SH sc).pre
      (s.withRegions (narrowRd hH.SH.stateBytes s) (narrowWr hH.SH.stateBytes hH.SH.digestBytes sc s)) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23⟩ := h
    simp only [finG, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, h22, h23⟩
  refine Verified.narrowTo (verified hH hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd hH.SH.stateBytes) (narrowWr hH.SH.stateBytes hH.SH.digestBytes sc) pre (fun s h => ?_)
    (fun s h => ?_) (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨h1, h2, _⟩ := h
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
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

end VG.Proof.Hmac.Generic.X86.Finalize
