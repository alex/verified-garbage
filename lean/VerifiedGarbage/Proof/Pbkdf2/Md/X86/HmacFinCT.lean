import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `finalize`, constant time

As for HMAC's `init` (`HmacInitCT.lean`): the pieces between the calls are
checked by the taint analysis, the prologue and the arguments of the first
call, which read the arguments on the stack, with them public (`argTaint`);
the call of the streaming `finalize` is related by `fin_rel`, that of the
compression function by `cmp_rel`. Then `finalize` is verified against the
contract with the arguments read only (`finG`), and with them writable
(`finW`).
-/

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (HashOK finG finW argTaint ArgsOut agree_argTaint rel_agree rel_wp stk fin_rel
  FinArgs fin5)
open VG.Proof.Pbkdf2.Stream.X86.Finalize (Pre KR E inn outer op scr tO pre_of pro_ok fin1Args_ok finCall_ok
  stk_eq)

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 6)) (.block H.st.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (VG.Taint.check taint (argTaint [.ebp, .ebx, .edi] (4 + 4 * 6))
    (.block ([] ++ Impl.Pbkdf2.Stream.X86.Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.st.buf)) hc).isSome = true
  mid : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi, .esi]) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp, .ebx, .edi]) (.block H.finOut) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  esp : s₀.gpr .esp = s₀'.gpr .esp
  args : ∀ i < 6, arg s₀ i = arg s₀' i

variable {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
variable {s₀ s₀' : State} (hp : Pre (H := H.st) sc s₀) (hp' : Pre (H := H.st) sc s₀') (hq : PubEq s₀ s₀')

/-- The arguments lie outside the writable regions. -/
theorem args_out {t : State} (h : Pre (H := H.st) sc t) {s : State} (hsp : s.gpr .esp = E t) (hwr : s.wr = t.wr) :
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
theorem kr_agree {s s' : State} (h : KR (H := H.st) sc s₀ s) (h' : KR (H := H.st) sc s₀' s') :
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

include hO hc hp hp' hq

theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have hH := hO.hH
  have e5 : scr s₀' = scr s₀ := (hq.args 5 (by decide)).symm
  have e0 : inn s₀' = inn s₀ := (hq.args 0 (by decide)).symm
  have eT : tO (H := H.st) s₀' = tO (H := H.st) s₀ := by rw [tO, tO, e5]
  have e2 : arg s₀' 2 = arg s₀ 2 := (hq.args 2 (by decide)).symm
  have e3 : arg s₀' 3 = arg s₀ 3 := (hq.args 3 (by decide)).symm
  -- The prologue.
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.st.finPrologue)
      fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀') :=
    rel_agree (argTaint [] (4 + 4 * 6)) (fun s s' e e' => by
        subst e e'
        exact agree_argTaint (fun r hr => nomatch hr) hq.esp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          hq.args) hc.pro
      (fun _ e => by subst e; exact WP.mono (pro_ok hp) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ e => by subst e; exact WP.mono (pro_ok hp') fun _ h => ⟨h.1, h.2.1⟩)
  -- The call of the streaming `finalize`.
  have a1 : RelCT isa (fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀'))
      (.block ([] ++ Impl.Pbkdf2.Stream.X86.Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.st.buf))
      fun s s' => (KR (H := H.st) sc s₀ s ∧
          FinArgs hH s .ebx (inn s₀) (tO (H := H.st) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧
          FinArgs hH s' .ebx (inn s₀) (tO (H := H.st) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s'.gpr .esi = outer s₀') :=
    rel_agree (argTaint [.ebp, .ebx, .edi] (4 + 4 * 6)) (fun s s' ⟨k, _⟩ ⟨k', _⟩ =>
        agree_argTaint (sub_regs (by decide) (kr_agree hq k k')) (by rw [k.esp, k'.esp, E, E, hq.esp])
          (args_out hp k.esp k.wr) (args_out hp' k'.esp k'.wr)
          fun i hi => by rw [k.argEq hp hi, k'.argEq hp' hi, hq.args i hi]) hc.fin1
      (fun _ ⟨k, si⟩ => WP.mono (fin1Args_ok hH hp k) fun _ ⟨k₁, a, s₁, _⟩ => ⟨k₁, a, s₁.trans si⟩)
      (fun _ ⟨k, si⟩ => WP.mono (fin1Args_ok hH hp' k) fun _ ⟨k₁, a, s₁, _⟩ =>
        ⟨k₁, by rw [← e0, ← eT, ← e5, ← e2, ← e3]; exact a, s₁.trans si⟩)
  have c1 : RelCT isa (fun s s' => (KR (H := H.st) sc s₀ s ∧
        FinArgs hH s .ebx (inn s₀) (tO (H := H.st) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧
          FinArgs hH s' .ebx (inn s₀) (tO (H := H.st) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧ s'.gpr .esi = outer s₀'))
      (.frame (.push (fin5 .ebx)) (.call H.st.finN H.st.finC) (.pop .eax (fin5 .ebx).length))
      fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀') :=
    rel_wp (fin_rel hH (sp := E s₀) fun s s' ⟨⟨k, a, _⟩, ⟨k', a', _⟩⟩ =>
        ⟨a, a', k.esp, by rw [k'.esp, E, E, hq.esp]⟩)
      (fun _ ⟨k, a, si⟩ => finCall_ok hH hp k a fun _ k' si' _ _ => ⟨k', si'.trans si⟩)
      (fun _ ⟨k, a, si⟩ => finCall_ok hH hp' k (by rw [e0, eT, e5]; exact a)
        fun _ k' si' _ _ => ⟨k', si'.trans si⟩)
  -- The outer block.
  have mid : RelCT isa (fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .esi = outer s₀) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .esi = outer s₀')) (.block H.finMid)
      fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .eax = inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (τr [.esp, .ebp, .ebx, .edi, .esi]) (fun s s' ⟨k, si⟩ ⟨k', si'⟩ => agree_regs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · exact kr_agree hq k k' _ (by simp)
        · rw [si, si', outer, outer, hq.args 1 (by decide)]) hc.mid
      (fun _ ⟨k, si⟩ => WP.mono (mid_ok hO hp k si) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ ⟨k, si⟩ => WP.mono (mid_ok hO hp' k si) fun _ h => ⟨h.1, h.2.1⟩)
  -- The compression.
  have hB : 0 < H.B := by have := hO.sizes.B4; omega
  have cm : RelCT isa (fun s s' => (KR (H := H.st) sc s₀ s ∧ s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N) ∧
        (KR (H := H.st) sc s₀' s' ∧ s'.gpr .eax = inn s₀' + BitVec.ofNat 32 H.N)) H.cmp
      fun s s' => KR (H := H.st) sc s₀ s ∧ KR (H := H.st) sc s₀' s' :=
    rel_wp (cmp_rel hO.comp hB (sp := E s₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
        ⟨cmpArgs hO.sizes hp k a, by have := cmpArgs hO.sizes hp' k' a'; rwa [e0, e5] at this, k.esp,
          by rw [k'.esp, E, E, hq.esp]⟩)
      (fun _ ⟨k, a⟩ => cmpF_ok hO hp k a fun _ k' _ _ => k')
      (fun _ ⟨k, a⟩ => cmpF_ok hO hp' k a fun _ k' _ _ => k')
  -- The MAC, and the end.
  obtain ⟨_, ho⟩ := hc.out
  have out : RelCT isa (fun s s' => KR (H := H.st) sc s₀ s ∧ KR (H := H.st) sc s₀' s') (.block H.finOut)
      fun _ _ => True :=
    RelCT.taint (A := taint) (τr [.esp, .ebp, .ebx, .edi]) (fun _ _ h => agree_regs (kr_agree hq h.1 h.2)) ho
  exact pro.seq ((a1.seq c1).seq (mid.seq (cm.seq out)))

end VG.Proof.Pbkdf2.Md.X86.HmacFin

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (finG finW)
open VG.Proof.Pbkdf2.Stream.X86.Finalize (pre_of)

/-- `finalize` is verified against `finG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
    (hfit : H.st.buf + H.st.F ≤ 8 * sc) (hsat : ∃ s, (finG hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacFin (finG hO.hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hO (pre_of hO.hH sc hs hfit)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨h1, h2⟩ := hpub
    exact (ct hO hc (pre_of hO.hH sc h₁ hfit) (pre_of hO.hH sc h₂ hfit) ⟨h1, h2⟩
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- The regions `finalize` reads and writes, of those `finW` gives it. -/
def narrowRd (S : Nat) (s : State) : List Region := [⟨(arg s 1).setWidth 64, S⟩, ⟨argAddr s 0, 24⟩]
def narrowWr (S D sc : Nat) (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, S⟩, ⟨(arg s 4).setWidth 64, D⟩, ⟨(arg s 5).setWidth 64, 8 * sc⟩]

/-- `finalize` is verified against `finW`, which lets it write its arguments:
the code only reads them. -/
theorem verifiedW {H : Hash} (hO : MdOk H) {sc : Nat} (hc : Checks H)
    (hfit : H.st.buf + H.st.F ≤ 8 * sc) (hsat : ∃ s, (finW hO.hH.SH sc).pre s) :
    Verified X86.target H.hmacFin (finW hO.hH.SH sc) := by
  have pre : ∀ s, (finW hO.hH.SH sc).pre s → (finG hO.hH.SH sc).pre
      (s.withRegions (narrowRd hO.hH.SH.stateBytes s)
        (narrowWr hO.hH.SH.stateBytes hO.hH.SH.digestBytes sc s)) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23⟩ := h
    simp only [finG, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
      State.withRegions_rd, State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
      h21, h22, h23⟩
  refine Verified.narrowTo (verified hO hc hfit (hsat.elim fun s hs => ⟨_, pre s hs⟩))
    (narrowRd hO.hH.SH.stateBytes) (narrowWr hO.hH.SH.stateBytes hO.hH.SH.digestBytes sc) pre (fun s h => ?_)
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

end VG.Proof.Pbkdf2.Md.X86.HmacFin
