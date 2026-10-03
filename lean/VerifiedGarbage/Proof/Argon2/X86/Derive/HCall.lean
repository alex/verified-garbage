import VerifiedGarbage.Proof.Argon2.X86.Derive.Initial

/-!
# Argon2 on x86 (32-bit): calls of H′ in the derivation

The derivation calls `vg_argon2_hprime` in a frame of its five arguments,
`hprime(r, eax, edi, ecx, edx)` with `r` the input's pointer (`ebp` for the
first blocks of a lane, `esi` for the tag), from the body (`Inv`).
`hcall_ok` runs one: its input lies in the memory matrix or the locals, its
output in the memory matrix or `out`, and `scratch` is its working space. The
call writes only the output, `scratch` and the 84 bytes below the locals.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

theorem hPrime_nosp : NoSp Impl.Argon2.X86.HPrime.code := NoSp.of_all (by lit_decide)
theorem hPrime_stack : stackUse Impl.Argon2.X86.HPrime.code = 60 := by lit_decide

/-- The bytes of a region a frame's regions miss are kept. -/
theorem bytes_keep {rs : List Region} {m m' : Mem} (f : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hR : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n :=
  Proof.Blake2.bytesAt_congr fun _ hi => f.bytes (R := ⟨p, n⟩) hd hR hi

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A range of the 84 bytes below the locals. -/
theorem in_call {x : BitVec 32} {n : Nat} (h₁ : (E s₀).toNat ≤ x.toNat + 84)
    (h₂ : x.toNat + n ≤ (E s₀).toNat) : Region.Sub ⟨x.setWidth 64, n⟩ (callR s₀) := by
  have hE := E_nat hp
  have := hp.esp_lo
  exact sub32 (by rw [sub_nat (by omega)]; omega) (by rw [sub_nat (by omega)]; omega)

theorem call_disj {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (callR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (call_stk hp)

theorem loc_call : (locR s₀).Disjoint (callR s₀) := by
  have hE := E_nat hp
  have := hp.esp_lo
  have := E_hi hp
  exact disj32 (.inr (by rw [sub_nat (by omega)]; omega)) (by omega) (by rw [sub_nat (by omega)]; omega)

theorem loc_sub_stk : Region.Sub (locR s₀) (stkR s₀) := by
  simpa using frame_stk hp (d := 0) (n := 144) (by decide)

theorem loc_disj' {R : Region} (hR : R ∈ [memR s₀, scrR s₀, outR s₀]) : (locR s₀).Disjoint R :=
  (hp.stk_all R (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR ⊢
    rcases hR with h | h | h <;> simp [h])).sub_left (loc_sub_stk hp)

/-- What H′ needs, from the body: `hprime(r, eax, edi, ecx, edx)`. -/
theorem hcall_pre {s : State} (h : Inv s₀ s) {r : Reg} (hr : r ≠ .esp)
    (hdx : s.gpr .edx = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, locR s₀], ∃ off, (s.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .eax).toNat ≤ R.len)
    (hinfit : (s.gpr r).toNat + (s.gpr .eax).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, (s.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .ecx).toNat ≤ R.len)
    (houtfit : (s.gpr .edi).toNat + (s.gpr .ecx).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .ecx).toNat) :
    CallPre HPrime.hPrimeX86 [.edx, .ecx, .edi, .eax, r]
      [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩, ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩]
      [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, scrR s₀] s := by
  have hE := E_nat hp
  have hlo := hp.esp_lo
  have hhi := E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  have nesp : Reg.esp ∉ [Reg.edx, .ecx, .edi, .eax, r] := by simp [Ne.symm hr]
  have fit : 4 * [Reg.edx, .ecx, .edi, .eax, r].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega
  have a0 := callEntry_arg fit nesp (i := 0) (by simp)
  have a1 := callEntry_arg fit nesp (i := 1) (by simp)
  have a2 := callEntry_arg fit nesp (i := 2) (by simp)
  have a3 := callEntry_arg fit nesp (i := 3) (by simp)
  have a4 := callEntry_arg fit nesp (i := 4) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3 a4
  rw [hdx] at a4
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact mem_mem hp
    · exact loc_mem s₀
  have outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact mem_mem hp
    · exact out_mem hp
  have cI : Covers [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  have cO : Covers [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  have scrW : scrR s₀ ∈ s.wr := by rw [h.wr]; exact scr_mem hp
  have I_scr : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sI
  have I_call : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sI
    · exact (loc_call hp).sub_left sI
  have O_scr : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  have O_call : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sO
    · exact (call_disj hp (R := outR s₀) (by simp)).symm.sub_left sO
  have S_call : (scrR s₀).Disjoint (callR s₀) := (call_disj hp (R := scrR s₀) (by simp)).symm
  -- The callee's stack, arguments and return address.
  have e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (E s₀).toNat - 20 := by rw [esp, sub_nat (by omega)]
  have e24 : (s.gpr .esp - BitVec.ofNat 32 24).toNat = (E s₀).toNat - 24 := by rw [esp, sub_nat (by omega)]
  have e84 : (s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 60).toNat = (E s₀).toNat - 84 := by
    rw [sub_nat (by omega), e24]; omega
  have cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have cS : Region.Sub (below (s.gpr .esp - BitVec.ofNat 32 24) 60) (callR s₀) :=
    in_call hp (by omega) (by omega)
  have a20 : argAddr (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := callEntry_argAddr0 _ _
  have ce : (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 :=
    callEntry_esp' _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [HPrime.hPrimeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, a0, a1, a2, a3, a4, a20, ce]
    refine ⟨trivial, trivial, I_scr, O_scr, ?_, ?_,
      ?_, ?_,
      I_call.symm.sub_left cS, O_call.symm.sub_left cS, S_call.symm.sub_left cS, hinfit, houtfit,
      by omega, by rw [sub_nat (by rw [esp]; omega), esp]; omega, by rw [sub_nat (by rw [esp]; omega), esp]; omega,
      hL⟩
    · exact O_call.symm.sub_left cA
    · exact S_call.symm.sub_left cA
    · exact O_call.symm.sub_left cR
    · exact S_call.symm.sub_left cR
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cI a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl (by simpa using hc))
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inr ⟨_, List.mem_append_right _ scrW, hc⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩
    · exact ⟨_, List.mem_cons_of_mem _ scrW, hc⟩

/-- A call of H′ from the body: `hprime(r, eax, edi, ecx, edx)`. -/
theorem hcall_ok {s : State} (h : Inv s₀ s) {r : Reg} (hr : r ≠ .esp)
    (hdx : s.gpr .edx = scrP s₀)
    (hin : ∃ R ∈ [memR s₀, locR s₀], ∃ off, (s.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .eax).toNat ≤ R.len)
    (hinfit : (s.gpr r).toNat + (s.gpr .eax).toNat ≤ 2 ^ 32)
    (hout : ∃ R ∈ [memR s₀, outR s₀], ∃ off, (s.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
      off + (s.gpr .ecx).toNat ≤ R.len)
    (houtfit : (s.gpr .edi).toNat + (s.gpr .ecx).toNat ≤ 2 ^ 32)
    (hL : 1 ≤ (s.gpr .ecx).toNat) {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ q ∈ calleeSaved, t.gpr q = s.gpr q) →
      Frame [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, scrR s₀, callR s₀] s.mem t.mem →
      bytesAt t.mem ((s.gpr .edi).setWidth 64) (s.gpr .ecx).toNat =
        Spec.Argon2.hPrime (s.gpr .ecx).toNat
          (bytesAt s.mem ((s.gpr r).setWidth 64) (s.gpr .eax).toNat) → Q t) :
    WP isa (.frame (.push [.edx, .ecx, .edi, .eax, r]) (.call Impl.Argon2.X86.Derive.hPrimeName
      Impl.Argon2.X86.HPrime.code) (.pop .eax 5)) s Q := by
  have hE := E_nat hp
  have hlo := hp.esp_lo
  have hhi := E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  have nesp : Reg.esp ∉ [Reg.edx, .ecx, .edi, .eax, r] := by simp [Ne.symm hr]
  have fit : 4 * [Reg.edx, .ecx, .edi, .eax, r].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega
  have a0 := callEntry_arg fit nesp (i := 0) (by simp)
  have a1 := callEntry_arg fit nesp (i := 1) (by simp)
  have a2 := callEntry_arg fit nesp (i := 2) (by simp)
  have a3 := callEntry_arg fit nesp (i := 3) (by simp)
  have a4 := callEntry_arg fit nesp (i := 4) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3 a4
  rw [hdx] at a4
  -- The input and the output.
  obtain ⟨RI, hRI, oI, bI, lI⟩ := hin
  obtain ⟨RO, hRO, oO, bO, lO⟩ := hout
  have sI : Region.Sub ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ RI := by
    rw [bI]; exact Offset.sub_base _ lI
  have sO : Region.Sub ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ RO := by
    rw [bO]; exact Offset.sub_base _ lO
  have inW : RI ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact mem_mem hp
    · exact loc_mem s₀
  have outW : RO ∈ s.wr := by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact mem_mem hp
    · exact out_mem hp
  have cI : Covers [⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RI, inW, oI, bI, lI⟩
  have cO : Covers [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RO, outW, oO, bO, lO⟩
  have scrW : scrR s₀ ∈ s.wr := by rw [h.wr]; exact scr_mem hp
  have I_scr : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact hp.mem_scr.sub_left sI
    · exact (loc_disj' hp (R := scrR s₀) (by simp)).sub_left sI
  have I_call : Region.Disjoint ⟨(s.gpr r).setWidth 64, (s.gpr .eax).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRI
    rcases hRI with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sI
    · exact (loc_call hp).sub_left sI
  have O_scr : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (scrR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact hp.mem_scr.sub_left sO
    · exact hp.scr_out.symm.sub_left sO
  have O_call : Region.Disjoint ⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩ (callR s₀) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sO
    · exact (call_disj hp (R := outR s₀) (by simp)).symm.sub_left sO
  have S_call : (scrR s₀).Disjoint (callR s₀) := (call_disj hp (R := scrR s₀) (by simp)).symm
  -- The callee's stack, arguments and return address.
  have e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (E s₀).toNat - 20 := by rw [esp, sub_nat (by omega)]
  have e24 : (s.gpr .esp - BitVec.ofNat 32 24).toNat = (E s₀).toNat - 24 := by rw [esp, sub_nat (by omega)]
  have e84 : (s.gpr .esp - BitVec.ofNat 32 24 - BitVec.ofNat 32 60).toNat = (E s₀).toNat - 84 := by
    rw [sub_nat (by omega), e24]; omega
  have cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have cS : Region.Sub (below (s.gpr .esp - BitVec.ofNat 32 24) 60) (callR s₀) :=
    in_call hp (by omega) (by omega)
  have a20 : argAddr (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := callEntry_argAddr0 _ _
  have ce : (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 :=
    callEntry_esp' _ _
  have pre := hcall_pre hp h hr hdx ⟨RI, hRI, oI, bI, lI⟩ hinfit ⟨RO, hRO, oO, bO, lO⟩ houtfit hL
  refine WP.callWith HPrime.hPrime_verified.1 hPrime_nosp (by simp) nesp
    (by rw [hPrime_stack, esp]; simp only [List.length_cons, List.length_nil]; omega) pre
    fun t rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  simp only [HPrime.hPrimeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3] at post
  have cB : Region.Sub (below (s.gpr .esp) 24) (callR s₀) := in_call hp (by rw [e24]; omega) (by rw [e24]; omega)
  have cf := callEntry_frame fit nesp
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at cf
  rw [hPrime_stack] at f'
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at f'
  have bk : bytesAt (pushed [Reg.edx, .ecx, .edi, .eax, r] s).callEntry.mem ((s.gpr r).setWidth 64)
      (s.gpr .eax).toNat = bytesAt s.mem ((s.gpr r).setWidth 64) (s.gpr .eax).toNat :=
    bytes_keep cf
    (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact I_call.sub_right cB)
    (Nat.le_of_lt (Nat.lt_trans (s.gpr .eax).isLt (by decide)))
  rw [m₂, bk] at post
  have f₁ : Frame [⟨(s.gpr .edi).setWidth 64, (s.gpr .ecx).toNat⟩, scrR s₀, callR s₀] s.mem t.mem :=
    f'.sub fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · refine ⟨callR s₀, by simp, ?_⟩
        rw [esp]
        exact fun _ h => h
  refine k t (h.step (cs' .esp (by decide)) (cs' .ebp (by decide)) rd' wr' (f₁.sub fun q hq => ?_)) cs' f₁ post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · refine ⟨RO, ?_, sO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRO
    rcases hRO with rfl | rfl <;> simp
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.X86.Derive
