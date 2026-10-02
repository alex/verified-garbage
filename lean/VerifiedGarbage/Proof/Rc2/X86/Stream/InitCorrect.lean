import VerifiedGarbage.Proof.Rc2.X86.Stream.InitArgs
import VerifiedGarbage.Proof.Rc2.X86.KeyCorrect
import VerifiedGarbage.Proof.Rc2.X86.KeyLit
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` is correct

Untrusted: everything here is checked by Lean. The call of the verified key
expansion (`keyCall_ok`) and `init_correct`: the error code for invalid
lengths, and otherwise the context.
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

abbrev rs5 : List Reg := [.ebx, .esi, .edx, .ecx, .eax]

theorem key_nosp : NoSp Impl.Rc2.X86.expandKey := NoSp.of_all (by lit_decide)

theorem key_stack : stackUse Impl.Rc2.X86.expandKey = 0 := by decide

def callRd (s₀ s : State) : List Region := [keyR s₀, ⟨argAddr (pushed rs5 s).callEntry 0, 20⟩]
def callWr (s₀ : State) : List Region := [schR s₀, ⟨sA s₀, 512⟩]

theorem setWidth_append (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  have := b.isLt
  omega

/-- What the call of `vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)` needs. -/
theorem keyCallPre_ok {s₀ s : State} (hp : Pre s₀) (hk : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128)
    (he : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) (hc : Common s₀ s)
    (eax : s.gpr .eax = key s₀) (ecx : s.gpr .ecx = arg s₀ 1) (edx : s.gpr .edx = arg s₀ 2)
    (esi : s.gpr .esi = ctx s₀) (ebx : s.gpr .ebx = scr s₀) :
    VG.X86.CallPre keyContract rs5 (callRd s₀ s) (callWr s₀) s := by
  have hlo := hp.sp_lo
  have hEf := hp.sp_fit
  have hesp : s.gpr .esp = E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have a0 : arg (pushed rs5 s).callEntry 0 = key s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact eax
  have a1 : arg (pushed rs5 s).callEntry 1 = arg s₀ 1 := by rw [callEntry_arg fit hrs (by simp)]; exact ecx
  have a2 : arg (pushed rs5 s).callEntry 2 = arg s₀ 2 := by rw [callEntry_arg fit hrs (by simp)]; exact edx
  have a3 : arg (pushed rs5 s).callEntry 3 = ctx s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact esi
  have a4 : arg (pushed rs5 s).callEntry 4 = scr s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact ebx
  have eSp : (pushed rs5 s).callEntry.gpr .esp = E s₀ - BitVec.ofNat 32 24 := by
    rw [callEntry_esp', hesp]; rfl
  have eA : argAddr (pushed rs5 s).callEntry 0 = (E s₀ - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have kA' : Region.Sub ⟨(E s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩ (stkR s₀) := below_sub (by decide) hlo
  have kR : Region.Sub ⟨(E s₀ - BitVec.ofNat 32 24).setWidth 64, 4⟩ (stkR s₀) := by
    have := below_inner (sp := E s₀) (a := 4) (b := 24) (k := 20) (by omega) hlo
    rw [show E s₀ - BitVec.ofNat 32 24 = E s₀ - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have bS : Region.Sub ⟨sA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by decide)
  have wr : s.wr = [ctxR s₀, scR s₀] := hc.wr.trans hp.wr
  have rd : s.rd = [keyR s₀, ivR s₀, argR s₀] := hc.rd.trans hp.rd
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyContract, callRd, callWr, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, addr32]
    refine ⟨trivial, trivial, hp.k_c.sub_right sch_sub, hp.k_s.sub_right bS,
      (hp.c_s.sub_left sch_sub).sub_right bS, (hp.t_c.sub_left kA').sub_right sch_sub,
      (hp.t_s.sub_left kA').sub_right bS, (hp.t_c.sub_left kR).sub_right sch_sub,
      (hp.t_s.sub_left kR).sub_right bS, hp.k_fit, by have := hp.c_fit; omega,
      by have := hp.s_fit; omega, by rw [sub_toNat (by omega)]; omega, hk.1, hk.2, he.1, he.2⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [callRd, callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨keyR s₀, by simp [rd], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true (by simp)⟩
    · refine ⟨below (s.gpr .esp) (4 * rs5.length), by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero, callEntry_argAddr0]
    · exact ⟨ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

/-- The call of `vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)`. -/
theorem keyCall_ok {s₀ s : State} (hp : Pre s₀) (hk : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128)
    (he : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) (hc : Common s₀ s)
    (eax : s.gpr .eax = key s₀) (ecx : s.gpr .ecx = arg s₀ 1) (edx : s.gpr .edx = arg s₀ 2)
    (esi : s.gpr .esi = ctx s₀) (ebx : s.gpr .ebx = scr s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [schR s₀, ⟨sA s₀, 512⟩, stkR s₀] s.mem s'.mem →
      Spec.Rc2.scheduleAt s'.mem (cA s₀) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s₀.mem (kA s₀) (kl s₀)) (eb s₀) → Q s') :
    WP isa keyCall s Q := by
  have hlo := hp.sp_lo
  have hEf := hp.sp_fit
  have hesp : s.gpr .esp = E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have hesp : s.gpr .esp = E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have a0 : arg (pushed rs5 s).callEntry 0 = key s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact eax
  have a1 : arg (pushed rs5 s).callEntry 1 = arg s₀ 1 := by rw [callEntry_arg fit hrs (by simp)]; exact ecx
  have a2 : arg (pushed rs5 s).callEntry 2 = arg s₀ 2 := by rw [callEntry_arg fit hrs (by simp)]; exact edx
  have a3 : arg (pushed rs5 s).callEntry 3 = ctx s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact esi
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  refine WP.callWith (k := keyContract) key_body_correct key_nosp (by simp) hrs
    (by rw [key_stack, hesp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega)
    (keyCallPre_ok hp hk he hc eax ecx edx esi ebx) fun s' rd' wr' cs f ⟨s₂, m₂, post⟩ => ?_
  · have ce := callEntry_frame fit hrs
    have kE : Region.Sub (below (s.gpr .esp) (4 * rs5.length + 4)) (stkR s₀) := by
      rw [hesp]; exact fun _ h => h
    simp only [keyContract, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, m₂, addr32] at post
    rw [Proof.Rc2.bytesAt_frame ce _ _ (by omega) (sing ((hp.t_k.sub_left kE).symm)),
      Proof.Rc2.bytesAt_frame hc.frame _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.k_c.sub_right cv_sub
        · exact hp.k_s)] at post
    refine hQ s' rd' wr' cs (f.sub fun r hr => ?_) post
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨schR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨sA s₀, 512⟩, by simp, fun _ h => h⟩
    · refine ⟨stkR s₀, by simp, ?_⟩
      rw [key_stack, hesp]; exact fun _ h => h

theorem code_err {s₀ : State} (h : code s₀ ≠ 0) :
    code s₀ = (if ¬(1 ≤ kl s₀ ∧ kl s₀ ≤ 128) then 1 else if ¬(1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) then 2 else 3) ∧
      ¬((1 ≤ kl s₀ ∧ kl s₀ ≤ 128) ∧ (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) ∧ il s₀ = 8) := by
  unfold code at h ⊢
  by_cases h₁ : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128 <;> by_cases h₂ : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024 <;>
    by_cases h₃ : il s₀ = 8 <;> simp [h₁, h₂, h₃] at h ⊢

theorem code_ok {s₀ : State} (h : code s₀ = 0) :
    (1 ≤ kl s₀ ∧ kl s₀ ≤ 128) ∧ (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) ∧ il s₀ = 8 := by
  unfold code at h
  by_cases h₁ : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128 <;> by_cases h₂ : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024 <;>
    by_cases h₃ : il s₀ = 8 <;> simp [h₁, h₂, h₃] at h ⊢ <;> omega

theorem code_lt (s₀ : State) : code s₀ < 4 := by
  unfold code; split <;> [skip; split <;> [skip; split]] <;> decide

theorem init_correct (s₀ : State) (hs : initContract.pre s₀) :
    WP isa init s₀ (fun s' => abiPreserved s₀ s' ∧ initContract.post s₀ s') := by
  have hp := pre_of hs
  rw [init]
  refine WP.seq (checks_ok hp fun s c m a b e => ?_)
  refine WP.seq (wp_test fun s₁ f₁ hz => WP.block_nil ?_)
  have hz' : s₁.zf = some (decide (code s₀ = 0)) := by
    rw [hz, a, BitVec.and_self, ofNat_beq_zero (by have := code_lt s₀; omega)]
  have c₁ := c.fupd f₁
  refine WP.ite (!decide (code s₀ = 0)) (by show s₁.zf.map (!·) = _; rw [hz']; rfl)
    (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · -- Invalid lengths.
    have h0 : code s₀ ≠ 0 := of_decide_eq_false (by revert hb; cases decide (code s₀ = 0) <;> simp)
    obtain ⟨hcode, hbad⟩ := code_err h0
    refine ⟨⟨?_, by rw [f₁.mem, m]⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rw [f₁.gpr]
      exacts [b, e, c.edi, c.ebp, c.esp]
    · refine init_post_error (m := s₀.mem) (m' := s₁.mem) (key := kA s₀) (iv := ivA s₀) (ctx := cA s₀)
        (keyLen := kl s₀) (effectiveBits := eb s₀) (ivLen := il s₀) ?_ hbad
      rw [setWidth_append, f₁.gpr, a, toNat_ofNat_lt (by have := code_lt s₀; omega)]
      exact hcode
  · have h0 : code s₀ = 0 := of_decide_eq_true (by revert hb; cases decide (code s₀ = 0) <;> simp)
    obtain ⟨hk, he, hi⟩ := code_ok h0
    rw [initBody]
    refine WP.seq (initArgs_ok hp hi c₁ (by rw [f₁.mem, m]) (by rw [f₁.gpr]; exact b) (by rw [f₁.gpr]; exact e)
      fun t ct ea ec ed es eb' cv w₁ w₂ => ?_)
    refine WP.seq (keyCall_ok hp hk he ct ea ec ed es eb' fun s' rd' wr' cs f sch => ?_)
    have bS : Region.Sub ⟨sA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by decide)
    have sep3 {r : Region} (h₁ : r.Disjoint (schR s₀)) (h₂ : r.Disjoint ⟨sA s₀, 512⟩) (h₃ : r.Disjoint (stkR s₀)) :
        ∀ x ∈ [schR s₀, ⟨sA s₀, 512⟩, stkR s₀], r.Disjoint x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl)
      exacts [h₁, h₂, h₃]
    have word {d : Nat} (hd : 512 ≤ d) (hd' : d + 4 ≤ 576) :
        s'.mem.readW (addr (scr s₀) d) 32 = t.mem.readW (addr (scr s₀) d) 32 := by
      refine f.readW (Region.contains_self _ _) (sep3 ?_ ?_ ?_) (by decide)
      · exact (hp.c_s.sub_left sch_sub).symm.sub_left (hp.scr_sub hd')
      · rw [hp.scr_addr hd']; exact Offset.disjoint_base _ hd (by omega)
      · exact hp.t_s.symm.sub_left (hp.scr_sub hd')
    have scIn (d : Nat) (hd : d + 4 ≤ 576) : InRegions (s'.rd ++ s'.wr) (addr (scr s₀) d) 4 := by
      rw [wr', ct.wr, hp.wr, hp.scr_addr hd]
      exact ⟨scR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
    have ebx' : s'.gpr .ebx = scr s₀ := by rw [cs _ (by simp [calleeSaved])]; exact eb'
    simp only [restore, List.cons_append, List.nil_append]
    refine wp_ldm (o := 516) ebx' (scIn 516 (by decide)) fun s₂ u₂ => ?_
    refine wp_ldm (o := 512) (B := scr s₀) (by rw [u₂.other _ (by decide)]; exact ebx')
      (by rw [u₂.rd, u₂.wr]; exact scIn 512 (by decide)) fun s₃ u₃ => ?_
    refine wp_movi fun s₄ u₄ => WP.block_nil ?_
    have mem : s₄.mem = s'.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have g (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ebx) (h₃ : r ≠ .esi) (hr : r ∈ calleeSaved) :
        s₄.gpr r = t.gpr r := by
      rw [u₄.other _ h₁, u₃.other _ h₂, u₂.other _ h₃]
      exact cs r hr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, word (by decide) (by decide)]; exact w₁
      · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, word (by decide) (by decide)]; exact w₂
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.edi
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.ebp
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.esp
    · have retStk : (retR s₀).Disjoint (stkR s₀) := by
        show Region.Disjoint ⟨(E s₀).setWidth 64, 4⟩ ⟨(E s₀ - BitVec.ofNat 32 24).setWidth 64, 24⟩
        rw [Taint.sub_setWidth hp.sp_lo]; exact Offset.base_disjoint_below _ (by decide)
      rw [mem, f.readW (Region.contains_self _ _) (sep3 (hp.r_c.sub_right sch_sub) (hp.r_s.sub_right bS) retStk)
        (by decide)]
      refine ct.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.r_c.sub_right cv_sub
      · exact hp.r_s
    · refine init_post (m := s₀.mem) (m' := s₄.mem) (key := kA s₀) (iv := ivA s₀) (ctx := cA s₀)
        (keyLen := kl s₀) (effectiveBits := eb s₀) (ivLen := il s₀) hk he hi ?_ ?_ ?_
      · rw [setWidth_append, u₄.gpr]; rfl
      · rw [mem]; exact sch
      · show Spec.Rc2.blockAt s₄.mem (cA s₀ + BitVec.ofNat 64 128) = _
        rw [mem, Proof.Rc2.blockAt_frame f _ (sep3 sch_cv.symm ((hp.c_s.sub_left cv_sub).sub_right bS)
          (hp.t_c.sub_right cv_sub).symm)]
        exact cv

end VG.Proof.Rc2.X86.Stream.Init
