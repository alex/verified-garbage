import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.AbsorbCorrect
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Streaming AES-CMAC on x86-64: `vg_cmac_aes_absorb` is constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proof pins to values of the public arguments (`AMid₁`,
`AAfter₁`, `AMid₂`, `AAfter₂`), and each call of `vg_cmac_aes_update` is
constant time by its own proof (`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after (v : Ctr32Impl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ s₀ St D S L R s) :
    WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) s
      (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_call v _ h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₆.saved _ (by simp [calleeSaved]), h.rbp],
      by rw [h₆.saved _ (by simp [calleeSaved]), h.r13], by rw [h₆.saved _ (by simp [calleeSaved]), h.r14],
      by rw [h₆.saved _ (by simp [calleeSaved]), h.r15], by rw [h₆.saved _ (by simp [calleeSaved]), h.rsp],
      by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)) S R
    (nbOf (s₀.gpr .rdx).toNat L)
  rbx : s.gpr .rbx = St
  r12 : s.gpr .r12 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .rdx).toNat L)
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .rdx).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨rbx₆, rbp₆, r13₆, r14₆, r15₆, rsp₆, rd₆, wr₆⟩ := h
  rw [hc] at r13₆ r14₆
  refine WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega) r14₆) fun s₇ h₇ => ?_
  obtain ⟨r12₇, r8₇, rdi₇, rsi₇, rdx₇, rcx₇, r9₇, sv₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at r12₇ r8₇
  have k₇ (r : Reg) (hr : r ∈ calleeSaved) (a : r ≠ .r12) : s₇.gpr r = s.gpr r := sv₇ r hr a
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L), 16 * nbOf (s₀.gpr .rdx).toNat L⟩ ⟨D, L⟩ :=
    Offset.sub_base D (by omega)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)) (n := nbOf (s₀.gpr .rdx).toNat L)
    (by rw [rdi₇, rbx₆]) (by rw [rsi₇, rbp₆]) (by rw [rdx₇, rbx₆]) (by rw [rcx₇, r13₆]) r8₇
    (by rw [r9₇, r15₆]) (by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₆]) (by rw [rd₇, rd₆])
    (by rw [wr₇, wr₆]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide))) (hp.stk_d.sub_right dD)
    (by
      by_cases h0 : nbOf (s₀.gpr .rdx).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)).isLt; omega
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .rdx).toNat L, rfl, by simp; omega⟩,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), rbx₆], r12₇,
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), r13₆], by rw [k₇ _ (by simp [calleeSaved]) (by decide), r14₆],
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), r15₆],
    by rw [k₇ _ (by simp [calleeSaved]) (by decide), rsp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = St
  r12 : s.gpr .r12 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .rdx).toNat L)
  r13 : s.gpr .r13 = D + BitVec.ofNat 64 (fOf (s₀.gpr .rdx).toNat L)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (leftOf (s₀.gpr .rdx).toNat L)
  r15 : s.gpr .r15 = S

theorem call2_after (v : Ctr32Impl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ s₀ St D S L R s) :
    WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.X86_64.update v.callee)) s
      (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_call v _ h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved _ (by simp [calleeSaved]), h.rbx], by rw [h₈.saved _ (by simp [calleeSaved]), h.r12],
      by rw [h₈.saved _ (by simp [calleeSaved]), h.r13], by rw [h₈.saved _ (by simp [calleeSaved]), h.r14],
      by rw [h₈.saved _ (by simp [calleeSaved]), h.r15]⟩

theorem absorb_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : absorbX86_64.pre s₀) (h0' : absorbX86_64.pre s₀')
    (hq : absorbX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .rdi) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat := by
    rw [q2, q3, q5, q6, q7]; exact APre.of h0'
  generalize s₀.gpr .rdi = St at hp hp'
  generalize s₀.gpr .rcx = D at hp hp'
  generalize s₀.gpr .r9 = S at hp hp'
  generalize (s₀.gpr .r8).toNat = L at hp hp'
  generalize (s₀.gpr .rsi).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r13, .r14, .r15, .rsp]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .r12, .r13, .r14, .r15]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := AMid₁ s₀ St D S L R) (F₂ := AMid₁ s₀' St D S L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩
  have c₁ := (upd_rel v _ (P := fun a b => AMid₁ s₀ St D S L R a ∧ AMid₁ s₀' St D S L R b)
    fun a b h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h => ⟨call1_after v h.1, call1_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.rbp, h.2.rbp, q3]
      · rw [h.1.r13, h.2.r13, q4]
      · rw [h.1.r14, h.2.r14, q4]
      · rw [h.1.r15, h.2.r15]
      · rw [h.1.rsp, h.2.rsp, q1]) hB).wp
    (F₁ := AMid₂ s₀ St D S L R) (F₂ := AMid₂ s₀' St D S L R) fun a b h => ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (upd_rel v _ (P := fun a b => AMid₂ s₀ St D S L R a ∧ AMid₂ s₀' St D S L R b)
    fun a b h => ⟨_, _, _, _, _, _, h.1.args, by rw [q4]; exact h.2.args, by rw [h.1.rsp, h.2.rsp, q1]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after v h.1, call2_after v h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.rbx, h.2.rbx]
      · rw [h.1.r12, h.2.r12, q4]
      · rw [h.1.r13, h.2.r13, q4]
      · rw [h.1.r14, h.2.r14, q4]
      · rw [h.1.r15, h.2.r15]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct (v : Ctr32Impl) :
    ConstantTime isa absorbX86_64.pre absorbX86_64.pub (absorb v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86_64
