import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbCorrect

/-!
# Streaming AES-CMAC on AArch64: `vg_cmac_aes_absorb` is constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proof pins to values of the public arguments (`AMid₁`,
`AAfter₁`, `AMid₂`, `AAfter₂`), and each call of `vg_cmac_aes_update` is
constant time by its own proof (`upd_rel`).
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.Stream.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.CmacAes.AArch64 (agree_of)

/-- What the first call leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem call1_after (v : Ctr32Impl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₁ s₀ St D S L R s) :
    WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.AArch64.update v.callee)) s
      (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_call v _ h.args) fun _ h₆ =>
    ⟨by rw [h₆.saved .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [h₆.saved .x20 (by simp [preserved]) (by decide), h.x20],
      by rw [h₆.saved .x21 (by simp [preserved]) (by decide), h.x21],
      by rw [h₆.saved .x22 (by simp [preserved]) (by decide), h.x22],
      by rw [h₆.saved .x23 (by simp [preserved]) (by decide), h.x23],
      by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd], by rw [h₆.wr, h.wr]⟩

/-- What `chain2` leaves, for the second call. -/
structure AMid₂ (s₀ : State) (St D S : Addr) (L R : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 64 272) (D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)) S R
    (nbOf (s₀.gpr .x2).toNat L)
  x19 : s.gpr .x19 = St
  x24 : s.gpr .x24 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .x2).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem chain2_mid {s₀ s : State} {St D S : Addr} {L R : Nat} (hp : APre s₀ St D S L R)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S L R) := by
  obtain ⟨c, hc⟩ : ∃ c, (s₀.gpr .x2).toNat = c := ⟨_, rfl⟩
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le c L
  have hsum := nb_le c L
  obtain ⟨x19₆, x20₆, x21₆, x22₆, x23₆, sp₆, rd₆, wr₆⟩ := h
  rw [hc] at x21₆ x22₆
  refine WP.mono (chain2_wp (x := leftOf c L) (by unfold leftOf; omega) x22₆) fun s₇ h₇ => ?_
  obtain ⟨x24₇, x4₇, x0₇, x1₇, x2₇, x3₇, x5₇, sv₇, sp₇, -, rd₇, wr₇⟩ := h₇
  have hnb : (if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16) = nbOf c L := rfl
  rw [hnb] at x24₇ x4₇
  have c272 : Region.Sub ⟨St + BitVec.ofNat 64 272, 16⟩ ⟨St, 304⟩ := Offset.sub_base St (by decide)
  subst hc
  have dD : Region.Sub ⟨D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L), 16 * nbOf (s₀.gpr .x2).toNat L⟩
      ⟨D, L⟩ := Offset.sub_base D (by omega)
  refine ⟨hp.uargs (s := s₇) (Dd := D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L))
    (n := nbOf (s₀.gpr .x2).toNat L)
    (by rw [x0₇, x19₆]) (by rw [x1₇, x20₆]) (by rw [x2₇, x19₆]) (by rw [x3₇, x21₆]) x4₇
    (by rw [x5₇, x23₆]) (by rw [rd₇, rd₆]) (by rw [wr₇, wr₆]) (by omega) ((hp.st_d.sub_left c272).symm.sub_left dD)
    ((hp.d_s.sub_left dD).sub_right (Region.sub_prefix (by decide)))
    (by
      by_cases h0 : nbOf (s₀.gpr .x2).toNat L = 0
      · rw [h0]; have := (D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)).isLt; omega
      · have := hp.wD; rw [toNat_add_lt D hp.wD (by omega)]; omega)
    ⟨⟨D, L⟩, by simp, fOf (s₀.gpr .x2).toNat L, rfl, by simp; omega⟩,
    by rw [sv₇ .x19 (by simp [preserved]) (by decide), x19₆], x24₇,
    by rw [sv₇ .x21 (by simp [preserved]) (by decide), x21₆],
    by rw [sv₇ .x22 (by simp [preserved]) (by decide), x22₆],
    by rw [sv₇ .x23 (by simp [preserved]) (by decide), x23₆], by rw [sp₇, sp₆]⟩

/-- What the second call leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : Addr) (L : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = St
  x24 : s.gpr .x24 = BitVec.ofNat 64 (16 * nbOf (s₀.gpr .x2).toNat L)
  x21 : s.gpr .x21 = D + BitVec.ofNat 64 (fOf (s₀.gpr .x2).toNat L)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (leftOf (s₀.gpr .x2).toNat L)
  x23 : s.gpr .x23 = S
  sp : s.sp = s₀.sp

theorem call2_after (v : Ctr32Impl) {s₀ s : State} {St D S : Addr} {L R : Nat}
    (h : AMid₂ s₀ St D S L R s) :
    WP isa (.call ("vg_cmac_aes_update" ++ v.suffix) (Impl.CmacAes.AArch64.update v.callee)) s
      (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_call v _ h.args) fun _ h₈ =>
    ⟨by rw [h₈.saved .x19 (by simp [preserved]) (by decide), h.x19],
      by rw [h₈.saved .x24 (by simp [preserved]) (by decide), h.x24],
      by rw [h₈.saved .x21 (by simp [preserved]) (by decide), h.x21],
      by rw [h₈.saved .x22 (by simp [preserved]) (by decide), h.x22],
      by rw [h₈.saved .x23 (by simp [preserved]) (by decide), h.x23], by rw [h₈.sp, h.sp]⟩

theorem absorb_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : absorbAArch64.pre s₀) (h0' : absorbAArch64.pre s₀')
    (hq : absorbAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee v.suffix) fun _ _ => True := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .x0) (s₀.gpr .x3) (s₀.gpr .x5) (s₀.gpr .x4).toNat (s₀.gpr .x1).toNat := by
    rw [q0, q1, q3, q4, q5]; exact APre.of h0'
  generalize s₀.gpr .x0 = St at hp hp'
  generalize s₀.gpr .x3 = D at hp hp'
  generalize s₀.gpr .x5 = S at hp hp'
  generalize (s₀.gpr .x4).toNat = L at hp hp'
  generalize (s₀.gpr .x1).toNat = R at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5]) absorbPre h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) chain2 h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x21, .x22, .x23, .x24]) absorbPost h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of q6 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) hA).wp
    (F₁ := AMid₁ s₀ St D S L R) (F₂ := AMid₁ s₀' St D S L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩
  have c₁ := (upd_rel v _ (P := fun a b => AMid₁ s₀ St D S L R a ∧ AMid₁ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q6]⟩).wp
    (F₁ := AAfter₁ s₀ St D S L) (F₂ := AAfter₁ s₀' St D S L) fun a b h => ⟨call1_after v h.1, call1_after v h.2⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => AAfter₁ s₀ St D S L a ∧ AAfter₁ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q6]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x20, h.2.x20, q1]
      · rw [h.1.x21, h.2.x21, q2]
      · rw [h.1.x22, h.2.x22, q2]
      · rw [h.1.x23, h.2.x23]) hB).wp
    (F₁ := AMid₂ s₀ St D S L R) (F₂ := AMid₂ s₀' St D S L R) fun a b h => ⟨chain2_mid hp h.1, chain2_mid hp' h.2⟩
  have c₂ := (upd_rel v _ (P := fun a b => AMid₂ s₀ St D S L R a ∧ AMid₂ s₀' St D S L R b)
    fun a b h => ⟨h.1.args, by rw [q2]; exact h.2.args, by rw [h.1.sp, h.2.sp, q6]⟩).wp
    (F₁ := AAfter₂ s₀ St D S L) (F₂ := AAfter₂ s₀' St D S L) fun a b h =>
      ⟨call2_after v h.1, call2_after v h.2⟩
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b) _
    (fun a b h => by
      refine agree_of (by rw [h.1.sp, h.2.sp, q6]) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.x19, h.2.x19]
      · rw [h.1.x21, h.2.x21, q2]
      · rw [h.1.x22, h.2.x22, q2]
      · rw [h.1.x23, h.2.x23]
      · rw [h.1.x24, h.2.x24, q2]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem absorb_ct (v : Ctr32Impl) :
    ConstantTime isa absorbAArch64.pre absorbAArch64.pub (absorb v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.AArch64
