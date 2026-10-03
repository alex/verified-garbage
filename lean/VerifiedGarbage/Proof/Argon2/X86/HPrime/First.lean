import VerifiedGarbage.Proof.Argon2.X86.HPrime.Output
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Body
import VerifiedGarbage.Proof.Argon2.X86.HPrime.CallsCT

/-!
# Argon2 H′ on x86 (32-bit): the first digest

`first_ok`: `first` leaves H(min(out_len, 64), LE32(out_len) ‖ input) at the
start of the digest, `scratch[768, 832)`. The input is read before anything
is written to the output, so the two may overlap.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (init update finalize absorbFixed chooseLength absorbInput finishInput
  first leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_movi wp_movm wp_cmpi)
open VG.Proof.Blake2.X86.CompressB (wp_addC wp_adcC)
open VG.Impl.Sha512.X86 (at_)

/-- Steps that keep memory, the permissions, `ebx`, `ebp` and `esp`. -/
theorem Keeps.same {B E : BitVec 32} {s t : State} (hb : t.gpr .ebx = s.gpr .ebx)
    (hp : t.gpr .ebp = s.gpr .ebp) (hs : t.gpr .esp = s.gpr .esp) (hm : t.mem = s.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Keeps B E s t :=
  ⟨hb, hp, hs, hrd, hwr, hm ▸ Frame.refl _ _⟩

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem arg_addr {i : Nat} (hi : i < 5) :
    addr (esp₀ s₀) (4 + 4 * i) = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_eq (by have := hp.esp_hi; omega)

theorem arg_sub {i : Nat} (hi : i < 5) : Region.Sub ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩ (argR s₀) := by
  show Region.Sub _ ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are kept in the body. -/
theorem Body.arg {s : State} (b : Body s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  have he := hp.esp_hi
  have hl := hp.esp_lo
  refine b.frame.readW (r := ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.arg_out.sub_left (arg_sub hp hi)
  · exact hp.arg_scr.sub_left (arg_sub hp hi)
  · show Region.Disjoint _ ⟨(esp₀ s₀ - BitVec.ofNat 32 60).setWidth 64, 60⟩
    rw [arg_addr hp hi, Taint.sub_setWidth hl]
    exact Offset.disjoint_below _ (by omega)

theorem Body.arg_in {s : State} (b : Body s₀ s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [b.rd, hp.rd], ?_⟩
  show Region.Contains ⟨addr (esp₀ s₀) (4 + 4 * 0), 20⟩ _ _
  rw [arg_addr hp hi, arg_addr hp (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

omit hp in
theorem Out.same {s t : State} {xs : List Byte} (h : Out s₀ s xs) (hm : t.mem = s.mem) : Out s₀ t xs :=
  ⟨by show _ = _; rw [hm]; exact h.ptr, by rw [hm]; exact h.left, by rw [hm]; exact h.bytes, h.len⟩

/-- `edx := min(out_len, 64)`. -/
theorem choose_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) :
    WP isa chooseLength s fun t => t.gpr .edx = BitVec.ofNat 32 (min (ol s₀) 64) ∧
      Keeps (scr s₀) (esp₀ s₀) s t := by
  have hs := hp.scr_fits
  have hol := (arg s₀ 3).isLt
  unfold chooseLength
  have rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ?_)
  have e₁ : s₁.gpr .edx = BitVec.ofNat 32 (ol s₀) := by rw [u₁.gpr, o.left]; rfl
  have k₂ : Keeps (scr s₀) (esp₀ s₀) s s₂ := Keeps.same
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
    (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd])
    (by rw [f₂.wr, u₁.wr])
  refine WP.ite (decide (ol s₀ < 65)) (by
      show s₂.cf = _
      rw [cf₂, e₁, Proof.Sha256.X86.Stream.toNat_ofNat_lt hol]; rfl)
    (fun h => WP.block_nil ⟨?_, k₂⟩) (fun h => wp_movi fun s₃ u₃ => WP.block_nil ⟨?_, ?_⟩)
  · have : ol s₀ ≤ 64 := by simp only [decide_eq_true_eq] at h; omega
    rw [f₂.gpr, e₁, Nat.min_eq_left this]
  · have : 64 ≤ ol s₀ := by simp only [decide_eq_false_iff_not] at h; omega
    rw [u₃.gpr, Nat.min_eq_right this]; rfl
  · exact k₂.trans (Keeps.same (u₃.other _ (by decide)) (u₃.other _ (by decide)) (u₃.other _ (by decide))
      u₃.mem u₃.rd u₃.wr)

end

/-! ## The steps of `first` -/

/-- The state before and between the steps of `first`: the body, no output
yet, `ebp` and the input kept. -/
structure F0 (s₀ s : State) : Prop where
  body : Body s₀ s
  out : Out s₀ s []
  ebp : s.gpr .ebp = s₀.gpr .ebp
  input : bytesAt s.mem ((inp s₀).setWidth 64) (inl s₀) = bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀)

/-- The length of the first digest. -/
abbrev nF (s₀ : State) : Nat := min (ol s₀) 64

/-- The input, on entry. -/
abbrev inB (s₀ : State) : List Byte := bytesAt s₀.mem ((inp s₀).setWidth 64) (inl s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem F0.keeps {s t : State} (h : F0 s₀ s) (k : Keeps (scr s₀) (esp₀ s₀) s t) : F0 s₀ t := by
  refine ⟨h.body.keeps hp k, h.out.keeps hp k, k.ebp.trans h.ebp, ?_⟩
  have hif := hp.in_fits
  have := k.bytes (R := inR s₀) (by simp; omega)
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in.symm
  simp only at this
  rw [this, h.input]

theorem nF_pos : 1 ≤ nF s₀ := by have := hp.ol_pos; simp only [nF]; omega

theorem first_choose {s : State} (h : F0 s₀ s) :
    WP isa chooseLength s fun t => F0 s₀ t ∧ t.gpr .edx = BitVec.ofNat 32 (nF s₀) :=
  (choose_ok hp h.body h.out).mono fun _ ⟨e, k⟩ => ⟨h.keeps hp k, e⟩

theorem first_init {s : State} (h : F0 s₀ s ∧ s.gpr .edx = BitVec.ofNat 32 (nF s₀)) :
    WP isa init s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) [] := by
  have c := h.1.body.ctx hp
  refine (init_ok c h.2 (nF_pos hp) (Nat.min_le_right _ _)).mono fun t ⟨r, cs, rd, wr, f⟩ => ⟨?_, r⟩
  refine h.1.keeps hp (Keeps.of_call (of_callee cs) rd wr f fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) c.lo⟩

theorem pfx_cov {s : State} (b : Body s₀ s) : Covers [⟨P s₀ + BitVec.ofNat 64 832, 4⟩] s.wr := by
  rw [b.wr, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, 832, rfl, by simp⟩

theorem first_fixed {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) []) :
    WP isa (absorbFixed 832 4) s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀)) := by
  have hs := hp.scr_fits
  refine (absorbFixed_ok (h.1.body.ctx hp) (offset := 832) (size := 4) (by omega) (by decide)
    (by decide) (pfx_cov hp h.1.body) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))) h.2).mono
    fun t ⟨r, k⟩ => ⟨h.1.keeps hp k, ?_⟩
  rw [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, h.1.body.pfx] at r
  exact r

/-- The instructions before `absorbInput`'s call of `update`. -/
theorem absorbInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .ecx (.imm 4), .mov .edx (.imm 0), .mov .esi (.mem (at_ .esp 4)),
      .mov .edi (.mem (at_ .esp 8))]) s fun t =>
      UpdateIn (scr s₀) (esp₀ s₀) (inp s₀) (inl s₀) 4 0 t ∧ Keeps (scr s₀) (esp₀ s₀) s t ∧ t.mem = s.mem := by
  have b := h.body
  refine wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ =>
    wp_movm (VG.Proof.Sha512.X86.ea_of (by rw [u₅.other _ (by decide), u₄.other _ (by decide), b.esp])
      4) (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact b.arg_in hp (i := 0) (by decide)) fun s₆ u₆ =>
    wp_movm (VG.Proof.Sha512.X86.ea_of (by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), b.esp]) 8)
      (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact b.arg_in hp (i := 1) (by decide)) fun s₇ u₇ =>
    WP.block_nil ?_
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have o₇ : ∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .edi → s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₇.other _ h4, u₆.other _ h3, u₅.other _ h2, u₄.other _ h1]
  have k₇ : Keeps (scr s₀) (esp₀ s₀) s s₇ := Keeps.same (o₇ _ (by decide) (by decide) (by decide) (by decide))
    (o₇ _ (by decide) (by decide) (by decide) (by decide)) (o₇ _ (by decide) (by decide) (by decide) (by decide))
    m₇ (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr])
  have b₇ := b.keeps hp k₇
  refine ⟨⟨b₇.ctx hp, ?_, ?_, ?_, ?_, ?_⟩, k₇, m₇⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem]; exact b.arg hp (i := 0) (by decide)
  · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, b.arg hp (i := 1) (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [b₇.rd, b₇.wr, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨inR s₀, by simp, 0, by simp, by simp⟩

theorem first_input {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀))) :
    WP isa absorbInput s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  have hil := (arg s₀ 1).isLt
  unfold absorbInput
  refine WP.seq ((absorbInput_blk hp h.1).mono fun s₇ ⟨⟨c₇, esi₇, edi₇, x₇, y₇, hDc⟩, k₇, m₇⟩ => ?_)
  have cnt₇ : s₇.gpr .edx ++ s₇.gpr .ecx = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀)).length := by
    rw [Proof.Argon2.le32_length, x₇, y₇]; rfl
  have F₇ := h.1.keeps hp k₇
  refine (update_ok c₇ (h0 := Spec.Blake2.init Spec.Blake2.b (nF s₀) 0) esi₇ edi₇ hif hDc
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in (by rw [m₇]; exact h.2) cnt₇
    (by rw [Proof.Argon2.le32_length]; omega)).mono fun s₈ ⟨r₈, cs₈, rd₈, wr₈, f₈⟩ => ?_
  rw [F₇.input] at r₈
  refine ⟨F₇.keeps hp (Keeps.of_call (of_callee cs₈) rd₈ wr₈ f₈ fun r hr => ?_), r₈⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- The count of the prefix and the input, as `finishInput` passes it. -/
abbrev cntLo (s₀ : State) : BitVec 32 := BitVec.ofNat 32 (inl s₀ + 4)
abbrev cntHi (s₀ : State) : BitVec 32 := BitVec.ofNat 32 ((inl s₀ + 4) / 2 ^ 32)

/-- The instructions before `finishInput`'s call of `finalize`. -/
theorem finishInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .ecx (.mem (at_ .esp 8)), .mov .edx (.imm 0), .alu .add .ecx (.imm 4),
      .alu .adc .edx (.imm 0)]) s fun t =>
      FinalizeIn (scr s₀) (esp₀ s₀) (cntLo s₀) (cntHi s₀) t ∧ Keeps (scr s₀) (esp₀ s₀) s t ∧
        t.mem = s.mem := by
  have hil := (arg s₀ 1).isLt
  have b := h.body
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.esp 8) (b.arg_in hp (i := 1) (by decide))
    fun s₉ u₉ => wp_movi fun s₁₀ u₁₀ => wp_addC fun s₁₁ u₁₁ cf₁₁ => wp_adcC cf₁₁ fun s₁₂ u₁₂ _ =>
    WP.block_nil ?_
  have m₁₂ : s₁₂.mem = s.mem := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have o₁₂ : ∀ r, r ≠ .ecx → r ≠ .edx → s₁₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₁₂.other _ h2, u₁₁.other _ h1, u₁₀.other _ h2, u₉.other _ h1]
  have k₁₂ : Keeps (scr s₀) (esp₀ s₀) s s₁₂ := Keeps.same (o₁₂ _ (by decide) (by decide))
    (o₁₂ _ (by decide) (by decide)) (o₁₂ _ (by decide) (by decide)) m₁₂
    (by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd]) (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr])
  have ecx₉ : s₉.gpr .ecx = BitVec.ofNat 32 (inl s₀) := by
    rw [u₉.gpr, b.arg hp (i := 1) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨⟨(b.keeps hp k₁₂).ctx hp, ?_, ?_⟩, k₁₂, m₁₂⟩
  · show _ = BitVec.ofNat 32 (inl s₀ + 4)
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), ecx₉, BitVec.ofNat_add]; rfl
  · show _ = BitVec.ofNat 32 ((inl s₀ + 4) / 2 ^ 32)
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₁₀.other _ (by decide), ecx₉]
    rw [← Proof.Blake2.X86.Stream.carry_ofNat (inl s₀) 4 (by decide), Nat.div_eq_of_lt hil]
    rfl

theorem first_finish {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) :
    WP isa finishInput s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  unfold finishInput
  refine WP.seq ((finishInput_blk hp h.1).mono fun s₁₂ ⟨⟨c₁₂, x₁₂, y₁₂⟩, k₁₂, m₁₂⟩ => ?_)
  have cnt : s₁₂.gpr .edx ++ s₁₂.gpr .ecx =
      BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀) ++ inB s₀).length := by
    rw [x₁₂, y₁₂, List.length_append, Proof.Argon2.le32_length]
    simp only [inB, bytesAt, List.length_map, List.length_range]
    apply BitVec.eq_of_toNat_eq
    rw [Proof.Blake2.X86.Stream.append_ofNat (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have F₁₂ := h.1.keeps hp k₁₂
  refine (finalize_ok c₁₂ (by rw [m₁₂]; exact h.2) cnt
    (by simp only [List.length_append, Proof.Argon2.le32_length, inB, bytesAt, List.length_map,
      List.length_range]; omega)).mono ?_
  rintro t ⟨d, cs, rd, wr, f⟩
  refine ⟨F₁₂.keeps hp (Keeps.of_call (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> exact cs _ (by decide) (by decide)) rd wr f fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show (bytesAt t.mem ((scr s₀).setWidth 64 + 768) 64).take _ = _
    rw [d, Proof.Argon2.H_stream]

/-- `first` hashes the length prefix and the input. -/
theorem first_ok {s : State} (h : F0 s₀ s) :
    WP isa first s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  unfold first
  exact WP.seq ((first_choose hp h).mono fun _ h₁ => WP.seq ((first_init hp h₁).mono fun _ h₂ =>
    WP.seq ((first_fixed hp h₂).mono fun _ h₃ => WP.seq ((first_input hp h₃).mono fun _ h₄ =>
      first_finish hp h₄))))

end

end VG.Proof.Argon2.X86.HPrime
