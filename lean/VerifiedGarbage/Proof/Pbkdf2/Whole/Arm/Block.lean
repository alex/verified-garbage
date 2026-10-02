import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Setup

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: a block of the output, up to `U₁`

Untrusted: everything here is checked by Lean. As on x86
(`Proof/Pbkdf2/Whole/X86/Block.lean`): after `k` blocks of the output
(`Inv`), `out` holds the first `done k` bytes of `T₁ ‖ … ‖ T_k`, `r4` is
`done k`, and `scratch` holds `INT (k + 1)`, byte-reversed. A step copies
the salted inner state into the working state, absorbs `INT (k + 1)` into
it (`update`) and computes `U₁` with HMAC's `finalize`.
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Hmac.Generic.Arm (Hash scrAt copy)
open VG.Proof.Hmac.Generic.Arm (HashOK cclob count)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_sub wp_cmp wp_rev wp_str op2_imm op2_reg)
open VG.Proof.Hmac.Generic.Common (bytes_keep)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

variable {F : Fns}

/-- The pseudorandom function: HMAC keyed with the password. -/
abbrev prf (hF : FnsOK F) (s₀ : State) : List Byte → List Byte := hmacBlockKey hF.hH.SH.H (K0 hF s₀)

/-- `T₁ ‖ … ‖ T_k`, `T_i`, the number of blocks and the bytes written after `k` of them. -/
abbrev Gk (hF : FnsOK F) (s₀ : State) (k : Nat) : List Byte := Whole.G (prf hF s₀) (saltB s₀) (cc s₀) k
abbrev Tk (hF : FnsOK F) (s₀ : State) (i : Nat) : List Byte := Whole.Tb (prf hF s₀) (saltB s₀) (cc s₀) i
abbrev nbk (F : Fns) (s₀ : State) : Nat := Whole.nb F.H.D (ol s₀)
abbrev dn (F : Fns) (s₀ : State) (k : Nat) : Nat := Whole.done F.H.D (ol s₀) k

/-- After `k` blocks of the output. -/
structure Inv (hF : FnsOK F) (s₀ : State) (k : Nat) (s : State) : Prop where
  kr : KR F s₀ s
  st : States hF s₀ s.mem
  k0l : (K0 hF s₀).length = F.H.B
  r4 : s.gpr .r4 = BitVec.ofNat 32 (dn F s₀ k)
  intW : s.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1))
  glen : (Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem (State.addr (out s₀)) (dn F s₀ k) = (Gk hF s₀ k).take (dn F s₀ k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := [.r4, .r5, .r6, .r11]

/-- Where a step writes, before it copies `T` out: the working space, or
the parts of `scratch` from the working state up to `INT (i)`. -/
def Wks (F : Fns) (s₀ : State) (r : Region) : Prop :=
  (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨ ∃ o n, r = sR s₀ o n ∧ F.stWO ≤ o ∧ o + n ≤ F.intO

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

omit hp in
theorem Wks.disj {r : Region} (h : Wks F s₀ r) :
    (svR F s₀).Disjoint r ∧ Region.Sub r (scR s₀ F) ∧ (sR s₀ F.st0O (3 * F.H.S)).Disjoint r ∧
      (sR s₀ F.intO 4).Disjoint r := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  rcases h with ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
  · exact ⟨sv_low hz hk, low_sub (by omega), (low_disj hz (by omega) (by omega)).symm,
      (low_disj hz (by omega) (by omega)).symm⟩
  · exact ⟨sv_disj hz (by omega) (by omega), part_sub (by omega),
      part_disj hz (Or.inl (by omega)) (by omega) (by omega), part_disj hz (Or.inr (by omega)) (by omega) (by omega)⟩

/-- `Inv` survives writes where a step writes, and to the stack below `sp`. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, Wks F s₀ r ∨ r = stkR s₀) : Inv hF s₀ k s' := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  have hsb : (stkR s₀).Disjoint (scR s₀ F) := hp.b_s
  refine ⟨h.kr.keep hrd hwr hsp (fun r hr => hg r (by simp only [List.mem_cons] at hr ⊢; tauto)) hf
    (fun r hr => ?_) (fun r hr => ?_), h.st.keep hz hf (fun r hr => ?_), h.k0l, by rw [hg _ (by simp), h.r4],
    ?_, h.glen, ?_⟩
  · rcases hw r hr with hw | rfl
    · exact (hw.disj hz).1
    · exact (hsb.sub_right (sv_sub hz)).symm
  · rcases hw r hr with hw | rfl
    · exact ⟨_, by simp, (hw.disj hz).2.1⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.1
    · exact (hsb.sub_right (part_sub (by omega))).symm
  · rw [← h.intW]
    refine hf.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rcases hw r hr with hw | rfl
    · exact (hw.disj hz).2.2.2
    · exact (hsb.sub_right (part_sub (by omega))).symm
  · rw [← h.outB]
    have osub : Region.Sub ⟨State.addr (out s₀), dn F s₀ k⟩ (outR s₀) :=
      Region.sub_prefix (Nat.min_le_right _ _)
    refine bytes_keep hf (fun r hr => ?_) (by
      have h1 : dn F s₀ k ≤ ol s₀ := Nat.min_le_right _ _; have := hp.no; omega)
    rcases hw r hr with hw | rfl
    · exact (hp.o_s.sub_left osub).sub_right (hw.disj hz).2.1
    · exact hp.b_o.symm.sub_left osub

theorem Inv.same {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : Inv hF s₀ k s' :=
  h.keep hp hz hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

theorem Inv.upd {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {d : Reg} (hd : d ∉ iregs) {v : BitVec 32}
    (u : Upd s s' d v) : Inv hF s₀ k s' :=
  h.same hp hz u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

theorem Inv.upd12 {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {d : Reg} (hd : d ∉ iregs) {v : BitVec 32}
    (u : Upd12 s s' d v) : Inv hF s₀ k s' :=
  h.same hp hz u.rd u.wr u.sp (fun r hr => u.other r (fun e => hd (e ▸ hr)) (by
    simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) u.mem

/-- After a call that writes where a step writes. -/
theorem Inv.after {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, Wks F s₀ r) : Inv hF s₀ k s' := by
  have f := ha.frame
  rw [h.kr.stkE] at f
  refine h.keep hp hz ha.rd ha.wr ha.sp (fun r hr => ha.cs r (by
    simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide) (by
    simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) f fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl (hw r hr)
  · simp only [List.mem_singleton] at hr; exact .inr hr

/-! ## The loop's start -/

omit hp hz in
theorem rev_eq (x : BitVec 32) : rev x = byteRev32 x := rfl

omit hz in
theorem addr_scr {s : State} (hk : KR F s₀ s) {o : Nat} (ho : o < F.L8) :
    State.addr (s.gpr .r11 + BitVec.ofNat 32 o) = A s₀ o := by
  rw [hk.r11]; exact dO_addr hp ho

omit hp hz in
theorem beq_zero (x : BitVec 32) : (x - 0 == 0) = decide (x.toNat = 0) := by
  have e : x - 0 = x := by apply BitVec.eq_of_toNat_eq; simp
  rw [e]
  rcases Decidable.em (x = 0) with h | h
  · subst h; rfl
  · have h' : x.toNat ≠ 0 := fun t => h (BitVec.eq_of_toNat_eq (by rw [t]; rfl))
    rw [decide_eq_false h']
    exact beq_eq_false_iff_ne.2 h

/-- `INT (1)`, no bytes written, and whether `out_len` is 0. -/
theorem loopInit_ok {s : State} (hk : KR F s₀ s) (hst : States hF s₀ s.mem) (hkl : (K0 hF s₀).length = F.H.B) :
    WP isa (.block F.loopInit) s fun t => Inv hF s₀ 0 t ∧ t.z = decide (ol s₀ = 0) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D; have := hz.reach
  unfold Fns.loopInit
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_rev fun s₂ u₂ => ?_
  have k₂ := (hk.upd (by decide) u₁).upd (by decide) u₂
  refine wp_str (a := A s₀ F.intO) (by omega) (addr_scr hp k₂ (by omega))
    (by rw [u₂.wr, u₁.wr]; exact in_sc hp hz hk.wr (by omega)) fun s₃ m₃ => ?_
  have f₃ : Frame [sR s₀ F.intO 4] s.mem s₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₃ : KR F s₀ s₃ := hk.write hz (by rw [m₃.rd, u₂.rd, u₁.rd]) (by rw [m₃.wr, u₂.wr, u₁.wr])
    (by rw [m₃.sp, u₂.sp, u₁.sp])
    (fun r hr => by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [m₃.gpr, u₂.other r (by rcases hr with rfl | rfl | rfl <;> decide),
        u₁.other r (by rcases hr with rfl | rfl | rfl <;> decide)])
    (by omega) (by omega) f₃
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_arg hp (k₃.upd (by decide) u₄) (i := 2) (by decide)
    fun s₅ u₅ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₆ f₆ z₆ => WP.block_nil ⟨⟨?_, ?_, hkl, ?_, ?_, by simp [Gk, Whole.G], ?_⟩, ?_⟩
  · exact ((k₃.upd (by decide) u₄).upd (by decide) u₅).same f₆.rd f₆.wr f₆.sp (fun r _ => by rw [f₆.gpr]) f₆.mem
  · rw [f₆.mem, u₅.mem, u₄.mem]
    exact hst.keep hz f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]; simp [dn, Whole.done]
  · rw [f₆.mem, u₅.mem, u₄.mem, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr]; rfl
  · simp [dn, Whole.done, bytesAt]
  · rw [z₆, u₅.gpr, beq_zero]

/-! ## A step: the working state, and `INT (i)` -/

/-- The salted inner state, copied into the working state. -/
theorem b1_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (copy .r11 F.stSO .r11 F.stWO F.H.S) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.reach
  refine WP.mono (copy_part_ok hp hz h.kr hz.S.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨kt, g, m⟩ => ⟨?_, ?_⟩
  · have f : Frame [sR s₀ F.stWO F.H.S] s.mem t.mem := by
      rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    exact h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (kt.sp.trans h.kr.sp.symm)
      (fun r hr => g r (by
        simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) h.st.stS
    rw [m]; exact copied_byte (by omega) i hi

omit hp hz in
theorem add_ofNat_eq (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    x + BitVec.ofNat 32 n = BitVec.ofNat 32 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := h
  omega

omit hz in
/-- The count of bytes absorbed, `B + salt_len + j`. -/
theorem count_salt {j : Nat} (hz : Sizes F) (hj : j ≤ 4) {s : State} (h2 : s.gpr .r2 = s₀.gpr .r3 + BitVec.ofNat 32 (F.H.B + j))
    (h3 : s.gpr .r3 = 0) : count s = BitVec.ofNat 64 (F.H.B + (sl s₀ + j)) := by
  have hsf := salt_fit hp hz
  have : sl s₀ = (s₀.gpr .r3).toNat := rfl
  simp only [count]
  rw [h3, h2, zero_append, add_ofNat_eq _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  congr 1; omega

/-- `update`'s arguments: the working state, `INT (i)`, and the bytes absorbed. -/
theorem b2_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.updArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .r0 = dO s₀ F.stWO ∧
      t.gpr .r1 = dO s₀ F.intO ∧ t.gpr .r7 = BitVec.ofNat 32 4 ∧ t.gpr .r10 = scr s₀ ∧
      count t = BitVec.ofNat 64 (F.H.B + (sl s₀ + 0)) ∧ t.mem = s.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.reach
  simp only [Fns.updArgs, List.append_assoc]
  refine scr_ok h.kr (by omega) fun s₁ u₁ => ?_
  have i₁ := h.upd12 hp hz (by decide) u₁
  refine scr_ok i₁.kr (by omega) fun s₂ u₂ => ?_
  have i₂ := i₁.upd12 hp hz (by decide) u₂
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_add (op2_imm hz.encB) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := (((i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz (by decide) u₅).upd hp hz
    (by decide) u₆
  refine ⟨i₆, ?_, ?_, ?_, ?_, count_salt hp hz (by decide) ?_ u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide) (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r11]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r6]; rfl
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b3_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = dO s₀ F.intO) (h7 : s.gpr .r7 = BitVec.ofNat 32 4) (h10 : s.gpr .r10 = scr s₀) :
    UpdL hF.hH s (dO s₀ F.stWO) (dO s₀ F.intO) (scr s₀) 4 := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hH.hWb
  have hk := h.kr
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have ei := dO_addr hp (o := F.intO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r7 := h7
      r10 := h10
      hlen := by decide
      sp16 := by rw [hk.sp]; have := hp.sp24; omega
      cd := by
        rw [ei]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.intO) (n := 4) (by omega)
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (by omega)
          · exact cov_low hp hk (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ei, ea]; exact part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      d_sc := by rw [ei]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      b_st := by rw [ea]; exact b16 hp hk (part_sub (by omega))
      b_d := by rw [ei]; exact b16 hp hk (part_sub (by omega))
      b_sc := b16 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

/-- `update` with `INT (k + 1)`. -/
theorem b3_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = dO s₀ F.intO) (h7 : s.gpr .r7 = BitVec.ofNat 32 4) (h10 : s.gpr .r10 = scr s₀)
    (hc : count s = BitVec.ofNat 64 (F.H.B + (sl s₀ + 0)))
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀)) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)) s
      fun t => Inv hF s₀ k t ∧
        hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have ei := dO_addr hp (o := F.intO) (by omega)
  refine upd_frame hF.hH (b3_args hp hz h h0 h1 h7 h10) fun s' a r => ⟨h.after hp hz (After.of_hmac a)
    fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], Nat.le_refl _, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := r _ (by rw [ea]; exact hr) (by
      rw [hc, List.length_append, xorPad_length, h.k0l, bytesAt_length]; rfl)
    rwa [ea, ei, Whole.bytes_rev_int h.intW] at this

/-! ## A step: `U₁` -/

omit hp hz in
theorem FnsOK.reprOK (hF : FnsOK F) : ReprOK hF.hH.SH := fun m m' p q msg hb =>
  hF.hH.repr m m' p q msg (fun i hi => hb i (by rw [hF.hH.hS]; exact hi))

/-- HMAC's `finalize`'s arguments. -/
theorem b4_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .r0 = dO s₀ F.stWO ∧
      t.gpr .r1 = dO s₀ F.st1O ∧ t.gpr .r10 = dO s₀ F.uO ∧ t.gpr .r12 = scr s₀ ∧
      count t = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4)) ∧ t.mem = s.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.reach
  simp only [Fns.finArgs, List.append_assoc]
  refine scr_ok h.kr (by omega) fun s₁ u₁ => ?_
  have i₁ := h.upd12 hp hz (by decide) u₁
  refine scr_ok i₁.kr (by omega) fun s₂ u₂ => ?_
  have i₂ := i₁.upd12 hp hz (by decide) u₂
  refine scr_ok i₂.kr (by omega) fun s₃ u₃ => ?_
  have i₃ := i₂.upd12 hp hz (by decide) u₃
  refine wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_add (op2_imm hz.encB4) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have i₆ := ((i₃.upd hp hz (by decide) u₄).upd hp hz (by decide) u₅).upd hp hz (by decide) u₆
  refine ⟨i₆, ?_, ?_, ?_, ?_, count_salt hp hz (by decide) ?_ u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.other _ (by decide) (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide) (by decide),
      u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r11]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide) (by decide),
      u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r6]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b5_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = dO s₀ F.st1O) (h10 : s.gpr .r10 = dO s₀ F.uO) (h12 : s.gpr .r12 = scr s₀) :
    HfArgs hF.hH.SH hF.Wf s (dO s₀ F.stWO) (dO s₀ F.st1O) (dO s₀ F.uO) (scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have ew := dO_addr hp (o := F.stWO) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r10 := h10
      r12 := h12
      sp := by rw [hk.sp]; exact hp.sp24
      cr := by
        rw [hS, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.st1O) (n := F.H.S) (by omega)
          exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hS, hD, ew, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (by omega)
          · exact cov_part hp hk (by omega)
          · exact cov_low hp hk (by omega)
      i_u := by rw [hS, ew, e1]; exact part_disj hz (Or.inr (by omega)) (by omega) (by omega)
      i_o := by rw [hS, hD, ew, eu]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_s := by rw [hS, ew]; exact (low_disj hz (by omega) (by omega)).symm
      u_o := by rw [hS, hD, e1, eu]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      u_s := by rw [hS, e1]; exact (low_disj hz (by omega) (by omega)).symm
      o_s := by rw [hD, eu]; exact (low_disj hz (by omega) (by omega)).symm
      b_i := by rw [hS, ew]; exact b24 hp hk (part_sub (by omega))
      b_u := by rw [hS, e1]; exact b24 hp hk (part_sub (by omega))
      b_o := by rw [hD, eu]; exact b24 hp hk (part_sub (by omega))
      b_s := b24 hp hk (low_sub (by omega))
      ni := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nu := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [hD, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

/-- HMAC's `finalize`: `U₁ = PRF (salt ‖ INT (k + 1))`. -/
theorem b5_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = dO s₀ F.st1O) (h10 : s.gpr .r10 = dO s₀ F.uO) (h12 : s.gpr .r12 = scr s₀)
    (hc : count s = BitVec.ofNat 64 (F.H.B + (sl s₀ + 4)))
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push [.r10, .r12]) (.call F.hfN F.hfC) (.pop .r12 8)) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have ew := dO_addr hp (o := F.stWO) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have hsf := salt_fit hp hz
  refine hf_frame (FnsOK.reprOK hF) (by rw [hS]; omega) hF.hf hF.hfSt (b5_args hp hz h h0 h1 h10 h12)
    fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [ew, hS], Nat.le_refl _, by omega⟩
    · exact .inr ⟨_, _, by rw [eu, hD], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := post (K0 hF s₀) (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) (by rw [h.k0l, hB])
      (by rw [h.k0l, List.length_append, bytesAt_length]; simp only [Spec.Pbkdf2.int, List.length_cons,
        List.length_nil]; omega)
      (by rw [ew, ← List.append_assoc]; exact hr)
      (by
        have e : s.gpr .r3 ++ s.gpr .r2 = count s := rfl
        rw [e, hc, List.length_append, bytesAt_length, hB]
        simp only [Spec.Pbkdf2.int, List.length_cons, List.length_nil])
      (by rw [e1]; exact h.st.st1)
    rwa [eu, hD] at this

end

end VG.Proof.Pbkdf2.Whole.Arm
