import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Setup

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: a block of the output, up to `U₁`

Untrusted: everything here is checked by Lean. After `k` blocks of the
output (`Inv`), `out` holds the first `done k` bytes of `T₁ ‖ … ‖ T_k`,
`ebx` is `done k`, and `scratch` holds `INT (k + 1)`, byte-reversed. A step
copies the salted inner state into the working state, absorbs `INT (k + 1)`
into it (`update`) and computes `U₁` with HMAC's `finalize`.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Hmac.Generic.X86 (Hash at_ copy)
open VG.Proof.Hmac.Generic.X86 (HashOK UpdArgs upd_frame cclob zero_append_ofNat)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_addi wp_store wp_bswap wp_test)
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
  ebx : s.gpr .ebx = BitVec.ofNat 32 (dn F s₀ k)
  intW : s.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1))
  glen : (Gk hF s₀ k).length = k * F.H.D
  outB : bytesAt s.mem ((out s₀).setWidth 64) (dn F s₀ k) = (Gk hF s₀ k).take (dn F s₀ k)

/-- The registers `Inv` fixes. -/
abbrev iregs : List Reg := [.esp, .ebp, .ebx]

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

/-- `Inv` survives writes where a step writes, and to the stack below `esp`. -/
theorem Inv.keep {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hw : ∀ r ∈ rs, Wks F s₀ r ∨ r = stkR s₀) : Inv hF s₀ k s' := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  have hsb : (stkR s₀).Disjoint (scR s₀ F) := hp.b_s
  refine ⟨h.kr.keep hrd hwr (fun r hr => hg r (by simp only [List.mem_cons] at hr ⊢; tauto)) hf
    (fun r hr => ?_) (fun r hr => ?_), h.st.keep hz hf (fun r hr => ?_), h.k0l, by rw [hg _ (by simp), h.ebx],
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
    have osub : Region.Sub ⟨(out s₀).setWidth 64, dn F s₀ k⟩ (outR s₀) :=
      Region.sub_prefix (Nat.min_le_right _ _)
    refine bytes_keep hf (fun r hr => ?_) (by
      have h1 : dn F s₀ k ≤ ol s₀ := Nat.min_le_right _ _; have := hp.no; omega)
    rcases hw r hr with hw | rfl
    · exact (hp.o_s.sub_left osub).sub_right (hw.disj hz).2.1
    · exact hp.b_o.symm.sub_left osub

theorem Inv.upd {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {d : Reg} (hd : d ∉ iregs) {v : BitVec 32}
    (u : Upd s s' d v) : Inv hF s₀ k s' :=
  h.keep hp hz u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

theorem Inv.same {k : Nat} {s s' : State} (h : Inv hF s₀ k s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ iregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : Inv hF s₀ k s' :=
  h.keep hp hz hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

/-- After a call that writes where a step writes. -/
theorem Inv.after {k : Nat} {s s' : State} (h : Inv hF s₀ k s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, Wks F s₀ r) : Inv hF s₀ k s' := by
  have f := ha.frame
  rw [h.kr.stkE] at f
  refine h.keep hp hz ha.rd ha.wr (fun r hr => ha.cs r (by simp only [List.mem_cons] at hr ⊢; simp [calleeSaved]; tauto))
    f fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact .inl (hw r hr)
  · simp only [List.mem_singleton] at hr; exact .inr hr

/-! ## The loop's start -/

omit hp hz in
theorem bswap_eq (x : BitVec 32) : bswap x = byteRev32 x := rfl

omit hz in
theorem ea_scr {s : State} (hk : KR F s₀ s) {o : Nat} (ho : o < F.L8) :
    s.ea (at_ .ebp o) = A s₀ o := by
  rw [show s.ea (at_ .ebp o) = (dO s₀ o).setWidth 64 by
    show (s.gpr .ebp + BitVec.ofNat 32 o).setWidth 64 = _; rw [hk.ebp]]
  exact dO_addr hp ho

/-- `INT (1)`, no bytes written, and whether `out_len` is 0. -/
theorem loopInit_ok {s : State} (hk : KR F s₀ s) (hst : States hF s₀ s.mem) (hkl : (K0 hF s₀).length = F.H.B) :
    WP isa (.block F.loopInit) s fun t => Inv hF s₀ 0 t ∧ t.zf = some (decide (ol s₀ = 0)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  unfold Fns.loopInit
  refine wp_movi fun s₁ u₁ => wp_bswap fun s₂ u₂ => ?_
  refine wp_store (a := A s₀ F.intO) (ea_scr hp ((hk.upd (by decide) u₁).upd (by decide) u₂) (by omega))
    (by rw [u₂.wr, u₁.wr]; exact in_sc hp hz hk.wr (by omega)) fun s₃ m₃ => ?_
  have f₃ : Frame [sR s₀ F.intO 4] s.mem s₃.mem := by
    rw [m₃.mem, u₂.mem, u₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₃ : KR F s₀ s₃ := hk.write hz (by rw [m₃.rd, u₂.rd, u₁.rd]) (by rw [m₃.wr, u₂.wr, u₁.wr])
    (fun r hr => by
      rw [m₃.gpr, u₂.other r (by simp only [List.mem_cons] at hr; rcases hr with rfl | rfl | h <;> simp_all),
        u₁.other r (by simp only [List.mem_cons] at hr; rcases hr with rfl | rfl | h <;> simp_all)])
    (by omega) (by omega) f₃
  refine wp_movi fun s₄ u₄ => wp_arg hp (k₃.upd (by decide) u₄) (by decide) fun s₅ u₅ => ?_
  refine wp_test fun s₆ f₆ z₆ => WP.block_nil ⟨⟨?_, ?_, hkl, ?_, ?_, by simp [Gk, Whole.G], ?_⟩, ?_⟩
  · exact ((k₃.upd (by decide) u₄).upd (by decide) u₅).same f₆.rd f₆.wr (fun r _ => by rw [f₆.gpr]) f₆.mem
  · rw [f₆.mem, u₅.mem, u₄.mem]
    exact hst.keep hz f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]; simp [dn, Whole.done]
  · rw [f₆.mem, u₅.mem, u₄.mem, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr]; rfl
  · simp [dn, Whole.done, bytesAt]
  · rw [z₆, u₅.gpr, Hmac.Generic.X86.test_z]

/-! ## A step: the working state, and `INT (i)` -/

/-- The salted inner state, copied into the working state. -/
theorem b1_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (copy .ebp F.stSO .ebp F.stWO F.H.S) s fun t => Inv hF s₀ k t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D
  refine WP.mono (copy_part_ok hp hz h.kr hz.S.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨kt, g, m⟩ => ⟨?_, ?_⟩
  · have f : Frame [sR s₀ F.stWO F.H.S] s.mem t.mem := by
      rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    exact h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (fun r hr => g r (by
      simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) h.st.stS
    rw [m]; exact copied_byte (by omega) i hi

/-- `update`'s arguments: the working state, `B + salt_len`, `INT (i)`. -/
theorem b2_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.updArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .edi = dO s₀ F.stWO ∧
      t.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B ∧ t.gpr .eax = 0 ∧ t.gpr .ecx = BitVec.ofNat 32 4 ∧
      t.gpr .edx = dO s₀ F.intO ∧ t.mem = s.mem := by
  simp only [Fns.updArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine wp_arg hp i₁.kr (by decide) fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_movi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have i₅ := (((i₁.upd hp hz (by decide) u₂).upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz
    (by decide) u₅
  rw [← List.append_nil (VG.Impl.Hmac.Generic.X86.scr .edx F.intO)]
  refine scr_ok i₅.kr fun s₆ u₆ => WP.block_nil ⟨i₅.upd hp hz (by decide) u₆, ?_, ?_, ?_, ?_, u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr]; rfl
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b3_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdi : s.gpr .edi = dO s₀ F.stWO)
    (hsi : s.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = BitVec.ofNat 32 4)
    (hdx : s.gpr .edx = dO s₀ F.intO) :
    UpdArgs hF.hH s .esi .edi (dO s₀ F.stWO) (dO s₀ F.intO) (scr s₀) (arg s₀ 3 + BitVec.ofNat 32 F.H.B) 4 := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have hk := h.kr
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have ei := dO_addr hp (o := F.intO) (by omega)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := by decide
      sp48 := by rw [hk.esp]; have := hp.sp76; omega
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
      b_st := by rw [ea]; exact b48 hp hk (part_sub (by omega))
      b_d := by rw [ei]; exact b48 hp hk (part_sub (by omega))
      b_sc := b48 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

/-- `update` with `INT (k + 1)`. -/
theorem b3_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdi : s.gpr .edi = dO s₀ F.stWO)
    (hsi : s.gpr .esi = arg s₀ 3 + BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = BitVec.ofNat 32 4)
    (hdx : s.gpr .edx = dO s₀ F.intO)
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀)) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => Inv hF s₀ k t ∧
        hF.hH.SH.Repr t.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stWO) (by omega)
  have ei := dO_addr hp (o := F.intO) (by omega)
  have hsf := salt_fit hp hz
  refine upd_frame hF.hH (b3_args hp hz h hdi hsi hax hcx hdx) fun s' a r => ⟨h.after hp hz (After.of_hmac (by
    rw [h.kr.esp]; exact hp.sp76) a) fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], Nat.le_refl _, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := r _ (by rw [ea]; exact hr) (by
      rw [List.length_append, xorPad_length, h.k0l, bytesAt_length,
        show arg s₀ 3 + BitVec.ofNat 32 F.H.B = BitVec.ofNat 32 (F.H.B + sl s₀) by
          rw [Nat.add_comm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        zero_append_ofNat (by omega)])
    rwa [ea, ei, Whole.bytes_rev_int h.intW] at this

/-! ## A step: `U₁` -/

omit hp hz in
theorem FnsOK.reprOK (hF : FnsOK F) : ReprOK hF.hH.SH := fun m m' p q msg hb =>
  hF.hH.repr m m' p q msg (fun i hi => hb i (by rw [hF.hH.hS]; exact hi))

omit hp hz in
theorem add_ofNat_eq (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    x + BitVec.ofNat 32 n = BitVec.ofNat 32 (x.toNat + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := h
  omega

/-- HMAC's `finalize`'s arguments. -/
theorem b4_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.finArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .edx = dO s₀ F.stWO ∧
      t.gpr .esi = dO s₀ F.st1O ∧ t.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4) ∧ t.gpr .ecx = 0 ∧
      t.gpr .edi = dO s₀ F.uO ∧ t.mem = s.mem := by
  simp only [Fns.finArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine scr_ok i₁.kr fun s₂ u₂ => ?_
  have i₂ := i₁.upd hp hz (by decide) u₂
  refine wp_arg hp i₂.kr (by decide) fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  have i₅ := ((i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄).upd hp hz (by decide) u₅
  rw [← List.append_nil (VG.Impl.Hmac.Generic.X86.scr .edi F.uO)]
  refine scr_ok i₅.kr fun s₆ u₆ => WP.block_nil ⟨i₅.upd hp hz (by decide) u₆, ?_, ?_, ?_, ?_, u₆.gpr, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]
  · rw [u₆.other _ (by decide), u₅.gpr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b5_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdx : s.gpr .edx = dO s₀ F.stWO)
    (hsi : s.gpr .esi = dO s₀ F.st1O) (hax : s.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4))
    (hcx : s.gpr .ecx = 0) (hdi : s.gpr .edi = dO s₀ F.uO) :
    HfArgs hF.hH.SH hF.Wf s (dO s₀ F.stWO) (dO s₀ F.st1O) (arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4)) 0
      (dO s₀ F.uO) (scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have ew := dO_addr hp (o := F.stWO) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  exact
    { edx := hdx
      esi := hsi
      eax := hax
      ecx := hcx
      edi := hdi
      ebp := hk.ebp
      sp := by rw [hk.esp]; exact hp.sp76
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
      b_i := by rw [hS, ew]; exact b76 hp hk (part_sub (by omega))
      b_u := by rw [hS, e1]; exact b76 hp hk (part_sub (by omega))
      b_o := by rw [hD, eu]; exact b76 hp hk (part_sub (by omega))
      b_s := b76 hp hk (low_sub (by omega))
      ni := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nu := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [hD, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

/-- HMAC's `finalize`: `U₁ = PRF (salt ‖ INT (k + 1))`. -/
theorem b5_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (hdx : s.gpr .edx = dO s₀ F.stWO)
    (hsi : s.gpr .esi = dO s₀ F.st1O) (hax : s.gpr .eax = arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4))
    (hcx : s.gpr .ecx = 0) (hdi : s.gpr .edi = dO s₀ F.uO)
    (hr : hF.hH.SH.Repr s.mem (A s₀ F.stWO) (xorPad (K0 hF s₀) ipad ++ saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push hf6) (.call F.hfN F.hfC) (.pop .eax hf6.length)) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWf; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have ew := dO_addr hp (o := F.stWO) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have hsf := salt_fit hp hz
  refine hf_frame (FnsOK.reprOK hF) (by rw [hS]; omega) hF.hf hF.hfSp hF.hfSU (b5_args hp hz h hdx hsi hax hcx hdi)
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
        rw [List.length_append, bytesAt_length, hB,
          show arg s₀ 3 + BitVec.ofNat 32 (F.H.B + 4) = BitVec.ofNat 32 (F.H.B + (sl s₀ + 4)) by
            rw [add_ofNat_eq _ (by have : sl s₀ = (arg s₀ 3).toNat := rfl; omega),
              show (arg s₀ 3).toNat + (F.H.B + 4) = F.H.B + (sl s₀ + 4) by
                have : sl s₀ = (arg s₀ 3).toNat := rfl; omega],
          zero_append_ofNat (by omega)]
        simp only [Spec.Pbkdf2.int, List.length_cons, List.length_nil])
      (by rw [e1]; exact h.st.st1)
    rwa [eu, hD] at this

end

end VG.Proof.Pbkdf2.Whole.X86
