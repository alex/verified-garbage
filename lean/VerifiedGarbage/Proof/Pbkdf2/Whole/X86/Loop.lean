import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Block

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the rest of a block, the loop, and `pbkdf2`

A step copies `U₁` into `T`, runs `iterate` for the rest of the chain, copies
as much of `T` as the output still needs (`copyR_ok`, a byte copy of a length
in a register), and moves on to the next block; after the last one, `out`
holds the derived key.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK cclob count_loop nm ea_at addr3 ofNat_succ32)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_add wp_addi wp_sub wp_subi wp_cmp wp_cmpi
  wp_store wp_bswap wp_movzx8 wp_store8 sub_beq sub_ofNat)
open VG.Proof.Hmac.Generic.Common (bytes_keep writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad hmacBlockKey)

/-! ## A byte copy of a length in a register -/

/-- After `k` bytes of a copy from `A` to `B`. -/
structure CopyRInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r ∉ cclob, t.gpr r = s.gpr r
  ecx : t.gpr .ecx = BitVec.ofNat 32 k
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

/-- The loop copying `n = esi > 0` bytes from `[ebp + so]` to `[edi]`, with
`ecx` the index. -/
theorem copyR_ok {so n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 32) {s : State} (hsi : s.gpr .esi = BitVec.ofNat 32 n)
    (hcx : s.gpr .ecx = 0)
    (hsw : (s.gpr .ebp).toNat + so + n ≤ 2 ^ 32) (hdw : (s.gpr .edi).toNat + n ≤ 2 ^ 32)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨(s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so, n⟩ ⟨(s.gpr .edi).setWidth 64, n⟩) :
    WP isa (.loop (.block [.mov .eax (.reg .ebp), .alu .add .eax (.reg .ecx), .movzx8 .edx (at_ .eax so),
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store8 (at_ .eax 0) .dl,
      .alu .add .ecx (.imm 1), .alu .cmp .ecx (.reg .esi)]) .ne) s
      (CopyRInv s ((s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so) ((s.gpr .edi).setWidth 64) n) := by
  generalize eA : (s.gpr .ebp).setWidth 64 + BitVec.ofNat 64 so = A at hin hsep ⊢
  generalize eB : (s.gpr .edi).setWidth 64 = B at hout hsep ⊢
  have i0 : CopyRInv s A B 0 s :=
    ⟨rfl, rfl, fun _ _ => rfl, hcx, by rw [bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine count_loop hn (CopyRInv s A B) (fun k hk t h => ?_) i0
  have gb := h.other .ebp (by decide)
  have gd := h.other .edi (by decide)
  have gs := h.other .esi (by decide)
  refine wp_mov fun t₁ u₁ => wp_add fun t₂ u₂ => ?_
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k)
    (by rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), gb, h.ecx, addr3 (by omega), eA])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hin k hk) fun t₃ u₃ => ?_
  refine wp_mov fun t₄ u₄ => wp_add fun t₅ u₅ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_at, u₅.gpr, u₄.gpr, u₄.other .ecx (by decide), u₃.other .ecx (by decide), u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gd, h.ecx,
      addr3 (by omega), eB]
        exact congrArg (· + BitVec.ofNat 64 k) (BitVec.add_zero _))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₆ m₆ => ?_
  refine wp_addi fun t₇ u₇ => wp_cmp fun t₈ f₈ _ z₈ => WP.block_nil ?_
  have h7 : t₇.gpr .ecx = BitVec.ofNat 32 (k + 1) := by
    rw [u₇.gpr, m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.ecx, ofNat_succ32]
  refine ⟨⟨by rw [f₈.rd, u₇.rd, m₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [f₈.wr, u₇.wr, m₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r hr => by
      rw [f₈.gpr, u₇.other r (nm hr .ecx), m₆.gpr, u₅.other r (nm hr .eax), u₄.other r (nm hr .eax),
        u₃.other r (nm hr .edx), u₂.other r (nm hr .eax), u₁.other r (nm hr .eax), h.other r hr],
    by rw [f₈.gpr, h7], ?_⟩, ?_⟩
  · have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
    have v : (t₅.gpr .edx).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, h.mem]
      simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega), ↓reduceIte]
      ext i hi; simp
    have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k))
      (by rw [hl]; omega)
    rw [hl] at e'
    rw [f₈.mem, u₇.mem, m₆.mem, show Reg8.dl.reg = .edx from rfl, v, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem,
      h.mem, bytesAt_snoc', e']
  · rw [z₈, h7, u₇.other _ (by decide), m₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), gs, hsi, sub_beq (by omega) hn']

variable {F : Fns}

section
variable {hF : FnsOK F} {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-! ## A step: `T`, from `U₁` and `iterate` -/

/-- `T ← U₁`. -/
theorem b6_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) {u : List Byte} (hu : bytesAt s.mem (A s₀ F.uO) F.H.D = u) :
    WP isa (copy .ebp F.uO .ebp F.tO F.H.D) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.uO) F.H.D = u ∧ bytesAt t.mem (A s₀ F.tO) F.H.D = u := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D
  refine WP.mono (copy_part_ok hp hz h.kr hz.D.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨kt, g, m⟩ => ?_
  have f : Frame [sR s₀ F.tO F.H.D] s.mem t.mem := by
    rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨h.keep hp hz (kt.rd.trans h.kr.rd.symm) (kt.wr.trans h.kr.wr.symm) (fun r hr => g r (by
      simp only [iregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      f fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inl (.inr ⟨_, _, rfl, by omega, by omega⟩), ?_, ?_⟩
  · rw [bytes_keep f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega))
      (by omega)]
    exact hu
  · rw [m, Hmac.Generic.Common.bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    exact hu

/-- `iterate`'s arguments: the key's states, `U`, `c - 1` and `T`. -/
theorem b7_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) :
    WP isa (.block F.iterArgs) s fun t => Inv hF s₀ k t ∧ t.gpr .esi = dO s₀ F.st0O ∧
      t.gpr .eax = dO s₀ F.uO ∧ t.gpr .ecx = arg s₀ 4 - 1 ∧ t.gpr .edx = dO s₀ F.tO ∧ t.mem = s.mem := by
  simp only [Fns.iterArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have i₁ := h.upd hp hz (by decide) u₁
  refine scr_ok i₁.kr fun s₂ u₂ => ?_
  have i₂ := i₁.upd hp hz (by decide) u₂
  refine wp_arg hp i₂.kr (by decide) fun s₃ u₃ => wp_subi fun s₄ u₄ _ => ?_
  have i₄ := (i₂.upd hp hz (by decide) u₃).upd hp hz (by decide) u₄
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .edx F.tO)]
  refine scr_ok i₄.kr fun s₅ u₅ => WP.block_nil ⟨i₄.upd hp hz (by decide) u₅, ?_, ?_, ?_, u₅.gpr, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem b8_args {k : Nat} {s : State} (h : Inv hF s₀ k s) (hsi : s.gpr .esi = dO s₀ F.st0O)
    (hax : s.gpr .eax = dO s₀ F.uO) (hcx : s.gpr .ecx = arg s₀ 4 - 1) (hdx : s.gpr .edx = dO s₀ F.tO) :
    ItArgs hF.hH.SH hF.Wt s (dO s₀ F.st0O) (dO s₀ F.uO) (arg s₀ 4 - 1) (dO s₀ F.tO) (scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD
  have hk := h.kr
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have et := dO_addr hp (o := F.tO) (by omega)
  exact
    { esi := hsi
      eax := hax
      ecx := hcx
      edx := hdx
      ebp := hk.ebp
      sp := by rw [hk.esp]; exact hp.sp76
      cr := by
        rw [hS, hD, e0, eu]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.st0O) (n := 2 * F.H.S) (by omega)
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
          · obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.uO) (n := F.H.D) (by omega)
            exact ⟨r', List.mem_append_right _ hr', off, e, l⟩
      cw := by
        rw [hD, et]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (by omega)
          · exact cov_low hp hk (by omega)
      k_t := by rw [hS, hD, e0, et]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      k_s := by rw [hS, e0]; exact (low_disj hz (by omega) (by omega)).symm
      u_t := by rw [hD, eu, et]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      u_s := by rw [hD, eu]; exact (low_disj hz (by omega) (by omega)).symm
      t_s := by rw [hD, et]; exact (low_disj hz (by omega) (by omega)).symm
      b_k := by rw [hS, e0]; exact b76 hp hk (part_sub (by omega))
      b_u := by rw [hD, eu]; exact b76 hp hk (part_sub (by omega))
      b_t := by rw [hD, et]; exact b76 hp hk (part_sub (by omega))
      b_s := b76 hp hk (low_sub (by omega))
      nk := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nu := by rw [hD, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nt := by rw [hD, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nsc := by have := hp.nsc; omega }

/-- `iterate`: `T_{k + 1}`. -/
theorem b8_ok {k : Nat} {s : State} (h : Inv hF s₀ k s) (hsi : s.gpr .esi = dO s₀ F.st0O)
    (hax : s.gpr .eax = dO s₀ F.uO) (hcx : s.gpr .ecx = arg s₀ 4 - 1) (hdx : s.gpr .edx = dO s₀ F.tO)
    (hu : bytesAt s.mem (A s₀ F.uO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1)))
    (ht : bytesAt s.mem (A s₀ F.tO) F.H.D = prf hF s₀ (saltB s₀ ++ Spec.Pbkdf2.int (k + 1))) :
    WP isa (.frame (.push it5) (.call F.itN F.itC) (.pop .eax it5.length)) s fun t => Inv hF s₀ k t ∧
      bytesAt t.mem (A s₀ F.tO) F.H.D = Tk hF s₀ (k + 1) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWt; have hS := hF.hH.hS; have hD := hF.hH.hD; have hB := hF.hH.hB
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have eu := dO_addr hp (o := F.uO) (by omega)
  have et := dO_addr hp (o := F.tO) (by omega)
  refine it_frame (FnsOK.reprOK hF) (by rw [hS]; omega) (by rw [hD]; omega) hF.it hF.itSp hF.itSU
    (b8_args hp hz h hsi hax hcx hdx) fun s' a post => ⟨h.after hp hz a fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [et, hD], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · have := post (K0 hF s₀) (by rw [h.k0l, hB]) (by rw [e0]; exact h.st.st0)
      (by rw [e0, hS, Hmac.Generic.Common.add_ofNat_add]; exact h.st.st1)
    rw [et, hD, eu, hu, ht] at this
    rw [this]
    have hc := hp.c0
    rw [show (arg s₀ 4 - 1).toNat = cc s₀ - 1 by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 1 ≤ (arg s₀ 4).toNat; exact hc)]; rfl]
    rfl

/-! ## A step: copying `T` out -/

omit hp hz in
theorem arg_ofNat (i : Nat) : arg s₀ i = BitVec.ofNat 32 (arg s₀ i).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The bytes of `T` the output still needs. -/
theorem outLen_ok {k : Nat} (hk : k * F.H.D < ol s₀) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.outLen s fun t => Inv hF s₀ k t ∧
      t.gpr .ecx = BitVec.ofNat 32 (min (ol s₀ - k * F.H.D) F.H.D) ∧ t.mem = s.mem := by
  have hD := hz.D; have hol : ol s₀ < 2 ^ 32 := (arg s₀ 6).isLt
  have hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  unfold Fns.outLen
  refine WP.seq (wp_arg hp h.kr (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_cmpi fun s₃ f₃ c₃ _ =>
    WP.block_nil ?_)
  have i₃ := ((h.upd hp hz (by decide) u₁).upd hp hz (by decide) u₂).same hp hz f₃.rd f₃.wr
    (fun r _ => by rw [f₃.gpr]) f₃.mem
  have e₃ : s₃.gpr .ecx = BitVec.ofNat 32 (ol s₀ - k * F.H.D) := by
    rw [f₃.gpr, u₂.gpr, u₁.gpr, u₁.other _ (by decide), h.ebx, hdn, arg_ofNat 6,
      sub_ofNat (by have : ol s₀ = (arg s₀ 6).toNat := rfl; omega)]
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have cf : s₃.cf = some (decide (ol s₀ - k * F.H.D < F.H.D)) := by
    rw [c₃, ← f₃.gpr, e₃, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega)]
  refine WP.ite (decide (ol s₀ - k * F.H.D < F.H.D)) (by show s₃.cf = _; rw [cf]) (fun hT => WP.block_nil ?_)
    fun hF' => wp_movi fun s₄ u₄ => WP.block_nil ⟨i₃.upd hp hz (by decide) u₄, ?_, by rw [u₄.mem, m₃]⟩
  · have : ol s₀ - k * F.H.D < F.H.D := of_decide_eq_true hT
    exact ⟨i₃, by rw [e₃, Nat.min_eq_left (Nat.le_of_lt this)], m₃⟩
  · have : ¬ ol s₀ - k * F.H.D < F.H.D := of_decide_eq_false hF'
    rw [u₄.gpr, Nat.min_eq_right (by omega)]

/-- Copying `n` bytes of `T` to `out` after the `k D` written. -/
theorem outLoop_ok {k n : Nat} (hn : 0 < n) (hkn : k * F.H.D + n ≤ ol s₀) (hnD : n ≤ F.H.D) {s : State}
    (h : Inv hF s₀ k s) (hcx : s.gpr .ecx = BitVec.ofNat 32 n) (hkD : k * F.H.D < ol s₀) :
    WP isa F.outLoop s fun t => KR F s₀ t ∧ t.gpr .ebx = s.gpr .ebx ∧ t.gpr .esi = BitVec.ofNat 32 n ∧
      t.mem = writeBytes s.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D))
        (bytesAt s.mem (A s₀ F.tO) n) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have hD := hz.D
  have hol : ol s₀ < 2 ^ 32 := (arg s₀ 6).isLt
  have hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  have hno := hp.no
  have eO : (out s₀ + BitVec.ofNat 32 (k * F.H.D)).setWidth 64 = (out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D) :=
    Pbkdf2.Stream.X86.setWidth_add (by have : ol s₀ = (arg s₀ 6).toNat := rfl; omega)
  have tO' : (out s₀ + BitVec.ofNat 32 (k * F.H.D)).toNat = (out s₀).toNat + k * F.H.D :=
    Pbkdf2.Stream.X86.toNat_add_ofNat (by have : ol s₀ = (arg s₀ 6).toNat := rfl; omega)
  have osub : Region.Sub ⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) :=
    Offset.sub_base _ hkn
  unfold Fns.outLoop
  refine WP.seq (wp_mov fun s₁ u₁ => wp_arg hp (h.kr.upd (by decide) u₁) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ =>
    wp_movi fun s₄ u₄ => WP.block_nil ?_)
  have k₄ := (((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  have e₄si : s₄.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hcx]
  have e₄di : s₄.gpr .edi = out s₀ + BitVec.ofNat 32 (k * F.H.D) := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ebx, hdn]
  have e₄bx : s₄.gpr .ebx = s.gpr .ebx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hL := L8_le hz; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copyR_ok (so := F.tO) hn (by omega) e₄si u₄.gpr
    (by rw [k₄.ebp]; have := hp.nsc; omega) (by rw [e₄di, tO']; omega)
    (fun j hj => by
      rw [k₄.ebp]
      exact ⟨scR s₀ F, List.mem_append_right _ (by rw [k₄.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [e₄di, eO]
      exact ⟨outR s₀, by rw [k₄.wr, hp.wr]; simp, by
        rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [k₄.ebp, e₄di, eO]
        exact (hp.o_s.sub_left osub).symm.sub_left (part_sub (F := F) (by omega)))) fun t c => ?_
  rw [k₄.ebp, e₄di, eO] at c
  have cm : t.mem = writeBytes s.mem ((out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D))
      (bytesAt s.mem (A s₀ F.tO) n) := by rw [c.mem, m₄]
  have f : Frame [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩] s₄.mem t.mem := by
    rw [cm, m₄]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k₄.keep c.rd c.wr (fun r hr => c.other r (by
      simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide))
    (rs := [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩]) f
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.o_s.sub_left osub).symm.sub_left (sv_sub hz))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, osub⟩),
    by rw [c.other _ (by decide), e₄bx], by rw [c.other _ (by decide), e₄si], cm⟩

/-- The rest of a step: as much of `T` as the output needs, copied out,
`INT (k + 2)`, and whether that was the last block. -/
theorem tail_ok {k : Nat} (hk : k < nbk F s₀) {s : State} (h : Inv hF s₀ k s)
    (ht : bytesAt s.mem (A s₀ F.tO) F.H.D = Tk hF s₀ (k + 1)) :
    WP isa (.seq F.outLen (.seq F.outLoop (.block F.advance))) s fun t =>
      Inv hF s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = nbk F s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have hD := hz.D
  have hol : ol s₀ < 2 ^ 32 := (arg s₀ 6).isLt
  have hno := hp.no
  have hkD : k * F.H.D < ol s₀ := (Whole.lt_nb hD.1).1 hk
  have hdn : dn F s₀ k = k * F.H.D := by show min _ _ = _; omega
  generalize en : min (ol s₀ - k * F.H.D) F.H.D = n
  have hn : 0 < n := by omega
  have hkn : k * F.H.D + n ≤ ol s₀ := by omega
  have hnD : n ≤ F.H.D := by omega
  have hdn' : dn F s₀ (k + 1) = k * F.H.D + n := by show min _ _ = _; rw [Nat.succ_mul]; omega
  have osub : Region.Sub ⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ (outR s₀) :=
    Offset.sub_base _ hkn
  refine WP.seq (WP.mono (outLen_ok hp hz hkD h) fun s₁ ⟨i₁, c₁, m₁⟩ => ?_)
  rw [en] at c₁
  refine WP.seq (WP.mono (outLoop_ok hp hz hn hkn hnD i₁ c₁ hkD) fun s₂ ⟨k₂, b₂, e₂, m₂⟩ => ?_)
  unfold Fns.advance
  refine wp_add fun s₃ u₃ => ?_
  have k₃ := k₂.upd (by decide) u₃
  refine wp_movm (a := A s₀ F.intO) (ea_scr hp k₃ (by omega)) (by
      obtain ⟨r, hr, c⟩ := in_sc hp hz k₃.wr (o := F.intO) (n := 4) (by omega)
      exact ⟨r, List.mem_append_right _ hr, c⟩)
    fun s₄ u₄ => wp_bswap fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_bswap fun s₇ u₇ => ?_
  have k₇ := (((k₃.upd (by decide) u₄).upd (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  refine wp_store (a := A s₀ F.intO) (ea_scr hp k₇ (by omega)) (in_sc hp hz k₇.wr (by omega)) fun s₈ m₈ => ?_
  have fr₈ : Frame [sR s₀ F.intO 4] s₇.mem s₈.mem := by
    rw [m₈.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₈ := k₇.write hz m₈.rd m₈.wr (fun r _ => by rw [m₈.gpr]) (by omega) (by omega) fr₈
  refine wp_arg hp k₈ (by decide) fun s₉ u₉ => wp_cmp fun s₁₀ f₁₀ _ z₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s₂.mem.writeW (A s₀ F.intO) (s₇.gpr .eax) := by
    rw [f₁₀.mem, u₉.mem, m₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have fr₂ : Frame [sR s₀ F.intO 4] s₂.mem s₁₀.mem := by
    rw [m₁₀]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr₁ : Frame [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have dI : (sR s₀ F.intO 4).Disjoint ⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩ :=
    ((hp.o_s.sub_left osub).sub_right (part_sub (by omega))).symm
  have r₂ : s₂.mem.readW (A s₀ F.intO) 32 = byteRev32 (BitVec.ofNat 32 (k + 1)) := by
    rw [← i₁.intW]
    exact fr₁.readW (r := sR s₀ F.intO 4) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dI) (by decide)
  have e₇ : s₇.gpr .eax = byteRev32 (BitVec.ofNat 32 (k + 1 + 1)) := by
    rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.mem, r₂, bswap_eq, bswap_eq, Whole.byteRev32_byteRev32, ofNat_succ32]
  have e₉ : s₉.gpr .ebx = BitVec.ofNat 32 (k * F.H.D + n) := by
    rw [u₉.other _ (by decide), m₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, b₂, e₂, i₁.ebx, hdn, ← BitVec.ofNat_add]
  have hg : (Gk hF s₀ (k + 1)) = Gk hF s₀ k ++ Tk hF s₀ (k + 1) := Whole.G_succ _ _ _ _
  have tl : (Tk hF s₀ (k + 1)).length = F.H.D := by rw [← ht, bytesAt_length]
  refine ⟨⟨(k₈.upd (by decide) u₉).same f₁₀.rd f₁₀.wr (fun r _ => by rw [f₁₀.gpr]) f₁₀.mem, ?_, i₁.k0l,
    by rw [f₁₀.gpr, e₉, hdn'], by rw [m₁₀, Mem.readW_writeW_self32, e₇], ?_, ?_⟩, ?_⟩
  · refine i₁.st.keep hz (rs := [⟨(out s₀).setWidth 64 + BitVec.ofNat 64 (k * F.H.D), n⟩, sR s₀ F.intO 4])
      ((fr₁.mono (by simp)).trans (fr₂.mono (by simp))) fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.o_s.sub_left osub).sub_right (part_sub (by omega))).symm
    · exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · rw [hg, List.length_append, i₁.glen, tl, Nat.succ_mul]
  · have osub' : Region.Sub ⟨(out s₀).setWidth 64, k * F.H.D + n⟩ (outR s₀) := Region.sub_prefix hkn
    rw [hdn', bytes_keep fr₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.o_s.sub_left osub').sub_right (part_sub (by omega))) (by omega), m₂]
    have bw := VG.Proof.Sha256.Stream.bytesAt_writeBytes s₁.mem ((out s₀).setWidth 64) (k * F.H.D) (bytesAt s₁.mem (A s₀ F.tO) n)
      (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at bw
    have ob := i₁.outB
    rw [hdn] at ob
    rw [bw, ob, Hmac.Generic.Common.bytesAt_take _ _ hnD, m₁, ht, hg, List.take_append,
      i₁.glen, Nat.add_sub_cancel_left, List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D) (by rw [i₁.glen]),
      List.take_of_length_le (l := Gk hF s₀ k) (i := k * F.H.D + n) (by rw [i₁.glen]; omega)]
  · rw [z₁₀, e₉, u₉.gpr, arg_ofNat 6, sub_beq (by omega) (by omega)]
    have e1 : k + 1 < nbk F s₀ ↔ (k + 1) * F.H.D < ol s₀ := Whole.lt_nb hD.1
    rw [Nat.succ_mul] at e1
    have : (arg s₀ 6).toNat = ol s₀ := rfl
    refine congrArg some (decide_eq_decide.2 ⟨fun h1 => ?_, fun h1 => ?_⟩)
    · by_contra h2
      have := e1.1 (by omega)
      omega
    · have : ¬ (k * F.H.D + F.H.D < ol s₀) := fun h' => absurd (e1.2 h') (by omega)
      omega

/-! ## The loop and `pbkdf2` -/

/-- A block of the output. -/
theorem block_ok {k : Nat} (hk : k < nbk F s₀) {s : State} (h : Inv hF s₀ k s) :
    WP isa F.block s fun t => Inv hF s₀ (k + 1) t ∧ t.zf = some (decide (k + 1 = nbk F s₀)) := by
  unfold Fns.block
  refine WP.seq (WP.mono (b1_ok hp hz h) fun s₁ ⟨i₁, r₁⟩ => ?_)
  refine WP.seq (WP.mono (b2_ok hp hz i₁) fun s₂ ⟨i₂, di, si, ax, cx, dx, m₂⟩ => ?_)
  refine WP.seq (WP.mono (b3_ok hp hz i₂ di si ax cx dx (by rw [m₂]; exact r₁)) fun s₃ ⟨i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (b4_ok hp hz i₃) fun s₄ ⟨i₄, dx, si, ax, cx, di, m₄⟩ => ?_)
  refine WP.seq (WP.mono (b5_ok hp hz i₄ dx si ax cx di (by rw [m₄]; exact r₃)) fun s₅ ⟨i₅, u₅⟩ => ?_)
  refine WP.seq (WP.mono (b6_ok hp hz i₅ u₅) fun s₆ ⟨i₆, u₆, t₆⟩ => ?_)
  refine WP.seq (WP.mono (b7_ok hp hz i₆) fun s₇ ⟨i₇, si, ax, cx, dx, m₇⟩ => ?_)
  refine WP.seq (WP.mono (b8_ok hp hz i₇ si ax cx dx (by rw [m₇]; exact u₆) (by rw [m₇]; exact t₆))
    fun s₈ ⟨i₈, t₈⟩ => ?_)
  exact tail_ok hp hz hk i₈ t₈

/-- The loop over the blocks of the output, if there are any. -/
theorem loop_ok {s : State} (h : Inv hF s₀ 0 s) (hz' : s.zf = some (decide (ol s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop F.block .ne)) s (Inv hF s₀ (nbk F s₀)) := by
  have hD := hz.D
  have e0 : nbk F s₀ = 0 ↔ ol s₀ = 0 := Whole.nb_zero hD.1
  refine WP.ite (decide (ol s₀ = 0)) (by show eval .e s = _; rw [VG.Proof.Sha256.X86.Stream.eval_e, hz'])
    (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · rw [e0.2 (of_decide_eq_true h0)]; exact h
  · have hpos : 0 < nbk F s₀ := by
      have := of_decide_eq_false h0; have : nbk F s₀ ≠ 0 := fun e => this (e0.1 e); omega
    exact count_loop hpos (Inv hF s₀) (fun k hk t ht => block_ok hp hz hk ht) h

theorem correct : WP isa F.pbkdf2 s₀ fun s' => abiPreserved s₀ s' ∧ (pbkG hF.hH.SH (F.W + F.H.S)).post s₀ s' := by
  have hD := hz.D
  unfold Fns.pbkdf2
  refine WP.seq (WP.mono (prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (keyed_ok (hF := hF) hp hz k₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (setup_ok hp hz hF h₂) fun s₃ ⟨k₃, st₃, kl₃⟩ => ?_)
  refine WP.seq (WP.mono (loopInit_ok hp hz k₃ st₃ kl₃) fun s₄ ⟨i₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hp hz i₄ z₄) fun s₅ h₅ => ?_)
  have k₅ := h₅.kr
  have hL := L8_le hz; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (Pbkdf2.Stream.X86.restore_ok F.L k₅.ebp k₅.saved (by rw [k₅.wr]; exact sc_mem hp)
    (show 8 * F.W + 16 ≤ F.L8 by have := hz.fits; omega) hp.nsc)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact k₅.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₅.esp]
    · exact hg r (Pbkdf2.Stream.X86.callee_saved r hr he)
  · have ob := h₅.outB
    have e : dn F s₀ (nbk F s₀) = ol s₀ := Whole.done_nb hD.1
    rw [e] at ob
    show Spec.Pbkdf2.pbkdf2Hmac _ _ _ _ _ = some (bytesAt s'.mem _ _)
    unfold Spec.Pbkdf2.pbkdf2Hmac
    rw [hF.hH.hD]
    exact Whole.pbkdf2_eq (prf hF s₀) (saltB s₀) hp.olD (by rw [hm, ob])

end

end VG.Proof.Pbkdf2.Whole.X86
