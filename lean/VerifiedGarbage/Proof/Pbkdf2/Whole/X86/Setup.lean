import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Key
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: HMAC's states for the key, and the salt

HMAC's `init` makes the key's inner and outer states; the inner one is copied
and absorbs the salt (`setup_ok`), which gives the three states every block
starts from (`States`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Impl.Pbkdf2.Stream.X86 (Hash at_ copy)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK UpdArgs upd_frame CopyInv Copied copy_ok cclob)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad)

variable {F : Fns}

/-- `K₀`, the password padded (or hashed and padded) to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte :=
  blockKey hF.hH.SH.H (bytesAt s₀.mem ((pw s₀).setWidth 64) (pwl s₀))

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem ((salt s₀).setWidth 64) (sl s₀)

/-- The key's states, and the inner one after the salt. -/
structure States (hF : FnsOK F) (s₀ : State) (m : Mem) : Prop where
  st0 : hF.hH.SH.Repr m (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad)
  st1 : hF.hH.SH.Repr m (A s₀ F.st1O) (xorPad (K0 hF s₀) opad)
  stS : hF.hH.SH.Repr m (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad ++ saltB s₀)

/-- The representation is kept by what writes elsewhere. -/
theorem repr_keep (hH : HashOK F.H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, F.H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, F.H.S⟩) hd (by show F.H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr

/-- The three states are kept by what writes elsewhere: after them in `scratch`. -/
theorem States.keep {hF : FnsOK F} {s₀ : State} (hz : Sizes F) {m m' : Mem} (h : States hF s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ F.st0O (3 * F.H.S)) r) :
    States hF s₀ m' := by
  have hl := layout (F := F); have he := end_le hz; have := hz.D
  have sub : ∀ o, F.st0O ≤ o → o + F.H.S ≤ F.st0O + 3 * F.H.S →
      Region.Sub (sR s₀ o F.H.S) (sR s₀ F.st0O (3 * F.H.S)) := fun o h₁ h₂ =>
    Offset.sub _ h₁ h₂
  refine ⟨repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.st0,
    repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.st1,
    repr_keep hF.hH hf (fun r hr => (hd r hr).sub_left (sub _ (by omega) (by omega))) h.stS⟩

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-- A copy of `n > 0` bytes within `scratch`, after the save area. -/
theorem copy_part_ok {s : State} (hk : KR F s₀ s) {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ F.L8)
    (hb : b + n ≤ F.L8) (hb' : 8 * F.W + 16 ≤ b) (hab : a + n ≤ b ∨ b + n ≤ a) :
    WP isa (copy .ebp a .ebp b n) s fun t => KR F s₀ t ∧ (∀ r ∉ cclob, t.gpr r = s.gpr r) ∧
      t.mem = writeBytes s.mem (A s₀ b) (bytesAt s.mem (A s₀ a) n) := by
  have hL := L8_le hz; have := hp.nsc; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copy_ok (src := .ebp) (dst := .ebp) (by decide) (by decide) hn (by omega)
    (by rw [hk.ebp]; omega) (by rw [hk.ebp]; omega)
    (fun j hj => by
      rw [hk.ebp]
      exact ⟨scR s₀ F, List.mem_append_right _ (by rw [hk.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [hk.ebp]
      exact ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp,
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [hk.ebp]; exact part_disj hz hab ha hb)) fun t c => ?_
  rw [hk.ebp] at c
  have f : Frame [sR s₀ b n] s.mem t.mem := by
    rw [c.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  exact ⟨hk.write hz c.rd c.wr (fun r hr => c.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide))
    hb' hb f, c.other, c.mem⟩

omit hp hz in
/-- After such a copy, the bytes at `b` are those at `a`. -/
theorem copied_byte {m : Mem} {a b n : Nat} (hn : n ≤ 2 ^ 32) (i : Nat) (hi : i < n) :
    writeBytes m (A s₀ b) (bytesAt m (A s₀ a) n) (A s₀ b + BitVec.ofNat 64 i) = m (A s₀ a + BitVec.ofNat 64 i) := by
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega), bytesAt_getD' _ _ hi]

end

/-- After the key: where it is, and its `K₀`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  edx : s.gpr .edx = kp F s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 (kl F s₀)
  k0 : blockKey hF.hH.SH.H (bytesAt s.mem ((kp F s₀).setWidth 64) (kl F s₀)) = K0 hF s₀

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hF : FnsOK F)
include hp hz hF

theorem keyed_ok {s : State} (hk : KR F s₀ s) : WP isa F.key s (Keyed hF s₀) :=
  WP.mono (key_ok hp hz hF.hH hk) fun _ ⟨k, d, c, b⟩ => ⟨k, d, c, b⟩

omit hp hz in
theorem su1_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.st0O ++ VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O)) s
      fun t => Keyed hF s₀ t ∧ t.gpr .edi = dO s₀ F.st0O ∧ t.gpr .esi = dO s₀ F.st1O := by
  refine scr_ok h.kr fun s₁ u₁ => ?_
  have k₁ := h.kr.upd (by decide) u₁
  rw [← List.append_nil (VG.Impl.Pbkdf2.Stream.X86.scr .esi F.st1O)]
  refine scr_ok k₁ fun s₂ u₂ => WP.block_nil ⟨⟨k₁.upd (by decide) u₂, ?_, ?_, ?_⟩, ?_, u₂.gpr⟩
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.edx]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · rw [u₂.mem, u₁.mem]; exact h.k0
  · rw [u₂.other _ (by decide), u₁.gpr]

theorem su2_args {s : State} (h : Keyed hF s₀ s) (hdi : s.gpr .edi = dO s₀ F.st0O)
    (hsi : s.gpr .esi = dO s₀ F.st1O) :
    HiArgs hF.hH.SH hF.Wi s (dO s₀ F.st0O) (dO s₀ F.st1O) (kp F s₀) (scr s₀) (kl F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have hk := h.kr
  have kd : ∀ o n, o + n ≤ F.hkO → F.st0O ≤ o →
      Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (sR s₀ o n) := fun o n h₁ h₂ =>
    key_disj hp hz (part_sub (by omega)) (part_disj hz (Or.inl h₁) (by omega) (by omega))
  have kls : Region.Disjoint ⟨(kp F s₀).setWidth 64, kl F s₀⟩ (lowR s₀ (hF.Wi * 8)) :=
    key_disj hp hz (low_sub (by omega)) (low_disj hz (by omega) (by omega))
  exact
    { edi := hdi
      esi := hsi
      edx := h.edx
      ecx := h.ecx
      ebp := hk.ebp
      klB := by rw [hF.hH.hB]; exact kl_le hp hz
      kl32 := by have := kl_le hp hz; have := hz.B; omega
      sp := by rw [hk.esp]; exact hp.sp76
      cr := key_cov hp hz hk
      cw := by
        rw [hS, e0, e1]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp hk (by omega)
          · exact cov_part hp hk (by omega)
          · exact cov_low hp hk (by omega)
      i_o := by rw [hS, e0, e1]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_k := by rw [hS, e0]; exact (kd _ _ (by omega) (by omega)).symm
      i_s := by rw [hS, e0]; exact (low_disj hz (by omega) (by omega)).symm
      o_k := by rw [hS, e1]; exact (kd _ _ (by omega) (by omega)).symm
      o_s := by rw [hS, e1]; exact (low_disj hz (by omega) (by omega)).symm
      k_s := kls
      b_i := by rw [hS, e0]; exact b76 hp hk (part_sub (by omega))
      b_o := by rw [hS, e1]; exact b76 hp hk (part_sub (by omega))
      b_k := key_stk hp hz hk
      b_s := b76 hp hk (low_sub (by omega))
      ni := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nk := key_toNat hp hz
      nsc := by have := hp.nsc; omega }

theorem su2_ok {s : State} (h : Keyed hF s₀ s) (hdi : s.gpr .edi = dO s₀ F.st0O)
    (hsi : s.gpr .esi = dO s₀ F.st1O) :
    WP isa (.frame (.push hi5) (.call F.hiN F.hiC) (.pop .eax hi5.length)) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  refine hi_frame hF.hi hF.hiSp hF.hiSU (su2_args hp hz hF h hdi hsi) fun s' a r0 r1 => ⟨?_, ?_, ?_⟩
  · refine h.kr.call hp hz a fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, by rw [e0, hS], by omega, by omega⟩
    · exact .inr ⟨_, _, by rw [e1, hS], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  · rw [h.k0, e0] at r0; exact r0
  · rw [h.k0, e1] at r1; exact r1

omit hF in
theorem K0_length (hF : FnsOK F) {s : State} (h : Keyed hF s₀ s) : (K0 hF s₀).length = F.H.B := by
  have := kl_le hp hz
  rw [← h.k0]
  simp only [blockKey, hF.hH.hB, bytesAt_length, show ¬ F.H.B < kl F s₀ by omega, ↓reduceIte,
    List.length_append, List.length_replicate]
  omega

/-- The key's inner state, copied for the salt. -/
theorem su3_ok {s : State} (hk : KR F s₀ s) (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad)) :
    WP isa (copy .ebp F.st0O .ebp F.stSO F.H.S) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have hL := L8_le hz
  refine WP.mono (copy_part_ok hp hz hk hz.S.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨k, _, m⟩ => ?_
  have f : Frame [sR s₀ F.stSO F.H.S] s.mem t.mem := by
    rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k, repr_keep hF.hH f (fun r hr => ?_) r0, repr_keep hF.hH f (fun r hr => ?_) r1, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) r0
    rw [m]; exact copied_byte (by omega) i hi

omit hz hF in
/-- `update`'s arguments: the salt. -/
theorem su4_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block (VG.Impl.Pbkdf2.Stream.X86.scr .edi F.stSO ++ ([.mov .eax (.imm 0),
      .mov .esi (.imm (BitVec.ofNat 32 F.H.B)), .mov .ecx (Fns.argM 3), .mov .edx (Fns.argM 2)] : List Instr))) s
      fun t => KR F s₀ t ∧ t.gpr .edi = dO s₀ F.stSO ∧ t.gpr .esi = BitVec.ofNat 32 F.H.B ∧ t.gpr .eax = 0 ∧
        t.gpr .ecx = arg s₀ 3 ∧ t.gpr .edx = salt s₀ ∧ t.mem = s.mem := by
  refine scr_ok hk fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
  have k₃ := ((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  refine wp_arg hp k₃ (by decide) fun s₄ u₄ => ?_
  have k₄ := k₃.upd (by decide) u₄
  refine wp_arg hp k₄ (by decide) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨k₄.upd (by decide) u₅, ?_, ?_, ?_, ?_, u₅.gpr, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.gpr]

omit hF in
/-- The salt is apart from `scratch`, so `B + salt_len` does not wrap around. -/
theorem salt_fit : F.H.B + 4 + sl s₀ < 2 ^ 32 := by
  have h₁ : (saltR s₀).base.toNat + (saltR s₀).len ≤ 2 ^ 32 := by
    show ((salt s₀).setWidth 64).toNat + sl s₀ ≤ _; rw [toNat_setWidth64]; exact hp.nsa
  have h₂ : (scR s₀ F).base.toNat + (scR s₀ F).len ≤ 2 ^ 32 := by
    show ((scr s₀).setWidth 64).toNat + F.L8 ≤ _; rw [toNat_setWidth64]; exact hp.nsc
  have h : sl s₀ + (F.W + F.H.S) * 8 ≤ 2 ^ 32 := Pbkdf2.Whole.len_add_le hp.sa_s h₁ h₂
  have := hz.B; have := hz.S; have := hz.BS
  omega

theorem su5_args {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stSO)
    (hsi : s.gpr .esi = BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 3)
    (hdx : s.gpr .edx = salt s₀) :
    UpdArgs hF.hH s .esi .edi (dO s₀ F.stSO) (salt s₀) (scr s₀) (BitVec.ofNat 32 F.H.B) (sl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega)
  exact
    { hst := hdi
      hlo := hsi
      eax := hax
      ecx := by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := hdx
      ebp := hk.ebp
      hr := by decide
      hl := by decide
      hlen := (arg s₀ 3).isLt
      sp48 := by rw [hk.esp]; have := hp.sp76; omega
      cd := cov_salt hp hk
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp hk (by omega)
          · exact cov_low hp hk (by omega)
      st_sc := by rw [ea]; exact (low_disj hz (k := hF.hH.Wb) (by omega) (by omega)).symm
      d_st := by rw [ea]; exact hp.sa_s.sub_right (part_sub (by omega))
      d_sc := hp.sa_s.sub_right (low_sub (by omega))
      b_st := by rw [ea]; exact b48 hp hk (part_sub (by omega))
      b_d := hp.b_sa.sub_left (stk48_sub hp hk)
      b_sc := b48 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := hp.nsa
      nsc := by have := hp.nsc; omega }

theorem su5_ok {s : State} (hk : KR F s₀ s) (hdi : s.gpr .edi = dO s₀ F.stSO)
    (hsi : s.gpr .esi = BitVec.ofNat 32 F.H.B) (hax : s.gpr .eax = 0) (hcx : s.gpr .ecx = arg s₀ 3)
    (hdx : s.gpr .edx = salt s₀) (hkl : (K0 hF s₀).length = F.H.B)
    (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad))
    (rS : hF.hH.SH.Repr s.mem (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad)) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)) s
      fun t => KR F s₀ t ∧ States hF s₀ t.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega)
  refine upd_frame hF.hH (su5_args hp hz hF hk hdi hsi hax hcx hdx) fun s' a r => ⟨hk.call hp hz (After.of_hmac (by
    rw [hk.esp]; exact hp.sp76) a) fun r hr => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, by rw [ea], by omega, by omega⟩
    · exact .inl ⟨_, rfl, by omega⟩
  all_goals have f := a.frame
  all_goals rw [ea] at f
  · refine repr_keep hF.hH f (fun r hr => ?_) r0
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
    · exact low_disj hz (by omega) (by omega) |>.symm
    · exact (b48 hp hk (part_sub (by omega))).symm
  · refine repr_keep hF.hH f (fun r hr => ?_) r1
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
    · exact low_disj hz (by omega) (by omega) |>.symm
    · exact (b48 hp hk (part_sub (by omega))).symm
  · have := r (xorPad (K0 hF s₀) ipad) (by rw [ea]; exact rS) (by
      rw [xorPad_length, hkl, Pbkdf2.Stream.X86.zero_append_ofNat (by have := hz.B; omega)])
    rw [ea, hk.saltBytes hp] at this
    exact this

theorem setup_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa F.setup s fun t => KR F s₀ t ∧ States hF s₀ t.mem ∧ (K0 hF s₀).length = F.H.B := by
  have hkl := K0_length hp hz hF h
  unfold Fns.setup
  refine WP.seq (WP.mono (su1_ok hF h) fun s₁ ⟨k₁, d₁, i₁⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hF k₁ d₁ i₁) fun s₂ ⟨k₂, r0, r1⟩ => ?_)
  refine WP.seq (WP.mono (su3_ok hp hz hF k₂ r0 r1) fun s₃ ⟨k₃, r0, r1, rS⟩ => ?_)
  refine WP.seq (WP.mono (su4_ok hp k₃) fun s₄ ⟨k₄, d₄, i₄, a₄, c₄, x₄, m₄⟩ => ?_)
  exact WP.mono (su5_ok hp hz hF k₄ d₄ i₄ a₄ c₄ x₄ hkl (m₄ ▸ r0) (m₄ ▸ r1) (m₄ ▸ rS))
    fun t ⟨k, st⟩ => ⟨k, st, hkl⟩

end

end VG.Proof.Pbkdf2.Whole.X86
