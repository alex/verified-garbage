import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Key
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common

/-!
# PBKDF2-HMAC on 32-bit ARM, the whole derivation: HMAC's states for the key, and the salt

As on x86 (`Proof/Pbkdf2/Whole/X86/Setup.lean`): HMAC's `init` makes the key's
inner and outer states; the inner one is copied and absorbs the salt
(`setup_ok`), which gives the three states every block starts from (`States`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt copy)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK Copied copy_ok cclob count)
open VG.Proof.MdStream.Arm (Upd wp_mov op2_imm op2_reg)
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (blockKey xorPad ipad opad)

variable {F : Fns}

/-- `K₀`, the password padded (or hashed and padded) to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte :=
  blockKey hF.hH.SH.H (bytesAt s₀.mem (State.addr (pw s₀)) (pwl s₀))

abbrev saltB (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (salt s₀)) (sl s₀)

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
    (hb : b + n ≤ F.L8) (hb' : 8 * F.W + 36 ≤ b) (hab : a + n ≤ b ∨ b + n ≤ a) :
    WP isa (copy .r11 a .r11 b n) s fun t => KR F s₀ t ∧ (∀ r ∉ cclob, t.gpr r = s.gpr r) ∧
      t.mem = writeBytes s.mem (A s₀ b) (bytesAt s.mem (A s₀ a) n) := by
  have hL := hz.reach; have := hp.nsc; have eL : F.L8 = (F.W + F.H.S) * 8 := rfl
  refine WP.mono (copy_ok (src := .r11) (dst := .r11) (by decide) (by decide) (by omega) (by omega) hn (by omega)
    (by rw [hk.r11]; omega) (by rw [hk.r11]; omega)
    (fun j hj => by
      rw [hk.r11]
      exact ⟨scR s₀ F, List.mem_append_right _ (by rw [hk.wr]; exact sc_mem hp),
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [hk.r11]
      exact ⟨scR s₀ F, by rw [hk.wr]; exact sc_mem hp,
        by rw [Hmac.Generic.Common.add_ofNat_add]; exact Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [hk.r11]; exact part_disj hz hab ha hb)) fun t c => ?_
  rw [hk.r11] at c
  have f : Frame [sR s₀ b n] s.mem t.mem := by
    rw [c.mem]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  exact ⟨hk.write hz c.rd c.wr c.sp (fun r hr => c.other r (by
    simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide))
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
  r2 : s.gpr .r2 = kp F s₀
  r3 : s.gpr .r3 = BitVec.ofNat 32 (kl F s₀)
  k0 : blockKey hF.hH.SH.H (bytesAt s.mem (State.addr (kp F s₀)) (kl F s₀)) = K0 hF s₀

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hF : FnsOK F)
include hp hz hF

theorem keyed_ok {s : State} (hk : KK F s₀ s) : WP isa F.key s (Keyed hF s₀) :=
  WP.mono (key_ok hp hz hF.hH hk) fun _ ⟨k, d, c, b⟩ => ⟨k, d, c, b⟩

omit hp in
theorem su1_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa (.block F.initArgs) s
      fun t => Keyed hF s₀ t ∧ t.gpr .r0 = dO s₀ F.st0O ∧ t.gpr .r1 = dO s₀ F.st1O ∧ t.gpr .r12 = scr s₀ := by
  have hl := layout (F := F); have he := end_le hz; have := hz.reach
  unfold Fns.initArgs
  rw [List.append_assoc]
  refine scr_ok h.kr (by omega) fun s₁ u₁ => ?_
  have k₁ := h.kr.upd12 (by decide) u₁
  refine scr_ok k₁ (by omega) fun s₂ u₂ => ?_
  have k₂ := k₁.upd12 (by decide) u₂
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ⟨⟨k₂.upd (by decide) u₃, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.r2]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.r3]
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact h.k0
  · rw [u₃.other _ (by decide), u₂.other _ (by decide) (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]
  · rw [u₃.gpr, u₂.other _ (by decide) (by decide), u₁.other _ (by decide) (by decide), h.kr.r11]

theorem su2_args {s : State} (h : Keyed hF s₀ s) (h0 : s.gpr .r0 = dO s₀ F.st0O)
    (h1 : s.gpr .r1 = dO s₀ F.st1O) (h12 : s.gpr .r12 = scr s₀) :
    HiArgs hF.hH.SH hF.Wi s (dO s₀ F.st0O) (dO s₀ F.st1O) (kp F s₀) (scr s₀) (kl F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  have hk := h.kr
  have kd : ∀ o n, o + n ≤ F.hkO → F.st0O ≤ o →
      Region.Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ (sR s₀ o n) := fun o n h₁ h₂ =>
    key_disj hp hz (part_sub (by omega)) (part_disj hz (Or.inl h₁) (by omega) (by omega))
  have kls : Region.Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ (lowR s₀ (hF.Wi * 8)) :=
    key_disj hp hz (low_sub (by omega)) (low_disj hz (by omega) (by omega))
  exact
    { r0 := h0
      r1 := h1
      r2 := h.r2
      r3 := h.r3
      r12 := h12
      klB := by rw [hF.hH.hB]; exact kl_le hp hz
      kl32 := by have := kl_le hp hz; have := hz.B; omega
      sp := by rw [hk.sp]; exact hp.sp24
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
      b_i := by rw [hS, e0]; exact b24 hp hk (part_sub (by omega))
      b_o := by rw [hS, e1]; exact b24 hp hk (part_sub (by omega))
      b_k := key_stk hp hz hk
      b_s := b24 hp hk (low_sub (by omega))
      ni := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      no := by rw [hS, dO_toNat hp (by omega)]; have := hp.nsc; omega
      nk := key_toNat hp hz
      nsc := by have := hp.nsc; omega }

theorem su2_ok {s : State} (h : Keyed hF s₀ s) (h0 : s.gpr .r0 = dO s₀ F.st0O)
    (h1 : s.gpr .r1 = dO s₀ F.st1O) (h12 : s.gpr .r12 = scr s₀) :
    WP isa (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8)) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  have e0 := dO_addr hp (o := F.st0O) (by omega)
  have e1 := dO_addr hp (o := F.st1O) (by omega)
  refine hi_frame hF.hi hF.hiSt (su2_args hp hz hF h h0 h1 h12) fun s' a r0 r1 => ⟨?_, ?_, ?_⟩
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
    WP isa (copy .r11 F.st0O .r11 F.stSO F.H.S) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad) ∧
      hF.hH.SH.Repr t.mem (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have hL := hz.reach
  refine WP.mono (copy_part_ok hp hz hk hz.S.1 (by omega) (by omega) (by omega) (Or.inl (by omega)))
    fun t ⟨k, _, m⟩ => ?_
  have f : Frame [sR s₀ F.stSO F.H.S] s.mem t.mem := by
    rw [m]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨k, repr_keep hF.hH f (fun r hr => ?_) r0, repr_keep hF.hH f (fun r hr => ?_) r1, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  · refine hF.hH.repr _ _ _ _ _ (fun i hi => ?_) r0
    rw [m]; exact copied_byte (by omega) i hi

omit hp hF in
/-- `update`'s arguments: the salt. -/
theorem su4_ok {s : State} (hk : KR F s₀ s) :
    WP isa (.block F.saltArgs) s
      fun t => KR F s₀ t ∧ t.gpr .r0 = dO s₀ F.stSO ∧ t.gpr .r1 = salt s₀ ∧ t.gpr .r7 = s₀.gpr .r3 ∧
        t.gpr .r10 = scr s₀ ∧ count t = BitVec.ofNat 64 F.H.B ∧ t.mem = s.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.reach; have := hz.B
  unfold Fns.saltArgs
  refine scr_ok hk (by omega) fun s₁ u₁ => ?_
  have k₁ := hk.upd12 (by decide) u₁
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    Pbkdf2.Stream.Arm.wp_movw fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have k₆ := ((((k₁.upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅).upd
    (by decide) u₆
  refine ⟨k₆, ?_, ?_, ?_, ?_, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide) (by decide), hk.r5]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide) (by decide), hk.r6]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide) (by decide), hk.r11]
  · simp only [count]
    rw [u₆.gpr, u₆.other .r2 (by decide), u₅.gpr, Pbkdf2.Stream.Arm.movw_ofNat (by omega), zero_append,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

omit hF in
/-- The salt is apart from `scratch`, so `B + 4 + salt_len` does not wrap around. -/
theorem salt_fit : F.H.B + 4 + sl s₀ < 2 ^ 32 := by
  have h₁ : (saltR s₀).base.toNat + (saltR s₀).len ≤ 2 ^ 32 := by
    show (State.addr (salt s₀)).toNat + sl s₀ ≤ _; rw [toNat_addr]; exact hp.nsa
  have h₂ : (scR s₀ F).base.toNat + (scR s₀ F).len ≤ 2 ^ 32 := by
    show (State.addr (scr s₀)).toNat + F.L8 ≤ _; rw [toNat_addr]; exact hp.nsc
  have h : sl s₀ + (F.W + F.H.S) * 8 ≤ 2 ^ 32 := Pbkdf2.Whole.len_add_le hp.sa_s h₁ h₂
  have := hz.B; have := hz.S; have := hz.BS
  omega

theorem su5_args {s : State} (hk : KR F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stSO) (h1 : s.gpr .r1 = salt s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r3) (h10 : s.gpr .r10 = scr s₀) :
    UpdL hF.hH s (dO s₀ F.stSO) (salt s₀) (scr s₀) (sl s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega)
  exact
    { r0 := h0
      r1 := h1
      r7 := by rw [h7, ofNat_toNat32]
      r10 := h10
      hlen := (s₀.gpr .r3).isLt
      sp16 := by rw [hk.sp]; have := hp.sp24; omega
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
      b_st := by rw [ea]; exact b16 hp hk (part_sub (by omega))
      b_d := hp.b_sa.sub_left (below_sub hk)
      b_sc := b16 hp hk (low_sub (by omega))
      nst := by rw [dO_toNat hp (by omega)]; have := hp.nsc; omega
      nd := hp.nsa
      nsc := by have := hp.nsc; omega }

theorem su5_ok {s : State} (hk : KR F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stSO) (h1 : s.gpr .r1 = salt s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r3) (h10 : s.gpr .r10 = scr s₀) (hc : count s = BitVec.ofNat 64 F.H.B)
    (hkl : (K0 hF s₀).length = F.H.B)
    (r0 : hF.hH.SH.Repr s.mem (A s₀ F.st0O) (xorPad (K0 hF s₀) ipad))
    (r1 : hF.hH.SH.Repr s.mem (A s₀ F.st1O) (xorPad (K0 hF s₀) opad))
    (rS : hF.hH.SH.Repr s.mem (A s₀ F.stSO) (xorPad (K0 hF s₀) ipad)) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)) s
      fun t => KR F s₀ t ∧ States hF s₀ t.mem := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hH.hWb
  have ea := dO_addr hp (o := F.stSO) (by omega)
  refine upd_frame hF.hH (su5_args hp hz hF hk h0 h1 h7 h10) fun s' a r => ⟨hk.call hp hz (After.of_hmac a)
    fun r hr => ?_, ?_, ?_, ?_⟩
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
    · exact (b16 hp hk (part_sub (by omega))).symm
  · refine repr_keep hF.hH f (fun r hr => ?_) r1
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
    · exact low_disj hz (by omega) (by omega) |>.symm
    · exact (b16 hp hk (part_sub (by omega))).symm
  · have := r (xorPad (K0 hF s₀) ipad) (by rw [ea]; exact rS) (by rw [xorPad_length, hkl, hc])
    rw [ea, hk.saltBytes hp] at this
    exact this

theorem setup_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa F.setup s fun t => KR F s₀ t ∧ States hF s₀ t.mem ∧ (K0 hF s₀).length = F.H.B := by
  have hkl := K0_length hp hz hF h
  unfold Fns.setup
  refine WP.seq (WP.mono (su1_ok hz hF h) fun s₁ ⟨k₁, a₀, a₁, a₁₂⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hF k₁ a₀ a₁ a₁₂) fun s₂ ⟨k₂, r0, r1⟩ => ?_)
  refine WP.seq (WP.mono (su3_ok hp hz hF k₂ r0 r1) fun s₃ ⟨k₃, r0, r1, rS⟩ => ?_)
  refine WP.seq (WP.mono (su4_ok hz k₃) fun s₄ ⟨k₄, a₀, a₁, a₇, a₁₀, c₄, m₄⟩ => ?_)
  exact WP.mono (su5_ok hp hz hF k₄ a₀ a₁ a₇ a₁₀ c₄ hkl (m₄ ▸ r0) (m₄ ▸ r1) (m₄ ▸ rS))
    fun t ⟨k, st⟩ => ⟨k, st, hkl⟩

end

end VG.Proof.Pbkdf2.Whole.Arm
