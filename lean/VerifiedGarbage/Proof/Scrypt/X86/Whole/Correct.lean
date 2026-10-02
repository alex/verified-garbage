import VerifiedGarbage.Proof.Scrypt.X86.Whole.Calls

/-!
# scrypt on x86 (32-bit): correctness

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Scrypt/X86_64/Whole/Correct.lean`): step 1 leaves the blocks `X k`
of `PBKDF2-HMAC-SHA256 (P, S, 1, 128 blen)` in `b` (`step1_ok`); the loop
replaces them by their scryptROMix one at a time (`Inv`, `loop_ok`); step 3
derives the key from them (`step3_ok`). `scrypt_ok` puts the frame around
it (`push_ctx`), for any implementation `pbk` of PBKDF2 verified against
its shared contract that uses at most 76 bytes of stack.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The password, the salt and the blocks -/

namespace Ctx

variable {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok)
include hc hL

theorem pw_bytes : bytesAt t.mem (L.pw.setWidth 64) L.pwl.toNat = bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.pb, hL.pv, hL.pc, hL.po, hL.kp.symm]) (by have := hL.np; omega)

theorem salt_bytes :
    bytesAt t.mem (L.salt.setWidth 64) L.sl.toNat = bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat :=
  Memory.frame_bytesAt hc.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    exacts [hL.sb, hL.sv, hL.sc, hL.so, hL.ks.symm]) (by have := hL.ns; omega)

end Ctx

/-- Block `k` of step 1. -/
def X (L : Lay) (m₀ : Mem) (k : Nat) : List Byte :=
  (Spec.Scrypt.blocks (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat)
    L.r.toNat L.pp).getD k []

/-- The derived key of step 1, from the password and the salt on entry. -/
abbrev Step1 (L : Lay) (m₀ : Mem) (B : List Byte) : Prop :=
  Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
    (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) 1 (L.blen.toNat * 128) = some B

theorem X_of (hL : L.Ok) {m : Mem} (h : Step1 L m₀ (bytesAt m (L.b.setWidth 64) (L.blen.toNat * 128))) {k : Nat}
    (hk : k < L.pp) : X L m₀ k = bytesAt m (blk L k) (128 * L.r.toNat) := by
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have h' : Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) 1 (L.pp * 128 * L.r.toNat) =
      some (bytesAt m (L.b.setWidth 64) (L.pp * 128 * L.r.toNat)) := by rw [e]; exact h
  have hl : k < (Spec.Scrypt.blocks (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
      (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat) L.r.toNat L.pp).length := by
    rw [Whole.blocks_length]; exact hk
  rw [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    Whole.blocks_getElem h' hl]

theorem blk_le' (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    128 * L.r.toNat * i + 128 * L.r.toNat ≤ L.blen.toNat * 128 := by
  have := blk_le hL hi; rw [Nat.mul_comm L.r.toNat 128] at this; exact this

/-- Distinct blocks are disjoint. -/
theorem blk_disj (hL : L.Ok) {k i : Nat} (hk : k < L.pp) (hi : i < L.pp) (hne : k ≠ i) :
    Region.Disjoint ⟨blk L k, 128 * L.r.toNat⟩ ⟨blk L i, L.r.toNat * 128⟩ := by
  have h₁ := blk_le hL hk
  have h₂ := blk_le hL hi
  have := hL.nb
  have hr := hL.rpos
  refine Offset.disjoint _ ?_ (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have : 128 * L.r.toNat * k + 128 * L.r.toNat ≤ 128 * L.r.toNat * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega
  · right
    have : 128 * L.r.toNat * i + 128 * L.r.toNat ≤ 128 * L.r.toNat * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    omega

theorem blk_sub (hL : L.Ok) {k : Nat} (hk : k < L.pp) :
    Region.Sub ⟨blk L k, 128 * L.r.toNat⟩ L.BB := by
  have := blk_le' hL hk
  exact Offset.sub_base _ (by omega)

theorem scr_sub (hL : L.Ok) : Region.Sub ⟨L.scr.setWidth 64, 200 * 8⟩ L.SC :=
  Within.sub (within_base _ (by have := hL.slen17; omega))

/-- A range in `b` misses the stack. -/
theorem b_stk (hL : L.Ok) {p : Addr} {n : Nat} (h : Region.Sub ⟨p, n⟩ L.BB) {d k : Nat} (hd : d + k ≤ 116) :
    Region.Disjoint ⟨p, n⟩ ⟨L.A + BitVec.ofNat 64 d, k⟩ :=
  (hL.kb.symm.sub_left h).sub_right (Offset.sub_base _ hd)

theorem toNat_blen (hL : L.Ok) : (BitVec.ofNat 32 (L.blen.toNat * 128)).toNat = L.blen.toNat * 128 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL.blen_lt]

/-! ## Step 1 -/

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hsp hst in
theorem pbk1_regions (hL : L.Ok) :
    PbkRegions L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) := by
  refine ⟨⟨L.SALT, by simp, within_base _ (Nat.le_refl _)⟩, ?_, ?_, hL.sc.sub_right (scr_sub hL), ?_, hL.ks,
    hL.ns, ?_, ?_⟩
  · rw [toNat_blen hL]; exact .inl (within_base _ (Nat.le_refl _))
  · rw [toNat_blen hL]; exact hL.sb
  · rw [toNat_blen hL]; exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_blen hL]; exact hL.nb
  · rw [toNat_blen hL]; exact hL.ol1

theorem step1_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (pbkCall name pbk pbk1Args) t fun t' => Ctx L g m₀ t' ∧
      Step1 L m₀ (bytesAt t'.mem (L.b.setWidth 64) (L.blen.toNat * 128)) := by
  refine WP.seq (pbk1Args_ok hL hc fun t₁ hc₁ _ ha₁ => ?_)
  refine WP.mono (pbk_call hv hsp hst name hL hc₁ ha₁ (pbk1_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  rw [toNat_blen hL, hc₁.pw_bytes hL, hc₁.salt_bytes hL] at hp
  exact hp

end

/-! ## The loop -/

/-- After `i` iterations of the loop: the next block is `i`, and blocks
`0, …, i - 1` are scryptROMix of those of step 1. -/
structure InvB (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur L i
  blks : ∀ k < L.pp, bytesAt t.mem (blk L k) (128 * L.r.toNat) =
    if k < i then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

abbrev Inv (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (i : Nat) (t : State) : Prop :=
  Ctx L g m₀ t ∧ InvB L m₀ i t

/-- In iteration `i`, after the call of ROMix: blocks `0, …, i` are scryptROMix
of those of step 1. -/
structure Mid (L : Lay) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  cur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur L i
  blks : ∀ k < L.pp, bytesAt t.mem (blk L k) (128 * L.r.toNat) =
    if k < i + 1 then Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) else X L m₀ k

theorem cur0' (L : Lay) : cur L 0 = L.b := by
  simp only [cur, Nat.mul_zero]; exact BitVec.add_zero _

/-- The bytes of a block, across a change of the frame. -/
theorem blk_fr (hL : L.Ok) {k : Nat} (hk : k < L.pp) {m m' : Mem} (hf : Frame [L.FR] m m') :
    bytesAt m' (blk L k) (128 * L.r.toNat) = bytesAt m (blk L k) (128 * L.r.toNat) :=
  Memory.frame_bytesAt hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact b_stk hL (blk_sub hL hk) (by omega))
    (by have := hL.blen_lt; have := blk_le hL hk; omega)

theorem start_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t)
    (h1 : Step1 L m₀ (bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128))) :
    WP isa (.block cur0) t (Inv L g m₀ 0) :=
  cur0_ok hL hc fun t' hc' hf hb => ⟨hc', hb.trans (cur0' L).symm, fun k hk => by
    simp only [Nat.not_lt_zero, ite_false]
    rw [blk_fr hL hk hf, X_of hL h1 hk]⟩

theorem next_eq (L : Lay) (i : Nat) :
    cur L i + BitVec.ofNat 32 (L.r.toNat * 128) = cur L (i + 1) := by
  simp only [cur]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ (128 * L.r.toNat) i, Nat.mul_comm L.r.toNat 128]

theorem beq32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem zf_eq (hL : L.Ok) {i : Nat} (hi : i < L.pp) :
    (cur L (i + 1) - (BitVec.ofNat 32 (L.blen.toNat * 128) + L.b) == 0) = decide (i + 1 = L.pp) := by
  have h₁ := blk_le hL hi
  have hb := hL.blen_lt
  have hr := hL.rpos
  have e₁ : 128 * L.r.toNat * (i + 1) < 2 ^ 32 := by
    rw [Nat.mul_succ]; omega
  rw [BitVec.add_comm (BitVec.ofNat 32 _) L.b]
  simp only [cur]
  rw [Offset.add_sub_add_left, ← hL.len_b, beq32 e₁ (by rw [hL.len_b]; exact hb)]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  exact Nat.eq_of_mul_eq_mul_left (by omega) h

theorem call_step (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (hc : Ctx L g m₀ t)
    (hb : InvB L m₀ i t) (ha : RomixArgs L (cur L i) t.mem) :
    WP isa (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix) t fun t' => Ctx L g m₀ t' ∧ Mid L m₀ i t' := by
  have hnB := hL.nB
  refine WP.mono (romix_call hL hc hi ha) fun t₂ ⟨hc₂, hf₂, hr₂⟩ => ⟨hc₂, ?_, fun k hk => ?_⟩
  · rw [← hb.cur]
    refine hf₂.readW (r := ⟨L.A + BitVec.ofNat 64 112, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hL.stk_in (by omega) (blk_in hL hi)
    · exact hL.stk_in (by omega) (.inr (.inl (within_base _ (Nat.le_refl _))))
    · exact hL.stk_in (by omega) (.inr (.inr (.inl (within_base _ (by have := hL.slen; omega)))))
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · by_cases hki : k = i
    · subst hki
      rw [hr₂, hb.blks k hk]
      simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
    · have e₂ : bytesAt t₂.mem (blk L k) (128 * L.r.toNat) = bytesAt t.mem (blk L k) (128 * L.r.toNat) :=
        Memory.frame_bytesAt hf₂ (fun r hr => by
          simp only [romixWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact blk_disj hL hk hi hki
          · exact hL.bv.sub_left (blk_sub hL hk)
          · exact (hL.bc.sub_left (blk_sub hL hk)).sub_right
              (Within.sub (within_base _ (by have := hL.slen; omega)))
          · exact (hL.kb.symm.sub_left (blk_sub hL hk)).sub_right (Region.sub_prefix (by omega)))
          (by have := hL.blen_lt; have := blk_le hL hk; omega)
      rw [e₂, hb.blks k hk]
      by_cases hlt : k < i
      · have : k < i + 1 := by omega
        simp only [hlt, this, ite_true]
      · have : ¬ k < i + 1 := by omega
        simp only [hlt, this, ite_false]

theorem body_ok (hL : L.Ok) {i : Nat} (hi : i < L.pp) {t : State} (h : Inv L g m₀ i t) :
    WP isa (.seq (.block romixArgs) (.seq (.call "vg_scrypt_romix" Impl.Scrypt.X86.roMix)
      (.block nextBlock))) t fun t' => Inv L g m₀ (i + 1) t' ∧ t'.zf = some (decide (i + 1 = L.pp)) :=
  WP.seq (romixArgs_ok hL h.1 h.2.cur fun t₁ hc₁ hf₁ ha₁ hcur₁ =>
    WP.seq (WP.mono (call_step hL hi hc₁ ⟨hcur₁, fun k hk => by rw [blk_fr hL hk hf₁]; exact h.2.blks k hk⟩ ha₁)
      fun t₂ ⟨hc₂, hm₂⟩ => nextBlock_ok hL hc₂ hm₂.cur fun t₃ hc₃ hf₃ hb₃ hz₃ =>
        ⟨⟨hc₃, by rw [hb₃, next_eq], fun k hk => by rw [blk_fr hL hk hf₃]; exact hm₂.blks k hk⟩,
          by rw [hz₃, next_eq, zf_eq hL hi]⟩))

theorem loop_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ 0 t) : WP isa romixLoop t (Inv L g m₀ L.pp) :=
  count_loop hL.pp_pos (Inv L g m₀) (fun _ hi _ h => body_ok hL hi h) h

/-! ## Step 3 -/

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hsp hst in
/-- The blocks after the loop, as one string. -/
theorem final_bytes' (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128) =
      (List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k) := by
  rw [← hL.len_b, Whole.bytesAt_chunks]
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [h.2.blks k hk]; simp only [hk, ite_true]

omit hv hsp hst in
theorem pbk2_regions (hL : L.Ok) :
    PbkRegions L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol := by
  refine ⟨⟨L.BB, by simp, ?_⟩, .inr (.inr (.inr (within_base _ (Nat.le_refl _)))), ?_,
    ?_, hL.co.symm.sub_right (scr_sub hL), ?_, ?_, hL.no, hL.olb⟩
  · rw [toNat_blen hL]; exact within_base _ (Nat.le_refl _)
  · rw [toNat_blen hL]; exact hL.bo
  · rw [toNat_blen hL]; exact hL.bc.sub_right (scr_sub hL)
  · rw [toNat_blen hL]; exact hL.kb
  · rw [toNat_blen hL]; exact hL.nb

theorem step3_ok (hL : L.Ok) {t : State} (h : Inv L g m₀ L.pp t) :
    WP isa (pbkCall name pbk pbk2Args) t fun t' => Ctx L g m₀ t' ∧
      Spec.Pbkdf2.pbkdf2HmacSha256 (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat)
        ((List.range L.pp).flatMap fun k => Spec.Scrypt.roMix L.r.toNat L.NN (X L m₀ k)) 1 L.ol.toNat =
        some (bytesAt t'.mem (L.out.setWidth 64) L.ol.toNat) := by
  refine WP.seq (pbk2Args_ok hL h.1 fun t₁ hc₁ hf₁ ha₁ => ?_)
  refine WP.mono (pbk_call hv hsp hst name hL hc₁ ha₁ (pbk2_regions hL)) fun t₂ ⟨hc₂, _, hp⟩ => ⟨hc₂, ?_⟩
  have e : bytesAt t₁.mem (L.b.setWidth 64) (L.blen.toNat * 128) =
      bytesAt t.mem (L.b.setWidth 64) (L.blen.toNat * 128) :=
    Memory.frame_bytesAt hf₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact b_stk hL (fun _ h => h) (by omega))
      (by have := hL.blen_lt; omega)
  rw [toNat_blen hL, hc₁.pw_bytes hL, e, final_bytes' hL h] at hp
  exact hp

/-- The frame's body. -/
theorem body_scrypt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (scryptBody name pbk) t fun t' => Ctx L g m₀ t' ∧
      Spec.Scrypt.scrypt (bytesAt m₀ (L.pw.setWidth 64) L.pwl.toNat) (bytesAt m₀ (L.salt.setWidth 64) L.sl.toNat)
        L.NN L.r.toNat L.pp L.ol.toNat = some (bytesAt t'.mem (L.out.setWidth 64) L.ol.toNat) := by
  refine WP.seq (WP.mono (step1_ok hv hsp hst name hL hc) fun t₁ ⟨hc₁, h1⟩ => ?_)
  refine WP.seq (WP.mono (start_ok hL hc₁ h1) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (loop_ok hL h₂) fun t₃ h₃ => ?_)
  refine WP.mono (step3_ok hv hsp hst name hL h₃) fun t₄ ⟨hc₄, hp⟩ => ⟨hc₄, ?_⟩
  have e : L.pp * 128 * L.r.toNat = L.blen.toNat * 128 := by
    rw [← hL.len_b]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  refine Whole.scrypt_eq hL.valid (B := bytesAt t₁.mem (L.b.setWidth 64) (L.blen.toNat * 128))
    (by rw [e]; exact h1) ?_
  refine Eq.trans (congrArg (fun x => Spec.Pbkdf2.pbkdf2HmacSha256 _ x 1 _) ?_) hp
  exact Proof.Scrypt.flatMap_congr fun k hk => by
    have hk := List.mem_range.mp hk
    rw [X_of hL h1 hk, Whole.chunk_bytesAt _ _ (blk_le' hL hk)]

end

/-! ## The whole function -/

theorem sub36 (x : BitVec 32) : x - BitVec.ofNat 32 (4 * 9) = x - BitVec.ofNat 32 116 + BitVec.ofNat 32 80 := by
  rw [Offset.sub_ofNat_eq x (show 4 * 9 ≤ 116 by omega)]

theorem push_ctx {s : State} (h : Proof.Scrypt.scryptX86.pre s) :
    Ctx (lay s) s.gpr s.mem (pushed pushRs s) := by
  have h116 := h.1
  have h56 := h.2.1
  have hn : 4 * pushRs.length ≤ (s.gpr .esp).toNat := by show 4 * 9 ≤ _; omega
  have hL := lay_ok h
  have hnB := hL.nB
  have hf := pushed_frame (s := s) (rs := pushRs) (by decide) hn
  have hfr : below (s.gpr .esp) (4 * pushRs.length) = (lay s).FR := by
    show (⟨(s.gpr .esp - BitVec.ofNat 32 (4 * 9)).setWidth 64, 36⟩ : Region) = _
    rw [sub36, show s.gpr .esp - BitVec.ofNat 32 116 = (lay s).B from rfl, addr_B (by omega)]
  rw [hfr] at hf
  have ha : ∀ i, i < 13 → (pushed pushRs s).mem.readW ((lay s).A + BitVec.ofNat 64 (120 + 4 * i)) 32 =
      arg s i := fun i hi => by
    have e : (lay s).A + BitVec.ofNat 64 (120 + 4 * i) = argAddr s i := by
      rw [Lay.A, ← addr_B (by rw [lay_B h116]; omega), argAddr]
      congr 1
      rw [show 120 + 4 * i = 116 + (4 + 4 * i) by omega, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc]
      simp only [lay]; rw [BitVec.sub_add_cancel]
    rw [arg, ← e]
    refine hf.readW (r := ⟨(lay s).A + BitVec.ofNat 64 (120 + 4 * i), 4⟩) (Region.contains_self _ _)
      (fun R hR => ?_) (by decide)
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨by rw [pushed_rd, h.2.2.1]; rfl, ?_, ?_, fun r _ hr => pushed_gpr _ _ hr,
    ⟨ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 4 (by omega), ha 5 (by omega),
      ha 6 (by omega), ha 7 (by omega), ha 8 (by omega), ha 9 (by omega), ha 11 (by omega),
      ha 12 (by omega)⟩, ?_⟩
  · rw [pushed_wr, hfr, h.2.2.2.1, ← lay_args h116 h56]; rfl
  · rw [pushed_esp]; show s.gpr .esp - BitVec.ofNat 32 (4 * 9) = _; rw [sub36]; rfl
  · refine Frame.sub hf fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(lay s).STK, by simp, Offset.sub_base _ (by omega)⟩

theorem ne_cs {r d : Reg} (hr : r ∈ calleeSaved) (hd : d ∉ calleeSaved) : r ≠ d :=
  fun e => hd (e ▸ hr)

theorem pop_esp (B : BitVec 32) : B + BitVec.ofNat 32 80 + BitVec.ofNat 32 (4 * 9) = B + BitVec.ofNat 32 116 := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

omit hv hst in
theorem body_nosp : NoSp (scryptBody name pbk) := by
  have hb : ∀ is : List Instr, is.all (fun i => !Taint.clobbers i .esp) = true →
      ∀ i ∈ is, Taint.clobbers i .esp = false := fun is h i hi => by
    simpa using List.all_eq_true.mp h i hi
  intro i hi
  replace hi : i ∈ (pbk1Args ++ VG.X86.instrs pbk) ++ (cur0 ++ ((romixArgs ++
      (VG.X86.instrs Impl.Scrypt.X86.roMix ++ nextBlock)) ++ (pbk2Args ++ VG.X86.instrs pbk))) := hi
  simp only [List.mem_append, or_assoc] at hi
  rcases hi with h | h | h | h | h | h | h | h
  · exact hb _ (by decide) i h
  · exact hsp i h
  · exact hb _ (by decide) i h
  · exact hb _ (by decide) i h
  · exact roMix_nosp i h
  · exact hb _ (by decide) i h
  · exact hb _ (by decide) i h
  · exact hsp i h

/-- `vg_scrypt` meets `scryptX86` and the calling convention. -/
theorem scrypt_ok {s : State} (h : Proof.Scrypt.scryptX86.pre s) :
    ∃ t s', Exec isa (scrypt name pbk) s t s' ∧ abiPreserved s s' ∧ Proof.Scrypt.scryptX86.post s s' := by
  have hL := lay_ok h
  have hc := push_ctx h
  have hnB := hL.nB
  refine WP.frame (rs := pushRs) (r := .eax) (by decide) (by decide) (by decide)
    (by show 4 * 9 ≤ _; have := h.1; omega) (body_nosp hsp name)
    (WP.mono (body_scrypt_ok hv hsp hst name hL hc) fun u ⟨hu, ho⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩)
  · by_cases hr' : r = .esp
    · subst hr'
      rw [popped_esp, hu.esp, show pushRs.length = 9 from rfl, pop_esp, lay_esp]
    · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
  · rw [popped_mem]
    refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
    · rw [Lay.RET, lay_ret h.1 h.2.1]; exact Region.contains_self _ _
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl | rfl)
      exacts [hL.rb, hL.rv, hL.rc, hL.ro, Offset.disjoint_base _ (by omega) (by omega)]
  · simp only [Proof.Scrypt.scryptX86, popped_mem]
    exact ho

end

end VG.Proof.Scrypt.X86.Whole
