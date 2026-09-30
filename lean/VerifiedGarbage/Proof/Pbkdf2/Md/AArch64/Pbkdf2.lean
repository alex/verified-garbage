import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkCalls
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Copy
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`, correct

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Pbkdf2/Md/X86_64/Pbkdf2.lean`): `pbkdf2` saves our caller's
registers, makes the key (hashing a password longer than a block), HMAC's
states for it and the inner state after the salt.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_mov wp_addImm wp_subImm wp_movz wp_lsr wp_str eval_zero sub_beq
  toNat_ofNat_lt add_ofNat)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok)
open VG.Proof.Hmac.Generic.AArch64 (initG After SavedRegs SavedRegs.frame save_ok saveR UpdArgs)
open VG.Proof.Hmac.Generic.AArch64.Init (untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep readW_writeW_ne bytesAt_take covers_one)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_getD' writeBytes_at xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash}

/-! ## Instructions and words -/

theorem wp_subImmW {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth 32 - BitVec.ofNat 32 imm).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .w d n imm :: is)) s Q :=
  VG.Proof.MdStream.AArch64.WP.cons (s' := s.write .w d ((s.gpr n).setWidth 32 - BitVec.ofNat 32 imm))
    (by simp [exec, h, State.read]) (k _ (VG.Proof.MdStream.AArch64.Upd.write s .w d _))

/-- `c - 1`, in 32 bits. -/
theorem sub1_32 (x : BitVec 64) (h : 0 < (x.setWidth 32).toNat) :
    (x.setWidth 32 - BitVec.ofNat 32 1).setWidth 64 = BitVec.ofNat 64 ((x.setWidth 32).toNat - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := (x.setWidth 32).isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat] at h this ⊢
  omega

/-- A shift right leaves zero exactly when the value is below the power of two. -/
theorem shr_beq_zero (x : BitVec 64) (k : Nat) : (x >>> k == 0) = decide (x.toNat < 2 ^ k) := by
  have hk := Nat.two_pow_pos k
  have e : (x >>> k).toNat = x.toNat / 2 ^ k := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases h : x.toNat < 2 ^ k
  · have : x >>> k = 0 := BitVec.eq_of_toNat_eq (by rw [e, Nat.div_eq_of_lt h]; rfl)
    simp [this, h]
  · have hne : (x >>> k == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have h1 : x.toNat / 2 ^ k = 0 := by rw [← e, h0]; rfl
      have h2 : 2 ^ k ≤ x.toNat := by omega
      have := Nat.div_le_div_right (c := 2 ^ k) h2
      rw [Nat.div_self hk] at this
      omega
    rw [hne]; simp [h]

theorem log2_B (hz : PSizes H) : 2 ^ Nat.log2 H.P.B = H.P.B ∧ Nat.log2 H.P.B < 64 := by
  rcases hz.z.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-! ## What the entry sets up, kept until the salt is absorbed -/

/-- The key's registers: `x19` = `password`, `x20` = `password_len`, `x21` =
`salt`, `x22` = `salt_len`. -/
structure KE (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  x19 : s.gpr .x19 = pw s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = salt s₀
  x22 : s.gpr .x22 = s₀.gpr .x3

/-- The registers `KE` fixes. -/
abbrev eregs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

/-- The public ones. -/
abbrev epub : List Reg := [.x19, .x20, .x21, .x22, .x23]

theorem kregs_eregs : ∀ r ∈ kregs, r ∈ eregs := by decide

theorem untouched_ne : ∀ r ∈ untouched, r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x9 ∧ r ≠ .x23 ∧
    r ≠ .x4 ∧ r ≠ .x10 := by decide

theorem KE.upd {s₀ s s' : State} (h : KE (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ eregs) : KE (H := H) s₀ s' := by
  have ne : ∀ r ∈ eregs, r ≠ d := fun r hr e => hd (e ▸ hr)
  exact ⟨h.kr.upd u fun h' => hd (kregs_eregs d h'), by rw [u.other _ (ne _ (by simp)), h.x19],
    by rw [u.other _ (ne _ (by simp)), h.x20], by rw [u.other _ (ne _ (by simp)), h.x21],
    by rw [u.other _ (ne _ (by simp)), h.x22]⟩

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

theorem KE.call {s s' : State} (h : KE (H := H) s₀ s) {ws : List Region} (a : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = sR s₀ o k ∧ H.st0O ≤ o ∧ o + k ≤ (H.W + H.S) * 8) : KE (H := H) s₀ s' :=
  ⟨h.kr.call hp hz a.rd a.wr a.sp a.cs a.frame hw, by rw [a.cs _ (by simp [preserved]) (by decide), h.x19],
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x20], by rw [a.cs _ (by simp [preserved]) (by decide), h.x21],
    by rw [a.cs _ (by simp [preserved]) (by decide), h.x22]⟩

/-! ## The entry -/

theorem entry_ok : WP isa (.block H.entry) s₀ (KE (H := H) s₀) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hW := hz.W
  have hsnw := hp.snw; have hc0 := hp.c0
  simp only [Hash.entry, Hash.entryPre, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => ?_
  have x4 : s₂.gpr .x4 = scr s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  have g₂ : ∀ r, r ≠ .x4 → r ≠ .x10 → s₂.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [u₂.other r h1, u₁.other r h2]
  refine save_ok H.hh (scr := scr s₀) (L := (H.W + H.S) * 8) x4 (by show H.W ≤ 1024; omega)
    (by rw [u₂.wr, u₁.wr]; exact sc_mem hp) (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; omega)
    fun s₃ g₃ rd₃ wr₃ sp₃ f₃ sv₃ => ?_
  simp only [Hash.entryPost]
  refine wp_mov fun s₄ u₄ => ?_
  have x23₄ : s₄.gpr .x23 = scr s₀ := by rw [u₄.gpr, g₃, x4]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, wr₃, u₂.wr, u₁.wr]
  refine wp_str (a := A s₀ H.outO) ⟨by omega, by omega⟩ (by rw [x23₄]) (in_sc hp hz wr₄ (by omega))
    fun s₅ m₅ => ?_
  refine wp_subImmW (by decide) fun s₆ u₆ => ?_
  have x23₆ : s₆.gpr .x23 = scr s₀ := by rw [u₆.other _ (by decide), m₅.gpr, x23₄]
  refine wp_str (a := A s₀ H.cO) ⟨by omega, by omega⟩ (by rw [x23₆])
    (by rw [u₆.wr, m₅.wr]; exact in_sc hp hz wr₄ (by omega)) fun s₇ m₇ => ?_
  refine wp_str (a := A s₀ H.olO) ⟨by omega, by omega⟩ (by rw [m₇.gpr, x23₆])
    (by rw [m₇.wr, u₆.wr, m₅.wr]; exact in_sc hp hz wr₄ (by omega)) fun s₈ m₈ => ?_
  refine wp_mov fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ => wp_mov fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ =>
    WP.block_nil ?_
  -- The registers.
  have g₈ : ∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x4 → r ≠ .x10 → s₈.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [m₈.gpr, m₇.gpr, u₆.other r h1, m₅.gpr, u₄.other r h2, g₃, g₂ r h3 h4]
  have g₁₂ : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → s₁₂.gpr r = s₈.gpr r := fun r a b c d => by
    rw [u₁₂.other r d, u₁₁.other r c, u₁₀.other r b, u₉.other r a]
  have v5 : s₄.gpr .x5 = out s₀ := by rw [u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  have v9 : s₆.gpr .x9 = BitVec.ofNat 64 (cc s₀ - 1) := by
    rw [u₆.gpr, m₅.gpr, u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.gpr, sub1_32 _ hc0]
  have v6 : s₇.gpr .x6 = s₀.gpr .x6 := by
    rw [m₇.gpr, u₆.other _ (by decide), m₅.gpr, u₄.other _ (by decide), g₃, g₂ _ (by decide) (by decide)]
  -- The memory.
  have m₁₂ : s₁₂.mem = ((s₃.mem.writeW (A s₀ H.outO) (out s₀)).writeW (A s₀ H.cO)
      (BitVec.ofNat 64 (cc s₀ - 1))).writeW (A s₀ H.olO) (s₀.gpr .x6) := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, m₈.mem, v6, m₇.mem, v9, u₆.mem, m₅.mem, v5, u₄.mem]
  have d_oc : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.cO, 8⟩ :=
    part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  have d_ol : Region.Disjoint ⟨A s₀ H.outO, 8⟩ ⟨A s₀ H.olO, 8⟩ :=
    part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  have d_cl : Region.Disjoint ⟨A s₀ H.cO, 8⟩ ⟨A s₀ H.olO, 8⟩ :=
    part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  have fW : Frame [sR s₀ H.outO 24] s₃.mem s₁₂.mem := by
    rw [m₁₂]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_refl _) (by omega)
      (by omega))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  have f₀ : Frame [outR s₀, scR (H := H) s₀, stkR s₀] s₀.mem s₁₂.mem := by
    have e₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
    rw [← e₂]
    refine (f₃.sub fun r hr => ?_).trans (fW.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR (H := H) s₀, by simp, Offset.sub_base _ (by show 8 * H.W + 56 ≤ (H.W + H.S) * 8; omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR (H := H) s₀, by simp, part_sub (by omega)⟩
  have sv : SavedRegs H.hh (scr s₀) s₀ s₃.mem :=
    ⟨by rw [sv₃.x19, g₂ _ (by decide) (by decide)], by rw [sv₃.x20, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x21, g₂ _ (by decide) (by decide)], by rw [sv₃.x22, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x24, g₂ _ (by decide) (by decide)], by rw [sv₃.x30, g₂ _ (by decide) (by decide)],
      by rw [sv₃.x23, g₂ _ (by decide) (by decide)]⟩
  refine ⟨⟨by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, m₈.rd, m₇.rd, u₆.rd, m₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd],
    by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, m₈.wr, m₇.wr, u₆.wr, m₅.wr, wr₄],
    by rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, m₈.sp, m₇.sp, u₆.sp, m₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp],
    by rw [g₁₂ _ (by decide) (by decide) (by decide) (by decide), m₈.gpr, m₇.gpr, x23₆],
    fun r hr => by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := untouched_ne r hr
      rw [g₁₂ r n1 n2 n3 n4, g₈ r n5 n6 n7 n8],
    SavedRegs.frame H.hh sv fW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact part_disj hz (a := 8 * H.W) (m := 56) (Or.inl (by omega)) (by omega) (by omega),
    by rw [m₁₂, readW_writeW_ne _ _ d_ol, readW_writeW_ne _ _ d_oc, Mem.readW_writeW_self64],
    by rw [m₁₂, readW_writeW_ne _ _ d_cl, Mem.readW_writeW_self64],
    by rw [m₁₂, Mem.readW_writeW_self64], f₀⟩, ?_, ?_, ?_, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      g₈ _ (by decide) (by decide) (by decide) (by decide)]

end

/-! ## Facts about the hash function -/

theorem _root_.VG.Proof.Pbkdf2.Md.AArch64.HashOK.wb_le (hH : HashOK H) : hH.stream.Wb ≤ 8 * H.W := by
  have := hH.stream.hWb; have e : H.stream.W = (H.P.so + 48) / 8 := rfl; have := hH.sizes.fits; omega

theorem hash_len (hH : HashOK H) (m : List Byte) : (hH.SH.H.hash m).length = H.D := by
  rw [hH.hash, List.length_take, VG.Proof.MdStream.Md.hash, hH.md.digest_length]; have := hH.sizes.DN; omega

/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash (hH : HashOK H) {k : List Byte} (hk : H.P.B < k.length) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hl := hash_len hH k; have hB := hH.hB; have := hH.sizes.pad
  simp only [blockKey, hB, hl, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.P.B < H.D by omega))]

theorem blockKey_length (hH : HashOK H) (k : List Byte) : (blockKey hH.SH.H k).length = H.P.B := by
  have hB := hH.hB; have := hH.sizes.pad
  simp only [blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hash_len]; omega
  · omega

theorem repr_keep (hH : HashOK H) {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.stream.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega) hi) hr

/-- A state copied from `p` to `q` represents the same message. -/
theorem repr_copy (hH : HashOK H) {m : Mem} {p q : Addr} {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr (writeBytes m q (bytesAt m p H.S)) q msg := by
  have : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega
  refine hH.stream.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ (show i < H.S from hi)]

/-! ## Hashing a password longer than a block -/

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hp in
theorem hk1_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.hkInit) s fun t => KE (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.stWO := by
  have hl := layout (H := H); have he := end_le hz
  simp only [Hash.hkInit]
  exact wp_addImm (by omega) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), by rw [u₁.gpr, h.kr.x23]⟩

theorem hk2_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hx0 : s.gpr .x0 = A s₀ H.stWO) :
    WP isa (.call H.initN H.initC) s fun t => KE (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hl := layout (H := H); have he := end_le hz
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  exact VG.Proof.Hmac.Generic.AArch64.init_call hH.stream (st := A s₀ H.stWO) hx0
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h.kr (by omega))
    fun s₂ a₂ r₂ => ⟨h.call hp hz a₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, by omega, by omega⟩, r₂⟩

/-- `update`'s arguments: the password. -/
theorem hk3_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.block H.hkUpd) s fun t => KE (H := H) s₀ t ∧
      UpdArgs hH.stream t (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) [] := by
  have hl := layout (H := H); have he := end_le hz; have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  simp only [Hash.hkUpd]
  refine wp_addImm (by omega) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k₅ := ((((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅
    (by decide)
  refine ⟨k₅, ?_, by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hr⟩
  exact
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h.x19]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.x20]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.kr.x23]
      cd := covers_one (List.mem_append_left _ (by rw [k₅.kr.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₅.kr (by omega)
        · exact cov_low hp k₅.kr (by omega)
      st_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix hWb)
      d_st := hp.pw_s.sub_right (part_sub (by omega))
      d_sc := hp.pw_s.sub_right (Region.sub_prefix (by omega))
      sp16 := by rw [k₅.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp k₅.kr (part_sub (by omega))
      stk_d := by rw [k₅.kr.sp]; exact hp.stk_pw
      stk_sc := stk_sc hp k₅.kr (Region.sub_prefix (by omega)) }

theorem hk4_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (ua : UpdArgs hH.stream s (A s₀ H.stWO) (pw s₀) (scr s₀) (pwl s₀))
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) []) :
    WP isa (.call H.updN H.updC) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hl := layout (H := H); have he := end_le hz; have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  refine VG.Proof.Hmac.Generic.AArch64.upd_call hH.stream ua fun s₈ a₈ r₈ =>
    ⟨h.call hp hz a₈ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · have := r₈ [] hr hx1
    rwa [List.nil_append, h.kr.pwBytes hp] at this

/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.block H.hkFin) s fun t => KE (H := H) s₀ t ∧
      VG.Proof.Hmac.Generic.AArch64.FinArgs hH.stream t (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀) ∧
      t.gpr .x1 = s₀.gpr .x1 ∧ hH.SH.Repr t.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hl := layout (H := H); have he := end_le hz; have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hF : H.stream.F = H.P.N := rfl
  simp only [Hash.hkFin]
  refine wp_addImm (by omega) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_addImm (by omega) fun s₃ u₃ =>
    wp_mov fun s₄ u₄ => WP.block_nil ?_
  have k₄ := (((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)
  refine ⟨k₄, ?_, by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x20],
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hr⟩
  exact
    { x0 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x2 := by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      x3 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₄.kr (by omega)
        · exact cov_part hp k₄.kr (by omega)
        · exact cov_low hp k₄.kr (by omega)
      st_o := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      st_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix hWb)
      o_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix hWb)
      sp16 := by rw [k₄.kr.sp]; exact hp.sp16
      stk_st := stk_sc hp k₄.kr (part_sub (by omega))
      stk_o := stk_sc hp k₄.kr (part_sub (by omega))
      stk_sc := stk_sc hp k₄.kr (Region.sub_prefix (by omega)) }

theorem hk6_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s)
    (fa : VG.Proof.Hmac.Generic.AArch64.FinArgs hH.stream s (A s₀ H.stWO) (A s₀ H.hkO) (scr s₀))
    (hx1 : s.gpr .x1 = s₀.gpr .x1) (hr : hH.SH.Repr s.mem (A s₀ H.stWO) (bytesAt s₀.mem (pw s₀) (pwl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => KE (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  have hl := layout (H := H); have he := end_le hz; have hWb := hH.wb_le; have hD := hz.z.DN
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have hF : H.stream.F = H.P.N := rfl
  refine VG.Proof.Hmac.Generic.AArch64.fin_call hH.stream fa fun s₁₃ a₁₃ r₁₃ =>
    ⟨h.call hp hz a₁₃ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · rw [bytesAt_take _ _ (show H.D ≤ H.stream.F by omega)]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .x1).isLt)
      (by rw [hx1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

omit hp in
theorem hk7_ok {s : State} (h : KE (H := H) s₀ s) :
    WP isa (.block H.hkKey) s fun t =>
      KE (H := H) s₀ t ∧ t.gpr .x2 = A s₀ H.hkO ∧ (t.gpr .x3).toNat = H.D ∧ t.mem = s.mem := by
  have hl := layout (H := H); have he := end_le hz; have hD := hz.z.DN; have hN := hz.N
  simp only [Hash.hkKey]
  refine wp_addImm (by omega) fun s₁ u₁ => wp_movz fun s₂ u₂ => WP.block_nil ?_
  exact ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.kr.x23],
    by rw [u₂.gpr, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show H.D < 2 ^ 16 by omega), Nat.mod_eq_of_lt (show H.D < 2 ^ 64 by omega)],
    by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = A s₀ H.hkO ∧ (t.gpr .x3).toNat = H.D ∧
      bytesAt t.mem (A s₀ H.hkO) H.D = hH.SH.H.hash (bytesAt s₀.mem (pw s₀) (pwl s₀)) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (hk1_ok hz h) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hp hz hH k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hp hz hH k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok hz k₆) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

end

/-! ## The key -/

/-- Where the key is, and its length. -/
abbrev kp (H : Hash) (s₀ : State) : Addr := if pwl s₀ < H.P.B + 1 then pw s₀ else A s₀ H.hkO
abbrev kl (H : Hash) (s₀ : State) : Nat := if pwl s₀ < H.P.B + 1 then pwl s₀ else H.D

/-- The key HMAC's `init` gets: the password, or the digest of a password
longer than a block, in `scratch`; either gives the same `K₀`. -/
structure KeyAt (hH : HashOK H) (s₀ : State) (m : Mem) (kp : Addr) (kl : Nat) : Prop where
  loc : (kp = pw s₀ ∧ kl = pwl s₀) ∨ (kp = A s₀ H.hkO ∧ kl = H.D)
  le : kl ≤ H.P.B
  k0 : blockKey hH.SH.H (bytesAt m kp kl) = blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- `K₀`, the password as a key. -/
abbrev K0 (hH : HashOK H) (s₀ : State) : List Byte := blockKey hH.SH.H (bytesAt s₀.mem (pw s₀) (pwl s₀))

/-- HMAC's states in `scratch`: `K₀ ⊕ ipad`, `K₀ ⊕ opad`, and `K₀ ⊕ ipad`
after the salt. -/
structure States (hH : HashOK H) (s₀ : State) (m : Mem) : Prop where
  i : hH.SH.Repr m (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad)
  o : hH.SH.Repr m (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)
  s : hH.SH.Repr m (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad ++ bytesAt s₀.mem (salt s₀) (sl s₀))

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : PSizes H)
include hp hz

omit hz in
theorem short_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hs : pwl s₀ < H.P.B + 1) :
    WP isa (.block Hash.short) s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧
      (t.gpr .x3).toNat = kl H s₀ ∧ KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have e₁ : kp H s₀ = pw s₀ := ite_eq_left_of_eq_true _ _ (eq_true hs)
  have e₂ : kl H s₀ = pwl s₀ := ite_eq_left_of_eq_true _ _ (eq_true hs)
  rw [e₁, e₂]
  simp only [Hash.short]
  refine wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => WP.block_nil ?_
  refine ⟨(h.upd u₁ (by decide)).upd u₂ (by decide), by rw [u₂.other _ (by decide), u₁.gpr, h.x19],
    by rw [u₂.gpr, u₁.other _ (by decide), h.x20], ⟨.inl ⟨rfl, rfl⟩, by omega, ?_⟩⟩
  rw [u₂.mem, u₁.mem, h.kr.pwBytes hp]

theorem long_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hs : ¬ pwl s₀ < H.P.B + 1) :
    WP isa H.hashKey s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧
      (t.gpr .x3).toNat = kl H s₀ ∧ KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hD := hz.z.DN; have := hz.z.pad
  have e₁ : kp H s₀ = A s₀ H.hkO := ite_eq_right_of_eq_false _ _ (eq_false hs)
  have e₂ : kl H s₀ = H.D := ite_eq_right_of_eq_false _ _ (eq_false hs)
  rw [e₁, e₂]
  refine WP.mono (hashKey_ok hp hz hH h) fun t ⟨k, x2, x3, hb⟩ =>
    ⟨k, x2, x3, ⟨.inr ⟨rfl, rfl⟩, by omega, ?_⟩⟩
  rw [hb, blockKey_hash hH (by rw [bytesAt_length]; omega)]

omit hp in
/-- The value of `x9` the key's first branch tests. -/
theorem key_shr {s : State} (h : KE (H := H) s₀ s) {s₁ : State}
    (u : Upd s s₁ .x9 (s.gpr .x20 >>> Nat.log2 H.P.B)) :
    isa.eval (.zero .x .x9) s₁ = some (decide (pwl s₀ < H.P.B)) := by
  change eval (.zero .x .x9) s₁ = _
  rw [eval_zero, u.gpr, h.x20, shr_beq_zero, (log2_B hz).1]

omit hp hz in
/-- The value of `x9` the key's second branch tests. -/
theorem key_sub {s : State} (h : KE (H := H) s₀ s) {s₂ : State}
    (u : Upd s s₂ .x9 (s.gpr .x20 - BitVec.ofNat 64 H.P.B)) (hB : H.P.B < 2 ^ 64) :
    isa.eval (.zero .x .x9) s₂ = some (decide (pwl s₀ = H.P.B)) := by
  change eval (.zero .x .x9) s₂ = _
  have ex : s₀.gpr .x1 = BitVec.ofNat 64 (pwl s₀) := by simp
  rw [eval_zero, u.gpr, h.x20, ex, sub_beq (s₀.gpr .x1).isLt hB]

theorem key_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) :
    WP isa H.key s fun t => KE (H := H) s₀ t ∧ t.gpr .x2 = kp H s₀ ∧ (t.gpr .x3).toNat = kl H s₀ ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hB := hz.B_le
  unfold Hash.key Hash.keyShr Hash.keySub
  refine WP.seq (wp_lsr (log2_B hz).2 fun s₁ u₁ => WP.block_nil ?_)
  have k₁ := h.upd u₁ (by decide)
  refine WP.ite _ (key_shr hz h u₁) (fun hT => short_ok hp hH k₁ (by have := of_decide_eq_true hT; omega))
    fun hF => ?_
  refine WP.seq (wp_subImm (by omega) fun s₂ u₂ => WP.block_nil ?_)
  have k₂ := k₁.upd u₂ (by decide)
  refine WP.ite _ (key_sub k₁ u₂ (by omega)) (fun hT => short_ok hp hH k₂ (by
    have := of_decide_eq_true hT; omega)) fun hF' => long_ok hp hz hH k₂ (by
      have := of_decide_eq_false hF; have := of_decide_eq_false hF'; omega)

/-! ## HMAC's states -/

omit hp in
theorem States.keep (hH : HashOK H) {m m' : Mem} (h : States hH s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ H.st0O (3 * H.S)) r) : States hH s₀ m' := by
  have hl := layout (H := H); have he := end_le hz
  exact ⟨repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (Nat.le_refl _) (by omega))) h.i,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) h.o,
    repr_keep hH hf (fun r hr => (hd r hr).sub_left (Offset.sub _ (by omega) (by omega))) h.s⟩

/-- The key's region: where HMAC's `init` may read it. -/
theorem KeyAt.facts (hH : HashOK H) {m : Mem} {kp : Addr} {kl : Nat} (hk : KeyAt hH s₀ m kp kl) {s : State}
    (h : KR (H := H) s₀ s) :
    Covers [⟨kp, kl⟩] (s.rd ++ s.wr) ∧ Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st0O, H.S⟩ ∧
      Region.Disjoint ⟨kp, kl⟩ ⟨A s₀ H.st1O, H.S⟩ ∧ Region.Disjoint ⟨kp, kl⟩ (lowR (H := H) s₀) ∧
      (below s.sp 16).Disjoint ⟨kp, kl⟩ := by
  have hl := layout (H := H); have he := end_le hz; have hD := hz.z.DN; have hN := hz.N
  rcases hk.loc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨covers_one (List.mem_append_left _ (by rw [h.rd, hp.rd]; simp)),
      hp.pw_s.sub_right (part_sub (by omega)), hp.pw_s.sub_right (part_sub (by omega)),
      hp.pw_s.sub_right low_sub, by rw [h.sp]; exact hp.stk_pw⟩
  · refine ⟨Covers.of_sub fun r hr => ?_, part_disj hz (Or.inr (by omega)) (by omega) (by omega),
      part_disj hz (Or.inr (by omega)) (by omega) (by omega), low_disj hz (by omega) (by omega),
      stk_sc hp h (part_sub (by omega))⟩
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨r', h', off, e, l⟩ := cov_part hp h (o := H.hkO) (n := H.D) (by omega)
    exact ⟨r', List.mem_append_right _ h', off, e, l⟩

/-- HMAC's `init`'s arguments: its two states and the key. -/
theorem su1_ok (hH : HashOK H) {s : State} (h : KE (H := H) s₀ s) (hx2 : s.gpr .x2 = kp H s₀)
    (hx3 : (s.gpr .x3).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.block H.initArgs) s fun t => KE (H := H) s₀ t ∧
      InitArgs (H := H) t (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀) ∧
      KeyAt hH s₀ t.mem (kp H s₀) (kl H s₀) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz
  have hsnw := hp.snw
  simp only [Hash.initArgs]
  refine wp_addImm (by omega) fun s₁ u₁ => wp_addImm (by omega) fun s₂ u₂ => wp_mov fun s₃ u₃ =>
    WP.block_nil ?_
  have k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ⟨kc, k_i, k_o, k_s, k_stk⟩ := hk.facts hp hz hH k₃.kr
  refine ⟨k₃, ?_, m₃ ▸ hk⟩
  exact
    { x0 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.kr.x23]
      x1 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.kr.x23]
      x2 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx2]
      x3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx3]
      x4 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.x23]
      klB := hk.le
      cr := kc
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₃.kr (by omega)
        · exact cov_part hp k₃.kr (by omega)
        · exact cov_low hp k₃.kr (by omega)
      i_o := part_disj hz (Or.inl (by omega)) (by omega) (by omega)
      i_s := low_disj hz (by omega) (by omega)
      o_s := low_disj hz (by omega) (by omega)
      k_i := k_i
      k_o := k_o
      k_s := k_s
      sp16 := by rw [k₃.kr.sp]; exact hp.sp16
      stk_i := stk_sc hp k₃.kr (part_sub (by omega))
      stk_o := stk_sc hp k₃.kr (part_sub (by omega))
      stk_k := k_stk
      stk_s := stk_sc hp k₃.kr low_sub
      scnw := by show (scr s₀).toNat + 8 * H.W ≤ 2 ^ 64; omega }

/-- HMAC's `init`: the key's inner and outer states. -/
theorem su2_ok (hH : HashOK H) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.fdepth ≤ 1) {s : State} (h : KE (H := H) s₀ s)
    (ia : InitArgs (H := H) s (A s₀ H.st0O) (A s₀ H.st1O) (kp H s₀) (scr s₀) (kl H s₀))
    (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa (.call H.hmacInitN H.hmacInit) s fun t => KE (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) := by
  have hl := layout (H := H); have he := end_le hz
  refine hinit_call hH hI hId ia fun s₄ a₄ ri₄ ro₄ => ⟨?_, ?_, ?_⟩
  · exact h.call hp hz a₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr ⟨_, _, rfl, Nat.le_refl _, by omega⟩
      · exact .inr ⟨_, _, rfl, by omega, by omega⟩
      · exact .inl ⟨_, rfl, Nat.le_refl _⟩
  · rw [hk.k0] at ri₄; exact ri₄
  · rw [hk.k0] at ro₄; exact ro₄

/-- The inner state copied, and `update`'s arguments: the salt. -/
theorem su3_ok (hH : HashOK H) {s₄ : State} (h : KE (H := H) s₀ s₄)
    (ri₄ : hH.SH.Repr s₄.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro₄ : hH.SH.Repr s₄.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad)) :
    WP isa (.block H.saltArgs) s₄ fun t => KE (H := H) s₀ t ∧
      UpdArgs hH.stream t (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 H.P.B ∧
      hH.SH.Repr t.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad) ∧
      hH.SH.Repr t.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad) ∧
      hH.SH.Repr t.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by
  have hl := layout (H := H); have he := end_le hz; have hL := L_lt hz; have hWb := hH.wb_le
  have hB := hz.B_le; have hN4 := hz.z.N4
  have hB4 : H.P.B % 4 = 0 := by rcases hz.z.B with h | h <;> omega
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  have eS : 4 * (H.S / 4) = H.S := by omega
  simp only [Hash.saltArgs, Hash.copy32]
  refine copy32_ok (src := .x23) (dst := .x23) (by decide) (by decide) H.st0O H.stSO (H.S / 4)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ _ s₄ _
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_rw hp hz h.kr (by omega))
    (fun j hj => by rw [h.kr.x23, add_ofNat]; exact in_sc hp hz h.kr.wr (by omega))
    (by rw [h.kr.x23, eS]; exact (part_disj hz (Or.inl (by omega)) (by omega) (by omega)).sep
          (Region.contains_self _ _) (Region.contains_self _ _))
    fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  rw [h.kr.x23, eS] at m₅
  have f₅ : Frame [sR s₀ H.stSO H.S] s₄.mem s₅.mem := by
    rw [m₅]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have g : ∀ r ∈ eregs, s₅.gpr r = s₄.gpr r := fun r hr => g₅ r (by rintro rfl; revert hr; decide)
  have k₅ : KE (H := H) s₀ s₅ := ⟨h.kr.write hz rd₅ wr₅ sp₅ (fun r hr => g r (kregs_eregs r hr))
      (o := H.stSO) (n := H.S) (by omega) (by omega) f₅,
    by rw [g _ (by simp), h.x19], by rw [g _ (by simp), h.x20], by rw [g _ (by simp), h.x21],
    by rw [g _ (by simp), h.x22]⟩
  have dS : ∀ o, o + H.S ≤ H.stSO → ∀ r ∈ [sR s₀ H.stSO H.S], Region.Disjoint ⟨A s₀ o, H.S⟩ r :=
    fun o ho r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl ho) (by omega) (by omega)
  have ri₅ := repr_keep hH f₅ (dS _ (by omega)) ri₄
  have ro₅ := repr_keep hH f₅ (dS _ (by omega)) ro₄
  have rs₅ : hH.SH.Repr s₅.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad) := by rw [m₅]; exact repr_copy hH ri₄
  refine wp_addImm (by omega) fun s₆ u₆ => wp_movz fun s₇ u₇ => wp_mov fun s₈ u₈ =>
    wp_mov fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ => WP.block_nil ?_
  have k₁₀ := ((((k₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
    (by decide)
  have m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  refine ⟨k₁₀, ?_, ?_, m₁₀ ▸ ri₅, m₁₀ ▸ ro₅, m₁₀ ▸ rs₅⟩
  · exact
      { x0 := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
            u₇.other _ (by decide), u₆.gpr, k₅.kr.x23]
        x2 := by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.x21]
        x3 := by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.x22]
        x4 := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
            u₆.other _ (by decide), k₅.kr.x23]
        cd := covers_one (List.mem_append_left _ (by rw [k₁₀.kr.rd, hp.rd]; simp))
        cw := Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp k₁₀.kr (by omega)
          · exact cov_low hp k₁₀.kr (by omega)
        st_sc := (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix hWb)
        d_st := hp.sa_s.sub_right (part_sub (by omega))
        d_sc := hp.sa_s.sub_right (Region.sub_prefix (by omega))
        sp16 := by rw [k₁₀.kr.sp]; exact hp.sp16
        stk_st := stk_sc hp k₁₀.kr (part_sub (by omega))
        stk_d := by rw [k₁₀.kr.sp]; exact hp.stk_sa
        stk_sc := stk_sc hp k₁₀.kr (Region.sub_prefix (by omega)) }
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show H.P.B < 2 ^ 16 by omega), Nat.mod_eq_of_lt (show H.P.B < 2 ^ 64 by omega)]

/-- `update` with the salt. -/
theorem su4_ok (hH : HashOK H) {s₁₀ : State} (k₁₀ : KE (H := H) s₀ s₁₀)
    (ua : UpdArgs hH.stream s₁₀ (A s₀ H.stSO) (salt s₀) (scr s₀) (sl s₀))
    (hx1 : s₁₀.gpr .x1 = BitVec.ofNat 64 H.P.B)
    (ri : hH.SH.Repr s₁₀.mem (A s₀ H.st0O) (xorPad (K0 hH s₀) ipad))
    (ro : hH.SH.Repr s₁₀.mem (A s₀ H.st1O) (xorPad (K0 hH s₀) opad))
    (rs : hH.SH.Repr s₁₀.mem (A s₀ H.stSO) (xorPad (K0 hH s₀) ipad)) :
    WP isa (.call H.updN H.updC) s₁₀ fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  have hl := layout (H := H); have he := end_le hz; have hWb := hH.wb_le
  have hSS : H.stream.S = H.P.N + H.P.B := rfl
  refine VG.Proof.Hmac.Generic.AArch64.upd_call hH.stream ua fun s₁₁ a₁₁ r₁₁ => ?_
  have k₁₁ := k₁₀.call hp hz a₁₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  have dW : ∀ o, H.st0O ≤ o → o + H.S ≤ H.stSO → ∀ r ∈ [(⟨A s₀ H.stSO, H.stream.S⟩ : Region),
      ⟨scr s₀, hH.stream.Wb⟩] ++ [below s₁₀.sp 16], Region.Disjoint ⟨A s₀ o, H.S⟩ r := fun o ho₀ ho r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact part_disj hz (Or.inl ho) (by omega) (by omega)
      · exact (low_disj hz (by omega) (by omega)).sub_right (Region.sub_prefix hWb)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (stk_sc hp k₁₀.kr (part_sub (by omega))).symm
  refine ⟨k₁₁, ⟨repr_keep hH a₁₁.frame (dW _ (by omega) (by omega)) ri,
    repr_keep hH a₁₁.frame (dW _ (by omega) (by omega)) ro, ?_⟩⟩
  have := r₁₁ _ rs (by rw [hx1, xorPad_length, blockKey_length])
  rwa [k₁₀.kr.saltBytes hp] at this

theorem setup_ok (hH : HashOK H) (hI : Verified AArch64.target H.hmacInit (initG hH.SH H.W))
    (hId : H.hmacInit.fdepth ≤ 1) {s : State} (h : KE (H := H) s₀ s)
    (hx2 : s.gpr .x2 = kp H s₀) (hx3 : (s.gpr .x3).toNat = kl H s₀) (hk : KeyAt hH s₀ s.mem (kp H s₀) (kl H s₀)) :
    WP isa H.setup s fun t => KE (H := H) s₀ t ∧ States hH s₀ t.mem := by
  unfold Hash.setup
  refine WP.seq (WP.mono (su1_ok hp hz hH h hx2 hx3 hk) fun s₁ ⟨k₁, a₁, h₁⟩ => ?_)
  refine WP.seq (WP.mono (su2_ok hp hz hH hI hId k₁ a₁ h₁) fun s₂ ⟨k₂, i₂, o₂⟩ => ?_)
  refine WP.seq (WP.mono (su3_ok hp hz hH k₂ i₂ o₂) fun s₃ ⟨k₃, a₃, x₃, i₃, o₃, r₃⟩ => ?_)
  exact su4_ok hp hz hH k₃ a₃ x₃ i₃ o₃ r₃

end

end VG.Proof.Pbkdf2.Md.AArch64.Pbk
