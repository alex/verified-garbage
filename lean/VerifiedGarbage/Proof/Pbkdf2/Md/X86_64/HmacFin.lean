import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.HmacFinInner

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `finalize`

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86_64.lean`) starts by finalizing the
inner state into `scratch` (`Proof/Pbkdf2/Md/X86_64/HmacFinInner.lean`);
then it computes the outer hash with one compression, as `iterate`
does (`Proof/Pbkdf2/X86_64/Iterate.lean`): it writes the outer hash value over
the inner state's and, into its buffer, the inner digest and the padding
(`finMid`, `mid_ok`), compresses that block (`cmp_ok`) and writes the digest
of the result to `out` (`finOut`, `out_ok`). That this is the outer hash is
`Md.Link.hash_block`. Everything up to the inner digest is
`HmacFinInner.lean`'s, for the hash function's streaming functions
(`HashOK.stream`); constant time likewise, from the taint checks of the pieces between the calls
(`Checks`) and the compression function's own proof (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacFin

open VG.X86_64 VG.Proof.MdStream
open VG.Proof.MdStream.X86_64 (add_ofNat sx_ofNat wp_mov wp_addi CallOk compressAt_ok compressAt_rel)
open VG.Impl.MdStream.X86_64 (compressAt)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.X86_64 (padLen_ok)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (finG FinArgs rel_taint rel_wp fin_rel restore_ok SavedRegs saveR repr_keep
  PubEq args)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

/-- The registers the code after the inner digest keeps public: `inner`,
the block (its buffer), `out`, `scratch` and the stack pointer. -/
abbrev oregs : List Reg := [.rbx, .rbp, .r13, .r15, .rsp]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.stream.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (fin1Block H.stream)) hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (Taint.check taint (Taint.ofRegs oregs) (.block H.finOut) hc).isSome = true

/-- The block: the inner state's buffer. -/
abbrev blk (H : Hash) (s₀ : State) : Addr := inn s₀ + BitVec.ofNat 64 H.P.N

/-- What holds from the outer block on: as `KR`, but `outer` is no longer
needed. -/
structure KO (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = inn s₀
  r13 : s.gpr .r13 = op s₀
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.stream (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

theorem KO.keep {s₀ s s' : State} (h : KO H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r13, .r15, .rsp], s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.stream (scr s₀)).Disjoint r)
    (hr : ∀ r ∈ rs, (retR s₀).Disjoint r) : KO H s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r13, (hg _ (by simp)).trans h.r15, h.saved.frame H.stream hf hs,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret⟩

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H.stream) sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.D % 4 = 0 ∧ H.P.L % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.D + H.P.L + 4 ≤ H.P.B ∧
    0 < H.D ∧ H.D ≤ H.P.N ∧ H.P.N + H.P.L ≤ H.P.B ∧ H.P.B ≤ 128 ∧ H.P.so + 96 + H.P.N ≤ 8 * sc ∧
    8 * sc ≤ 2 ^ 64 ∧ H.P.N + H.P.B ≤ 256 := by
  have := hH.hN4; have := hH.hD4; have := hH.hL4; have := hH.hDL; have := hH.hD0; have := hH.hDN
  have := hH.hNL; have := hH.B_le; have := hH.hso; have := hp.nw; have := hp.hS
  have : H.P.B % 4 = 0 := by rcases hH.dims.B with h | h <;> omega
  have f : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have hb : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 48 := rfl
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  omega

omit hH hp in
/-- The ranges of the inner state, which holds the hash value and the block. -/
theorem in_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    Region.Sub ⟨inn s₀ + BitVec.ofNat 64 a, n⟩ (inR (H := H.stream) s₀) :=
  Offset.sub_base _ h

omit hH in
theorem save_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    (saveR H.stream (scr s₀)).Disjoint ⟨inn s₀ + BitVec.ofNat 64 a, n⟩ :=
  (hp.i_s.symm.sub_left (save_sub hp)).sub_right (in_inR h)

omit hH in
theorem ret_inR {a n : Nat} (h : a + n ≤ H.P.N + H.P.B) :
    (retR s₀).Disjoint ⟨inn s₀ + BitVec.ofNat 64 a, n⟩ :=
  hp.ret_i.sub_right (in_inR h)

omit hH in
/-- `KO` from `KR`, after code that writes only the inner state. -/
theorem KO.of_kr {s s' : State} (hk : KR (H := H.stream) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r13, .r15, .rsp], s'.gpr r = s.gpr r)
    (hf : Frame [inR (H := H.stream) s₀] s.mem s'.mem) : KO H s₀ s' :=
  KO.keep (s := s) ⟨hk.rd, hk.wr, hk.rsp, hk.rbx, hk.r13, hk.r15, hk.saved, hk.ret⟩ hrd hwr hg hf
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (save_sub hp))
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_i)

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it, and the block's address in `rsi`. -/
theorem mid_ok {s : State} (hk : KR (H := H.stream) s₀ s) :
    WP isa (.block H.finMid) s fun t => KO H s₀ t ∧ t.gpr .rbp = blk H s₀ ∧ t.gpr .rsi = blk H s₀ ∧
      (∀ i < H.P.N, t.mem (inn s₀ + BitVec.ofNat 64 i) = s.mem (outer s₀ + BitVec.ofNat 64 i)) ∧
      bytesAt t.mem (blk H s₀) H.D = bytesAt s.mem (T (H := H.stream) s₀) H.D ∧
      bytesAt t.mem (blk H s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.md.tailPad H.D := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, -, h8, hSB⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have hbuf : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have eN : 4 * (H.P.N / 4) = H.P.N := by omega
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have oR : outerR (H := H.stream) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have tsub : Region.Sub ⟨T (H := H.stream) s₀, H.D⟩ (scR sc s₀) := Offset.sub_base _ (by omega)
  simp only [Hash.finMid, List.append_assoc]
  refine copy32_ok (src := .r12) (dst := .rbx) (by decide) (by decide) 0 0 (H.P.N / 4) _ s _
    (fun j hj => by
      rw [hk.r12, add_ofNat]
      exact ⟨_, oR, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [hk.rbx, add_ofNat, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hk.r12, hk.rbx, eN]
      exact hp.i_o.symm.sep (Offset.contains_base _ (by omega) (by omega))
        (Offset.contains_base _ (by omega) (by omega)))
    (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  rw [hk.r12, hk.rbx, eN, z, z] at m₁
  have r15 : s₁.gpr .r15 = scr s₀ := by rw [g₁ _ (by decide), hk.r15]
  have rbx : s₁.gpr .rbx = inn s₀ := by rw [g₁ _ (by decide), hk.rbx]
  refine copy32_ok (src := .r15) (dst := .rbx) (by decide) (by decide) H.stream.buf H.P.N (H.D / 4) _ s₁ _
    (fun j hj => by
      rw [r15, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
      exact ⟨_, List.mem_append_right _ sR, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [rbx, add_ofNat, wr₁, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [r15, rbx, eD]
      exact hp.i_s.symm.sep (Offset.contains_base _ (by omega) (by omega))
        (Offset.contains_base _ (by omega) (by omega)))
    (by omega) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  rw [r15, rbx, eD] at m₂
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ => ?_
  have rbp₄ : s₄.gpr .rbp = blk H s₀ := by
    rw [u₄.gpr, u₃.gpr, g₂ _ (by decide), rbx, sx_ofNat (by omega)]
  have G₄ : ∀ r, r ≠ .rax → r ≠ .rbp → s₄.gpr r = s₁.gpr r := fun r h1 h2 => by
    rw [u₄.other r h2, u₃.other r h2, g₂ r h1]
  refine padLen_ok hH.shape (hH.lenOk _ (by omega)) hD4 hL4 hB4 (by omega) hB (s := s₄) rbp₄
    (by rw [G₄ _ (by decide) (by decide), rbx, add_ofNat,
      show H.P.N + (H.P.B - H.P.L) = H.P.N + H.P.B - H.P.L by omega])
    (fun a n h' => by
      rw [u₄.wr, u₃.wr, wr₂, wr₁, hk.wr, add_ofNat]
      exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩) fun s₅ g₅ rd₅ wr₅ f₅ p₅ d₅ => ?_
  refine wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have G : ∀ r, r ≠ .rax → r ≠ .rbp → r ≠ .r12 → r ≠ .rsi → s₆.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₆.other r h4, g₅ r h1 h3, G₄ r h1 h2, g₁ r h1]
  have hm : s₆.mem = s₅.mem := u₆.mem
  -- What each piece writes.
  have f₁ : Frame [⟨inn s₀, H.P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₂ : Frame [⟨blk H s₀, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  rw [f₄] at f₅ d₅
  have fI : Frame [inR (H := H.stream) s₀] s.mem s₆.mem := by
    rw [hm]
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₅.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, in_inR (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, in_inR (by omega)⟩
  refine ⟨KO.of_kr hp hk (by rw [u₆.rd, rd₅, u₄.rd, u₃.rd, rd₂, rd₁])
      (by rw [u₆.wr, wr₅, u₄.wr, u₃.wr, wr₂, wr₁])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact G _ (by decide) (by decide) (by decide) (by decide)) fI,
    by rw [u₆.other _ (by decide), g₅ _ (by decide) (by decide), rbp₄],
    by rw [u₆.gpr, g₅ _ (by decide) (by decide), rbp₄], fun i hi => ?_, ?_, by rw [hm]; exact p₅⟩
  · -- The hash value: the outer one, which the later pieces keep.
    have hd : ∀ {a n : Nat}, H.P.N ≤ a → a + n ≤ H.P.N + H.P.B →
        ∀ r ∈ [(⟨inn s₀ + BitVec.ofNat 64 a, n⟩ : Region)], Region.Disjoint ⟨inn s₀, H.P.N⟩ r := fun ha hn => by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.base_disjoint _ ha (by omega)
    rw [hm, f₅.bytes (R := ⟨inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega)) (by show H.P.N ≤ 2 ^ 64; omega) hi,
      f₂.bytes (R := ⟨inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega)) (by show H.P.N ≤ 2 ^ 64; omega) hi,
      m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ hi]
  · -- The inner digest.
    rw [hm, d₅, m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    exact bytes_keep f₁ (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.sub_right tsub).symm.sub_right (Region.sub_prefix (by omega))) (by omega)

/-- What the call of the compression function needs. -/
theorem callOk {t : State} (hk : KO H s₀ t) (hsi : t.gpr .rsi = blk H s₀) :
    CallOk H.P t (inn s₀) (scr s₀) (blk H s₀) := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := sizes hH hp
  have := hH.hso
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have z : inn s₀ + BitVec.ofNat 64 0 = inn s₀ := BitVec.add_zero _
  have hv : Region.Sub ⟨inn s₀, H.P.N⟩ (inR (H := H.stream) s₀) := Region.sub_prefix (by omega)
  have hb : Region.Sub ⟨blk H s₀, H.P.B⟩ (inR (H := H.stream) s₀) := in_inR (by omega)
  have hs : Region.Sub ⟨scr s₀, H.P.so⟩ (scR sc s₀) := Region.sub_prefix (by omega)
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega) (by omega)
  refine ⟨hk.rbx, hk.r15, hsi, (hp.i_s.sub_left hv).sub_right hs, Offset.disjoint_base _ (Nat.le_refl _) (by omega),
    (hp.i_s.sub_left hb).sub_right hs, (hp.stk_i.sub_left b8).sub_right hv, (hp.stk_s.sub_left b8).sub_right hs,
    (hp.stk_i.sub_left b8).sub_right hb, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ iR, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, iR, 0, z.symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega⟩

/-- The compression of the block into the hash value. -/
theorem cmp_ok {t : State} (hk : KO H s₀ t) (hsi : t.gpr .rsi = blk H s₀) {Q : State → Prop}
    (k : ∀ s', KO H s₀ s' → s'.gpr .rbp = t.gpr .rbp →
      hH.md.stateAt s'.mem (inn s₀) = hH.md.compress (hH.md.stateAt t.mem (inn s₀))
        (hH.md.blockAt t.mem (blk H s₀)) → Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := sizes hH hp
  have := hH.hso
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have z : inn s₀ + BitVec.ofNat 64 0 = inn s₀ := BitVec.add_zero _
  refine compressAt_ok hH.md hH.comp (callOk hH hp hk hsi) (by omega) (by omega)
    fun s' hrd hwr hcs hfr hst _ _ => k s' (hk.keep hrd hwr (fun r hr => hcs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) hfr ?_ ?_)
    (hcs _ (by simp [calleeSaved])) hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · have := save_inR hp (a := 0) (n := H.P.N) (by omega); rwa [z] at this
    · exact (cal_save hH.stream hp).symm.sub_right (Region.sub_prefix (by show H.P.so ≤ H.P.so + 48; omega))
    · rw [hk.rsp]
      exact (hp.stk_s.symm.sub_left (save_sub hp)).sub_right (Offset.sub_below _ (by omega) (by omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_i.sub_right (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by omega))
    · rw [hk.rsp]; exact (stk_ret (s₀ := s₀)).symm.sub_right (Offset.sub_below _ (by omega) (by omega))

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : KO H s₀ s) (hbp : s.gpr .rbp = blk H s₀) :
    WP isa (.block H.finOut) s fun s' => ∃ t, KO H s₀ t ∧
      bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D ∧ s'.mem = t.mem ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = t.gpr r) := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := sizes hH hp
  have hD := hp.hD
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have hdl := hH.md.digest_length (hH.md.stateAt s.mem (inn s₀))
  have hL : 8 * H.stream.W + 48 ≤ 8 * sc := by
    have : H.stream.buf = 8 * H.stream.W + 48 := rfl
    have := hp.fits
    omega
  have fin : ∀ t, KO H s₀ t → bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D →
      WP isa (.block H.stream.restore) t fun s' => ∃ t, KO H s₀ t ∧
        bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D ∧ s'.mem = t.mem ∧
        (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
        (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = t.gpr r) := fun t kt bt =>
    WP.mono (restore_ok H.stream kt.r15 hp.hW kt.saved (by rw [kt.wr]; exact sR) hL)
      fun s' ⟨hm, _, _, hg, ho⟩ => ⟨t, kt, bt, hm, hg, ho⟩
  have rbx_in : InRegions (s.rd ++ s.wr) (s.gpr .rbx) H.P.N := by
    have := Offset.contains_base (inn s₀) (d := 0) (n := H.P.N) (k := H.P.N + H.P.B) (by omega) (by omega)
    rw [z] at this
    rw [hk.rbx, hk.rd, hk.wr]
    exact ⟨_, List.mem_append_right _ iR, this⟩
  unfold Hash.finOut
  by_cases hDN' : H.D < H.P.N
  · simp only [hDN', ↓reduceIte, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (hH.shape.out s rbx_in (by
        rw [hbp, hk.wr]; exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩)
      (by rw [hk.rbx, hbp]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)))
      fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
    rw [hbp, hk.rbx] at m₁
    have f₁ : Frame [⟨blk H s₀, H.P.N⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    have k₁ : KO H s₀ s₁ := hk.keep rd₁ wr₁ (fun r hr => g₁ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)) f₁
      (by simp only [List.mem_singleton]; rintro r rfl; exact save_inR hp (by omega))
      (by simp only [List.mem_singleton]; rintro r rfl; exact ret_inR hp (by omega))
    have b₁ : bytesAt s₁.mem (blk H s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D := by
      rw [bytesAt_take _ _ (Nat.le_of_lt hDN'), m₁, bytesAt_writeBytes_self' hdl (by omega)]
    have rbp₁ : s₁.gpr .rbp = blk H s₀ := by rw [g₁ _ (by decide), hbp]
    refine copy32_ok (src := .rbp) (dst := .r13) (by decide) (by decide) 0 0 (H.D / 4) _ s₁ _
      (fun j hj => by
        rw [rbp₁, add_ofNat, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
        exact ⟨_, List.mem_append_right _ iR, Offset.contains_base _ (by omega) (by omega)⟩)
      (fun j hj => by
        rw [k₁.r13, add_ofNat, k₁.wr]
        exact ⟨_, pR, Offset.contains_base _ (by show 0 + 4 * j + 4 ≤ H.D; omega) (by omega)⟩)
      (by
        rw [rbp₁, k₁.r13, eD, add_ofNat]
        exact hp.i_p.sep (Offset.contains_base _ (by omega) (by omega))
          (Offset.contains_base _ (by show 0 + H.D ≤ H.D; omega) (by omega)))
      (by omega) fun s₂ g₂ rd₂ wr₂ m₂ => ?_
    rw [rbp₁, k₁.r13, eD, z, z] at m₂
    refine fin s₂ (k₁.keep rd₂ wr₂ (fun r hr => g₂ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide))
      (m₂ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [bytesAt_length]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_p)) ?_
    rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), b₁]
  · have eDN : H.D = H.P.N := by omega
    simp only [hDN', ↓reduceIte, List.cons_append]
    refine wp_mov fun s₁ u₁ _ _ => ?_
    rw [WP.block_append_iff]
    have rbx₁ : s₁.gpr .rbx = inn s₀ := by rw [u₁.other _ (by decide), hk.rbx]
    refine WP.mono (hH.shape.out s₁ (by rw [u₁.rd, u₁.wr, u₁.other _ (by decide)]; exact rbx_in) (by
        rw [u₁.gpr, hk.r13, u₁.wr, hk.wr, ← eDN]; exact ⟨_, pR, Region.contains_self _ _⟩)
      (by rw [rbx₁, u₁.gpr, hk.r13, ← eDN]; exact hp.i_p.sub_left (Region.sub_prefix (by omega))))
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    rw [rbx₁, u₁.gpr, hk.r13, u₁.mem] at m₂
    refine fin s₂ (hk.keep (rd₂.trans u₁.rd) (wr₂.trans u₁.wr) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> rw [g₂ _ (by decide), u₁.other _ (by decide)])
      (m₂ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [hdl, ← eDN]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_p)) ?_
    rw [m₂, eDN, bytesAt_writeBytes_self' hdl (by omega), List.take_of_length_le (by omega)]

/-! ## Correctness -/

theorem correct : WP isa H.hmacFin s₀ fun s' => gprPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  obtain ⟨hN4, hD4, hL4, hB4, hDL, hD0, hDN, hNL, hB, hf, h8, hSB⟩ := sizes hH hp
  have hB0 := hH.B_pos
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨k₁, di₁, dx₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hH.stream hp k₁ di₁ dx₁) fun t₁ ⟨kt₁, a₁, si₁, m₁⟩ =>
    finCall_ok hH.stream hp kt₁ a₁ fun s₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (mid_ok hH hp k₂) fun s₃ ⟨k₃, bp₃, si₃, i₃, b₃, p₃⟩ => ?_)
  refine WP.seq (cmp_ok hH hp k₃ si₃ fun s₄ k₄ bp₄ e₄ => ?_)
  refine WP.mono (out_ok hH hp k₄ (bp₄.trans bp₃)) fun s' ⟨s₅, k₅, m₅, hm, hg, ho⟩ =>
    ⟨⟨fun r hr => ?_, by rw [hm, k₅.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hH.hB] at hk0 hcnt
  have hl0 : (xorPad k0 ipad ++ text).length = H.P.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until the inner digest is written.
  have oI : ∀ r ∈ [saveR H.stream (scr s₀)], Region.Disjoint (outerR (H := H.stream) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (save_sub hp)
  have o₂ : ∀ r ∈ [inR (H := H.stream) s₀, tR (H := H.stream) s₀, calR hH.stream s₀,
      stkR s₀], Region.Disjoint (outerR (H := H.stream) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (t_sub hp)
    · exact hp.o_s.sub_right (cal_sub hH.stream hp)
    · exact hp.stk_o.symm
  have rO₂ := repr_keep hH.stream f₂ o₂ (m₁ ▸ repr_keep hH.stream f₁ oI hrO)
  -- The inner digest.
  have dig : (bytesAt s₂.mem (T (H := H.stream) s₀) H.P.N).take H.D = hH.SH.H.hash (xorPad k0 ipad ++ text) :=
    d₂ _ (m₁ ▸ repr_keep hH.stream f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [si₁, hcnt, hl0])
  -- The outer hash: one compression of the outer hash value.
  have hxl : (xorPad k0 opad).length = H.P.B := by rw [xorPad_length, hk0]
  have ho : hH.md.stateAt s₃.mem (inn s₀) = hH.md.compressList hH.iv (xorPad k0 opad) 1 := by
    rw [hH.reloc s₂.mem s₃.mem (outer s₀) (inn s₀) i₃]
    exact Md.stateAt_of_repr hB0 hxl ((hH.repr _ _ _).1 rO₂)
  show bytesAt s'.mem (op s₀) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hH.hD, hm, m₅, e₄, ho, hH.md.blockAt_eq (by omega) p₃, b₃, hmacBlockKey, ← dig,
    ← bytesAt_take _ _ hDN, hH.iterOk.link.hash_block hxl (bytesAt_length _ _ _)]

end

/-! ## Constant time -/

section

variable {sc : Nat} {s₀ s₀' : State} (hp : Pre (H := H.stream) sc s₀) (hp' : Pre (H := H.stream) sc s₀')
  (hq : PubEq s₀ s₀')

omit hH in
/-- The registers `oregs` agree in two runs. -/
theorem ko_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KO H s₀ s ∧ s.gpr .rbp = blk H s₀)
    (h' : KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀') : ∀ r ∈ oregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.1.rbx, h'.1.rbx, inn, inn, hq.rdi]
  · rw [h.2, h'.2, blk, blk, inn, inn, hq.rdi]
  · rw [h.1.r13, h'.1.r13, op, op, hq.rcx]
  · rw [h.1.r15, h'.1.r15, scr, scr, hq.r8]
  · rw [h.1.rsp, h'.1.rsp, hq.rsp]

include hH hp hp' hq

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.stream.finPrologue)
      fun s s' => (KR (H := H.stream) s₀ s ∧ s.gpr .rdi = inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx) ∧
        (KR (H := H.stream) s₀' s' ∧ s'.gpr .rdi = inn s₀' ∧ s'.gpr .rdx = s₀'.gpr .rdx) :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  have fin1 := fin_rel' hH.stream hp hp' hq (c := s₀.gpr .rdx)
    (F := fun s => KR (H := H.stream) s₀ s ∧ s.gpr .rdi = inn s₀ ∧ s.gpr .rdx = s₀.gpr .rdx)
    (F' := fun s => KR (H := H.stream) s₀' s ∧ s.gpr .rdi = inn s₀' ∧ s.gpr .rdx = s₀'.gpr .rdx) hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH.stream hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH.stream hp' k d x) fun _ ⟨k, a, si, m⟩ =>
      ⟨k, a, si.trans hq.rdx.symm, m⟩)
  have mid : RelCT isa (fun s s' => KR (H := H.stream) s₀ s ∧ KR (H := H.stream) s₀' s') (.block H.finMid)
      fun s s' => (KO H s₀ s ∧ s.gpr .rbp = blk H s₀ ∧ s.gpr .rsi = blk H s₀) ∧
        (KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀' ∧ s'.gpr .rsi = blk H s₀') :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.mid
      (fun s k => WP.mono (mid_ok hH hp k) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
      (fun s k => WP.mono (mid_ok hH hp' k) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)
  have cmp : RelCT isa (fun s s' => (KO H s₀ s ∧ s.gpr .rbp = blk H s₀ ∧ s.gpr .rsi = blk H s₀) ∧
        (KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀' ∧ s'.gpr .rsi = blk H s₀')) (compressAt H.compN H.compC)
      fun s s' => (KO H s₀ s ∧ s.gpr .rbp = blk H s₀) ∧ (KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀') :=
    rel_wp (compressAt_rel hH.md hH.comp fun s s' ⟨⟨k, _, si⟩, ⟨k', _, si'⟩⟩ =>
        ⟨⟨_, _, _, callOk hH hp k si⟩, ⟨_, _, _, callOk hH hp' k' si'⟩,
          by rw [k.rbx, k'.rbx, inn, inn, hq.rdi], by rw [k.r15, k'.r15, scr, scr, hq.r8],
          by rw [si, si', blk, blk, inn, inn, hq.rdi], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
      (fun s ⟨k, bp, si⟩ => cmp_ok hH hp k si fun s' k' bp' _ => ⟨k', bp'.trans bp⟩)
      (fun s ⟨k, bp, si⟩ => cmp_ok hH hp' k si fun s' k' bp' _ => ⟨k', bp'.trans bp⟩)
  obtain ⟨_, hr⟩ := hc.out
  have out : RelCT isa (fun s s' => (KO H s₀ s ∧ s.gpr .rbp = blk H s₀) ∧ (KO H s₀' s' ∧ s'.gpr .rbp = blk H s₀'))
      (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs oregs) (fun _ _ h => Taint.agree_ofRegs (ko_agree hq h.1 h.2)) hr
  exact pro.seq (fin1.seq (mid.seq (cmp.seq out)))

end

/-- HMAC's `finalize` is verified against `finG`, given the taint checks and
the facts about its code that the kernel checks for each hash function. -/
theorem verified {sc : Nat} (hc : Checks H) (hfit : H.stream.buf + H.stream.F ≤ 8 * sc)
    (hmx : H.hmacFin.allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified X86_64.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH.stream sc hs hfit)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH.stream sc h₁ hfit) (pre_of hH.stream sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.HmacFin
