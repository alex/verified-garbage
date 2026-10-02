import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Instances

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `finalize`

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/HmacFin.lean`): HMAC's `finalize`
(`Impl/Pbkdf2/Md/AArch64.lean`) starts as the generic one
(`Proof/Hmac/Generic/AArch64/Finalize.lean`), finalizing the inner state into
`scratch`; then it computes the outer hash with one compression, as `iterate`
does (`Proof/Pbkdf2/AArch64/Iterate.lean`): it writes the outer hash value
over the inner state's and, into its buffer, the inner digest and the padding
(`finMid`, `mid_ok`), compresses that block (`cmp_ok`) and writes the digest
of the result to `out` (`finOut`, `out_ok`). That this is the outer hash is
`Md.Link.hash_block`. Everything up to the inner digest is the generic
proof's, for the hash function's streaming functions (`HashOK.stream`);
constant time likewise, from the taint checks of the pieces between the calls
(`Checks`) and the compression function's own proof (`compressAt_rel`).
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacFin

open VG.AArch64 VG.Proof.MdStream
open VG.Proof.MdStream.AArch64 (add_ofNat wp_mov wp_addImm)
open VG.Impl.MdStream.AArch64 (compressAt compressWith mov)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok padLen_ok padLen_keepsV CallOk compressAt_ok compressAt_rel)
open VG.Proof.Hmac.Generic.AArch64 (finG FinArgs rel_taint rel_wp fin_rel restore_ok saveR SavedRegs VecKept
  savedRegs)
open VG.Proof.Hmac.Generic.AArch64.Finalize (Pre KR kregs inn outer op scr T tR calR stkR inR outerR opR scR
  pre_of wr_mem t_sub save_sub cal_sub pro_ok fin1Args_ok finCall_ok fin1Block pubRegs)
open VG.Proof.Hmac.Generic.AArch64.Init (repr_keep PubEq args untouched)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

/-- The registers the code after the inner digest keeps public: `inner`, the
block (its buffer), `scratch` and `out`. -/
abbrev oregs : List Reg := [.x19, .x21, .x23, .x24]

/-- The registers `KO` fixes. -/
abbrev koregs : List Reg := [.x19, .x23, .x24, .x25, .x26, .x27, .x28]

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.stream.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin1Block H.stream)) hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (Taint.check taint (Taint.ofRegs oregs) (.block H.finOut) hc).isSome = true

/-- The block: the inner state's buffer. -/
abbrev blk (H : Hash) (s₀ : State) : Addr := inn s₀ + BitVec.ofNat 64 H.P.N

/-- What holds from the outer block on: as `KR`, but `outer` is no longer
needed, and `out` is in `x24`. -/
structure KO (H : Hash) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = inn s₀
  x23 : s.gpr .x23 = scr s₀
  x24 : s.gpr .x24 = op s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H.stream (scr s₀) s₀ s.mem

theorem untouched_ko : ∀ r ∈ untouched, r ∈ koregs := by decide

theorem KO.keep {s₀ s s' : State} (h : KO H s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ koregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.stream (scr s₀)).Disjoint r) : KO H s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19, (hg _ (by simp)).trans h.x23,
    (hg _ (by simp)).trans h.x24, fun r hr => (hg r (untouched_ko r hr)).trans (h.cs r hr),
    h.saved.frame H.stream hf hs⟩

omit hH in
/-- The end: `abiPreserved`, from `KO` and `restore`. -/
theorem abi_of {s₀ s s' : State} (hk : KO H s₀ s) (hsp : s'.sp = s.sp) (hv : VecKept s₀ s')
    (hg : ∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) (ho : ∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, by rw [hsp, hk.sp], hv⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hg _ (by decide)
    | exact (ho _ (by decide)).trans (hk.cs _ (by decide))

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H.stream) sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.D % 4 = 0 ∧ H.P.L % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.D + 4 ≤ H.P.B - H.P.L ∧
    0 < H.D ∧ H.D ≤ H.P.N ∧ H.P.N + H.P.L ≤ H.P.B ∧ H.P.B ≤ 128 ∧ H.P.so % 8 = 0 ∧
    H.P.so + 104 + H.P.N ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 ∧ H.P.N + H.P.B ≤ 256 ∧ H.P.so + 104 + H.P.N ≤ 4096 := by
  have := hH.sizes.N4; have := hH.sizes.D4; have := hH.sizes.L4; have := hH.sizes.pad; have := hH.sizes.D0
  have := hH.sizes.DN; have := hH.sizes.NL; have := hH.B_le; have := hH.sizes.dims.so; have := hH.N_le
  have := hp.nw; have := hp.hS
  have : H.P.md.so = H.P.so := rfl
  have : H.P.B % 4 = 0 := by rcases hH.sizes.B with h | h <;> omega
  have f : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have hb : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 56 := rfl
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

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it; `x20` = `scratch`, `x24` = `out`, and the
block's address in `x21` and `x1`. -/
theorem mid_ok {s : State} (hk : KR (H := H.stream) s₀ s) :
    WP isa (.block H.finMid) s fun t => KO H s₀ t ∧ t.gpr .x20 = scr s₀ ∧ t.gpr .x21 = blk H s₀ ∧
      t.gpr .x1 = blk H s₀ ∧
      (∀ i < H.P.N, t.mem (inn s₀ + BitVec.ofNat 64 i) = s.mem (outer s₀ + BitVec.ofNat 64 i)) ∧
      bytesAt t.mem (blk H s₀) H.D = bytesAt s.mem (T (H := H.stream) s₀) H.D ∧
      bytesAt t.mem (blk H s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.md.tailPad H.D := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, -, h8, hSB, h4k⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have hbuf : H.stream.buf % 4 = 0 ∧ H.stream.buf + H.P.N ≤ 8 * sc ∧ H.stream.buf + H.P.N ≤ 4096 := by
    have : H.stream.buf = 8 * ((H.P.so + 48) / 8) + 56 := rfl
    have : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
    omega
  clear h4k
  have eN : 4 * (H.P.N / 4) = H.P.N := by omega
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have oR : outerR (H := H.stream) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have tsub : Region.Sub ⟨T (H := H.stream) s₀, H.D⟩ (scR sc s₀) := Offset.sub_base _ (by omega)
  simp only [Hash.finMid, Hash.copy32, List.append_assoc]
  refine copy32_ok (src := .x20) (dst := .x19) (by decide) (by decide) 0 0 (H.P.N / 4) ⟨rfl, by omega⟩
    ⟨rfl, by omega⟩ _ s _
    (fun j hj => by
      rw [hk.x20, add_ofNat]
      exact ⟨_, oR, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [hk.x19, add_ofNat, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [hk.x20, hk.x19, eN]
      exact hp.i_o.symm.sep (Offset.contains_base _ (by omega) (by omega))
        (Offset.contains_base _ (by omega) (by omega)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [hk.x20, hk.x19, eN, z, z] at m₁
  have x23 : s₁.gpr .x23 = scr s₀ := by rw [g₁ _ (by decide), hk.x23]
  have x19 : s₁.gpr .x19 = inn s₀ := by rw [g₁ _ (by decide), hk.x19]
  refine copy32_ok (src := .x23) (dst := .x19) (by decide) (by decide) H.stream.buf H.P.N (H.D / 4)
    ⟨by omega, by omega⟩ ⟨hN4, by omega⟩ _ s₁ _
    (fun j hj => by
      rw [x23, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
      exact ⟨_, List.mem_append_right _ sR, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [x19, add_ofNat, wr₁, hk.wr]
      exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩)
    (by
      rw [x23, x19, eD]
      exact hp.i_s.symm.sep (Offset.contains_base _ (by omega) (by omega))
        (Offset.contains_base _ (by omega) (by omega)))
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  rw [x23, x19, eD] at m₂
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₃ u₃ => wp_addImm (by omega) fun s₄ u₄ => wp_mov fun s₅ u₅ => ?_
  have x21₅ : s₅.gpr .x21 = blk H s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide), x19]
  have G₅ : ∀ r, r ≠ .x9 → r ≠ .x20 → r ≠ .x21 → r ≠ .x24 → s₅.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h2, u₄.other r h3, u₃.other r h4, g₂ r h1]
  refine padLen_ok hH.shape (hH.lenOk _ (by omega)) hD4 hL4 hB4 hpad hB (s := s₅) x21₅
    (by rw [G₅ _ (by decide) (by decide) (by decide) (by decide), x19, add_ofNat,
      show H.P.N + (H.P.B - H.P.L) = H.P.N + H.P.B - H.P.L by omega])
    (fun a n h' => by
      rw [u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hk.wr, add_ofNat]
      exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩) fun s₆ g₆ rd₆ wr₆ sp₆ f₆ p₆ d₆ => ?_
  refine wp_mov fun s₇ u₇ => WP.block_nil ?_
  have G : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x22 → r ≠ .x1 → s₇.gpr r = s₅.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₇.other r h4, g₆ r h1 h2 h3]
  have hm : s₇.mem = s₆.mem := u₇.mem
  have f₁ : Frame [⟨inn s₀, H.P.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₂ : Frame [⟨blk H s₀, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  rw [f₅] at f₆ d₆
  have fI : Frame [inR (H := H.stream) s₀] s.mem s₇.mem := by
    rw [hm]
    refine ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)).trans (f₆.sub fun r hr => ?_) <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, in_inR (by omega)⟩
    · exact ⟨_, List.mem_singleton_self _, in_inR (by omega)⟩
  have Gk : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x22 → r ≠ .x1 → r ≠ .x20 → r ≠ .x21 → r ≠ .x24 →
      s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 => by
    rw [G r h1 h2 h3 h4, G₅ r h1 h5 h6 h7, g₁ r h1]
  have hu : ∀ r ∈ untouched, r ≠ .x9 ∧ r ≠ .x12 ∧ r ≠ .x22 ∧ r ≠ .x1 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x24 := by
    decide
  refine ⟨⟨by rw [u₇.rd, rd₆, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁, hk.rd],
      by rw [u₇.wr, wr₆, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hk.wr],
      by rw [u₇.sp, sp₆, u₅.sp, u₄.sp, u₃.sp, sp₂, sp₁, hk.sp],
      by rw [Gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hk.x19],
      by rw [Gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hk.x23],
      by rw [G _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, g₂ _ (by decide), g₁ _ (by decide), hk.x21],
      fun r hr => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hu r hr
        rw [Gk r h1 h2 h3 h4 h5 h6 h7, hk.cs r hr],
      hk.saved.frame H.stream fI (by
        simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (save_sub hp))⟩,
    by rw [G _ (by decide) (by decide) (by decide) (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hk.x23],
    by rw [G _ (by decide) (by decide) (by decide) (by decide), x21₅],
    by rw [u₇.gpr, g₆ _ (by decide) (by decide) (by decide), x21₅], fun i hi => ?_, ?_, by rw [hm]; exact p₆⟩
  · -- The hash value: the outer one, which the later pieces keep.
    have hd : ∀ {a n : Nat}, H.P.N ≤ a → a + n ≤ H.P.N + H.P.B →
        ∀ r ∈ [(⟨inn s₀ + BitVec.ofNat 64 a, n⟩ : Region)], Region.Disjoint ⟨inn s₀, H.P.N⟩ r := fun ha hn => by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.base_disjoint _ ha (by omega)
    rw [hm, f₆.bytes (R := ⟨inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega)) (by show H.P.N ≤ 2 ^ 64; omega) hi,
      f₂.bytes (R := ⟨inn s₀, H.P.N⟩) (hd (Nat.le_refl _) (by omega)) (by show H.P.N ≤ 2 ^ 64; omega) hi,
      m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ hi]
  · -- The inner digest.
    rw [hm, d₆, m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    exact bytes_keep f₁ (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.sub_right tsub).symm.sub_right (Region.sub_prefix (by omega))) (by omega)

/-- What the call of the compression function needs. -/
theorem callOk {t : State} (hk : KO H s₀ t) (h20 : t.gpr .x20 = scr s₀) (h1 : t.gpr .x1 = blk H s₀) :
    CallOk t H.P.N H.P.B H.P.so (inn s₀) (scr s₀) (blk H s₀) := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have z : inn s₀ + BitVec.ofNat 64 0 = inn s₀ := BitVec.add_zero _
  have hv : Region.Sub ⟨inn s₀, H.P.N⟩ (inR (H := H.stream) s₀) := Region.sub_prefix (by omega)
  have hb : Region.Sub ⟨blk H s₀, H.P.B⟩ (inR (H := H.stream) s₀) := in_inR (by omega)
  have hs : Region.Sub ⟨scr s₀, H.P.so⟩ (scR sc s₀) := Region.sub_prefix (by omega)
  refine ⟨hk.x19, h20, h1, (hp.i_s.sub_left hv).sub_right hs, Offset.disjoint_base _ (Nat.le_refl _) (by omega),
    (hp.i_s.sub_left hb).sub_right hs, ?_, ?_⟩
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
theorem cmp_ok {t : State} (hk : KO H s₀ t) (h20 : t.gpr .x20 = scr s₀) (h1 : t.gpr .x1 = blk H s₀)
    {Q : State → Prop}
    (k : ∀ s', KO H s₀ s' → s'.gpr .x21 = t.gpr .x21 →
      hH.md.stateAt s'.mem (inn s₀) = hH.md.compress (hH.md.stateAt t.mem (inn s₀))
        (hH.md.blockAt t.mem (blk H s₀)) → Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := sizes hH hp
  have z : inn s₀ + BitVec.ofNat 64 0 = inn s₀ := BitVec.add_zero _
  have kp : ∀ r ∈ koregs, r ∈ preserved ∧ r ≠ .x30 := by decide
  refine compressAt_ok hH.comp (callOk hH hp hk h20 h1) fun s' hrd hwr hcs hsp hfr hst =>
    k s' (hk.keep hrd hwr hsp (fun r hr => hcs r (kp r hr).1 (kp r hr).2) hfr ?_)
      (hcs _ (by decide) (by decide)) hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · have := save_inR hp (a := 0) (n := H.P.N) (by omega); rwa [z] at this
  · exact (Offset.base_disjoint (scr s₀) (k := H.P.so) (e := 8 * H.stream.W) (n := 56)
      (by show H.P.so ≤ 8 * ((H.P.so + 48) / 8); omega)
      (by show 8 * ((H.P.so + 48) / 8) + 56 ≤ 2 ^ 64; omega)).symm

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : KO H s₀ s) (h21 : s.gpr .x21 = blk H s₀) :
    WP isa (.block H.finOut) s fun s' => ∃ t, KO H s₀ t ∧
      bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D ∧ s'.mem = t.mem ∧
      s'.sp = t.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ savedRegs → s'.gpr r = t.gpr r) := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have hdl := hH.md.digest_length (hH.md.stateAt s.mem (inn s₀))
  have k9 : ∀ r ∈ koregs, r ≠ .x9 := by decide
  have hL : 8 * H.stream.W + 56 ≤ 8 * sc := by
    have : H.stream.buf = 8 * H.stream.W + 56 := rfl
    have := hp.fits
    omega
  have fin : ∀ t, KO H s₀ t → bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D →
      WP isa (.block H.stream.restore) t fun s' => ∃ t, KO H s₀ t ∧
        bytesAt t.mem (op s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D ∧ s'.mem = t.mem ∧
        s'.sp = t.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧ (∀ r, r ∉ savedRegs → s'.gpr r = t.gpr r) :=
    fun t kt bt =>
      WP.mono (restore_ok H.stream kt.x23 (Nat.le_trans hp.hW (by decide)) kt.saved (by rw [kt.wr]; exact sR) hL)
        fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨t, kt, bt, hm, hsp, hg, ho⟩
  have x19_in : InRegions (s.rd ++ s.wr) (s.gpr .x19) H.P.N := by
    have := Offset.contains_base (inn s₀) (d := 0) (n := H.P.N) (k := H.P.N + H.P.B) (by omega) (by omega)
    rw [z] at this
    rw [hk.x19, hk.rd, hk.wr]
    exact ⟨_, List.mem_append_right _ iR, this⟩
  unfold Hash.finOut
  by_cases hDN' : H.D < H.P.N
  · simp only [hDN', ↓reduceIte, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (hH.shape.out s x19_in (by
        rw [h21, hk.wr]; exact ⟨_, iR, Offset.contains_base _ (by omega) (by omega)⟩)
      (by rw [hk.x19, h21]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
    rw [h21, hk.x19] at m₁
    have f₁ : Frame [⟨blk H s₀, H.P.N⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    have k₁ : KO H s₀ s₁ := hk.keep rd₁ wr₁ sp₁ (fun r hr => g₁ r (k9 r hr)) f₁
      (by simp only [List.mem_singleton]; rintro r rfl; exact save_inR hp (by omega))
    have b₁ : bytesAt s₁.mem (blk H s₀) H.D = (hH.md.digest (hH.md.stateAt s.mem (inn s₀))).take H.D := by
      rw [bytesAt_take _ _ (Nat.le_of_lt hDN'), m₁, bytesAt_writeBytes_self' hdl (by omega)]
    have x21₁ : s₁.gpr .x21 = blk H s₀ := by rw [g₁ _ (by decide), h21]
    simp only [Hash.copy32]
    refine copy32_ok (src := .x21) (dst := .x24) (by decide) (by decide) 0 0 (H.D / 4) ⟨rfl, by omega⟩
      ⟨rfl, by omega⟩ _ s₁ _
      (fun j hj => by
        rw [x21₁, add_ofNat, add_ofNat, rd₁, wr₁, hk.rd, hk.wr]
        exact ⟨_, List.mem_append_right _ iR, Offset.contains_base _ (by omega) (by omega)⟩)
      (fun j hj => by
        rw [k₁.x24, add_ofNat, k₁.wr]
        exact ⟨_, pR, Offset.contains_base _ (by show 0 + 4 * j + 4 ≤ H.D; omega) (by omega)⟩)
      (by
        rw [x21₁, k₁.x24, eD, add_ofNat]
        exact hp.i_p.sep (Offset.contains_base _ (by omega) (by omega))
          (Offset.contains_base _ (by show 0 + H.D ≤ H.D; omega) (by omega)))
      fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
    rw [x21₁, k₁.x24, eD, z, z] at m₂
    refine fin s₂ (k₁.keep rd₂ wr₂ sp₂ (fun r hr => g₂ r (k9 r hr))
      (m₂ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [bytesAt_length]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))) ?_
    rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), b₁]
  · have eDN : H.D = H.P.N := by omega
    simp only [hDN', ↓reduceIte, List.cons_append]
    refine wp_mov fun s₁ u₁ => ?_
    rw [WP.block_append_iff]
    have x19₁ : s₁.gpr .x19 = inn s₀ := by rw [u₁.other _ (by decide), hk.x19]
    refine WP.mono (hH.shape.out s₁ (by rw [u₁.rd, u₁.wr, u₁.other _ (by decide)]; exact x19_in) (by
        rw [u₁.gpr, hk.x24, u₁.wr, hk.wr, ← eDN]; exact ⟨_, pR, Region.contains_self _ _⟩)
      (by rw [x19₁, u₁.gpr, hk.x24, ← eDN]; exact hp.i_p.sub_left (Region.sub_prefix (by omega))))
      fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_
    rw [x19₁, u₁.gpr, hk.x24, u₁.mem] at m₂
    refine fin s₂ (hk.keep (rd₂.trans u₁.rd) (wr₂.trans u₁.wr) (sp₂.trans u₁.sp) (fun r hr => by
        rw [g₂ r (k9 r hr), u₁.other r (by revert hr; revert r; decide)])
      (m₂ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
        rw [hdl, ← eDN]; exact Region.contains_self _ _))
      (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))) ?_
    rw [m₂, eDN, bytesAt_writeBytes_self' hdl (by omega), List.take_of_length_le (by omega)]

/-! ## Correctness -/

theorem correct : WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  obtain ⟨hN4, hD4, hL4, hB4, hpad, hD0, hDN, hNL, hB, hso, hf, h8, hSB, h4k⟩ := sizes hH hp
  have hB0 := hH.B_pos
  refine WP.seq (WP.mono (WP.preservedV (pro_ok hp) (by rfl)) fun s₁ ⟨⟨k₁, di₁, dx₁, f₁⟩, hv₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (WP.preservedV (fin1Args_ok hH.stream hp k₁ di₁ dx₁) (by rfl))
    fun t₁ ⟨⟨kt₁, a₁, si₁, m₁⟩, hva₁⟩ => finCall_ok hH.stream hp kt₁ a₁ fun s₂ hv₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (WP.preservedV (mid_ok hH hp k₂) (by rw [Code.allInstrs_eq]; exact hH.finMid_keepsV))
    fun s₃ ⟨⟨k₃, x20₃, x21₃, x1₃, i₃, b₃, p₃⟩, hv₃⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (cmp_ok hH hp k₃ x20₃ x1₃ (Q := fun s' => KO H s₀ s' ∧
      s'.gpr .x21 = s₃.gpr .x21 ∧ hH.md.stateAt s'.mem (inn s₀) =
        hH.md.compress (hH.md.stateAt s₃.mem (inn s₀)) (hH.md.blockAt s₃.mem (blk H s₀)))
      fun s₄ k₄ x21₄ e₄ => ⟨k₄, x21₄, e₄⟩)
    (by rw [Code.allInstrs_eq]; exact hH.cmp_keepsV)) fun s₄ ⟨⟨k₄, x21₄, e₄⟩, hv₄⟩ => ?_)
  refine WP.mono (WP.preservedV (out_ok hH hp k₄ (x21₄.trans x21₃))
    (by rw [Code.allInstrs_eq]; exact hH.finOut_keepsV))
    fun s' ⟨⟨s₅, k₅, m₅, hm, hsp, hg, ho⟩, hv₅⟩ => ⟨abi_of k₅ hsp (fun r hr => by
      rw [hv₅ r hr, hv₄ r hr, hv₃ r hr, hv₂ r hr, hva₁ r hr, hv₁ r hr]) hg ho, ?_⟩
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
open VG.Proof.Hmac.Generic.AArch64.Finalize (kr_agree fin_rel')

variable {sc : Nat} {s₀ s₀' : State} (hp : Pre (H := H.stream) sc s₀) (hp' : Pre (H := H.stream) sc s₀')
  (hq : PubEq s₀ s₀')

omit hH in
/-- The registers `oregs` and the stack pointer agree in two runs. -/
theorem ko_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KO H s₀ s ∧ s.gpr .x21 = blk H s₀)
    (h' : KO H s₀' s' ∧ s'.gpr .x21 = blk H s₀') : s.sp = s'.sp ∧ ∀ r ∈ oregs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.1.sp, h'.1.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.1.x19, h'.1.x19, inn, inn, hq.x0]
  · rw [h.2, h'.2, blk, blk, inn, inn, hq.x0]
  · rw [h.1.x23, h'.1.x23, scr, scr, hq.x4]
  · rw [h.1.x24, h'.1.x24, op, op, hq.x3]

omit hH in
theorem callOk_congr {t : State} {N B so : Nat} {a b c a' b' c' : Addr} (h : CallOk t N B so a b c) (ha : a = a')
    (hb : b = b') (hc : c = c') : CallOk t N B so a' b' c' := by
  subst ha hb hc; exact h

include hH hp hp' hq

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.stream.finPrologue)
      fun s s' => (KR (H := H.stream) s₀ s ∧ s.gpr .x0 = inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2) ∧
        (KR (H := H.stream) s₀' s' ∧ s'.gpr .x0 = inn s₀' ∧ s'.gpr .x2 = s₀'.gpr .x2) :=
    rel_taint args (fun s s' e e' => by
        rw [e, e']
        refine ⟨hq.sp, fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.x0
        · exact hq.x1
        · exact hq.x2
        · exact hq.x3
        · exact hq.x4) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp) fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hp') fun _ ⟨k, d, x, _⟩ => ⟨k, d, x⟩)
  have fin1 := fin_rel' hH.stream hp hp' hq (c := s₀.gpr .x2)
    (F := fun s => KR (H := H.stream) s₀ s ∧ s.gpr .x0 = inn s₀ ∧ s.gpr .x2 = s₀.gpr .x2)
    (F' := fun s => KR (H := H.stream) s₀' s ∧ s.gpr .x0 = inn s₀' ∧ s.gpr .x2 = s₀'.gpr .x2) hc.fin1
    (fun _ _ h h' => kr_agree hq h.1 h'.1)
    (fun s ⟨k, d, x⟩ => fin1Args_ok hH.stream hp k d x)
    (fun s ⟨k, d, x⟩ => WP.mono (fin1Args_ok hH.stream hp' k d x) fun _ ⟨k, a, si, m⟩ =>
      ⟨k, a, si.trans hq.x2.symm, m⟩)
  have mid : RelCT isa (fun s s' => KR (H := H.stream) s₀ s ∧ KR (H := H.stream) s₀' s') (.block H.finMid)
      fun s s' => (KO H s₀ s ∧ s.gpr .x20 = scr s₀ ∧ s.gpr .x21 = blk H s₀ ∧ s.gpr .x1 = blk H s₀) ∧
        (KO H s₀' s' ∧ s'.gpr .x20 = scr s₀' ∧ s'.gpr .x21 = blk H s₀' ∧ s'.gpr .x1 = blk H s₀') :=
    rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hc.mid
      (fun s k => WP.mono (mid_ok hH hp k) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
      (fun s k => WP.mono (mid_ok hH hp' k) fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  have e₀ : inn s₀' = inn s₀ := hq.x0.symm
  have e₄ : scr s₀' = scr s₀ := hq.x4.symm
  have eb : blk H s₀' = blk H s₀ := by rw [blk, blk, e₀]
  have cmp : RelCT isa (fun s s' =>
        (KO H s₀ s ∧ s.gpr .x20 = scr s₀ ∧ s.gpr .x21 = blk H s₀ ∧ s.gpr .x1 = blk H s₀) ∧
        (KO H s₀' s' ∧ s'.gpr .x20 = scr s₀' ∧ s'.gpr .x21 = blk H s₀' ∧ s'.gpr .x1 = blk H s₀'))
      (compressAt H.compN H.compC)
      fun s s' => (KO H s₀ s ∧ s.gpr .x21 = blk H s₀) ∧ (KO H s₀' s' ∧ s'.gpr .x21 = blk H s₀') :=
    rel_wp (compressAt_rel hH.comp fun s s' ⟨⟨k, x20, _, x1⟩, ⟨k', x20', _, x1'⟩⟩ =>
        ⟨callOk hH hp k x20 x1, callOk_congr (callOk hH hp' k' x20' x1') e₀ e₄ eb, by rw [k.sp, k'.sp, hq.sp]⟩)
      (fun s ⟨k, x20, x21, x1⟩ => cmp_ok hH hp k x20 x1 fun s' k' e _ => ⟨k', e.trans x21⟩)
      (fun s ⟨k, x20, x21, x1⟩ => cmp_ok hH hp' k x20 x1 fun s' k' e _ => ⟨k', e.trans x21⟩)
  obtain ⟨_, hr⟩ := hc.out
  have out : RelCT isa (fun s s' => (KO H s₀ s ∧ s.gpr .x21 = blk H s₀) ∧ (KO H s₀' s' ∧ s'.gpr .x21 = blk H s₀'))
      (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs oregs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := ko_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact pro.seq (fin1.seq (mid.seq (cmp.seq out)))

end

/-- HMAC's `finalize` is verified against `finG`, given the taint checks. -/
theorem verified {sc : Nat} (hc : Checks H) (hfit : H.stream.buf + H.stream.F ≤ 8 * sc)
    (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified AArch64.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH.stream sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_,
    hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH.stream sc h₁ hfit) (pre_of hH.stream sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.AArch64.HmacFin
