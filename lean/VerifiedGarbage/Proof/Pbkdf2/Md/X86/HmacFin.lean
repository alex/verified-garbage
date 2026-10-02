import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Hmac.Generic.X86.Finalize

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `finalize`, correct

Untrusted: everything here is checked by Lean. HMAC's `finalize`
(`Impl/Pbkdf2/Md/X86.lean`) starts as in the streaming-level design: the
prologue and the call of the hash function's streaming `finalize` on the
inner state, which writes the inner digest to `scratch`
(`Proof/Hmac/Generic/X86/Finalize.lean`, whose `KR` the rest keeps). Then
the inner state gets the outer hash value and, in its buffer, the digest and
the padding (`mid_ok`); one compression (`cmpF_ok`) gives the outer hash
value, whose digest is the MAC (`out_ok`): `Md.Link.hmac_outer`.
-/

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash copyW)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Hmac.Generic.X86 (HashOK finG SavedRegs saveR savedRegs restore_ok callee_saved ea_at stk After
  setWidth_add toNat_add_ofNat)
open VG.Proof.Hmac.Generic.X86.Finalize (Pre KR E inn outer op scr inR outerR opR scR stkR T tR calR tO wr_mem
  save_sub t_sub save_t wrs kregs kregs_callee stk_eq pro_ok fin1Args_ok finCall_ok)
open VG.Proof.Hmac.Generic.Common (InRegions.right' bytesAt_writeBytes_self' bytesAt_take covers_one)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov sub_offset)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep writeBytes_at bytesAt_getD'
  xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : Sizes H) {sc : Nat} {s₀ : State} (hp : Pre (H := H.st) sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ H.st.buf + H.st.F ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ 0 < H.D ∧ H.D ≤ H.N ∧ H.B ≤ 128 ∧ 64 ≤ H.B ∧
    H.S = H.N + H.B ∧ H.D ≤ H.st.F ∧ (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (outer s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (op s₀).toNat + H.D ≤ 2 ^ 32 := by
  have := hp.ni; have := hp.no; have := hp.np
  have hS := hz.S
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N.1, hz.N.2.1, hz.D.1, hz.D.2.1, hz.B4.2.2, hz.B4.2.1, hS, hz.F.1,
    by rw [← hS]; exact hp.ni, by rw [← hS]; exact hp.no, hp.np⟩

/-- The compression function's scratch space. -/
abbrev cmpR (H : Hash) (s₀ : State) : Region := ⟨(scr s₀).setWidth 64, H.so⟩

theorem cmp_sub : Region.Sub (cmpR H s₀) (scR sc s₀) := by
  have := bounds hz hp; exact Region.sub_prefix (by omega)

theorem save_cmp : (saveR H.st (scr s₀)).Disjoint (cmpR H s₀) := by
  have := bounds hz hp
  exact Offset.disjoint_base _ (by omega) (by omega)

omit hp in
theorem inR_eq : inR (H := H.st) s₀ = ⟨(inn s₀).setWidth 64, H.N + H.B⟩ := by
  rw [inR, show H.st.S = H.N + H.B from hz.S]

/-- The inner state is writable. -/
theorem cov_in {s : State} (hwr : s.wr = s₀.wr) : Covers [⟨(inn s₀).setWidth 64, H.N + H.B⟩] s.wr := by
  rw [← inR_eq hz, hwr]
  exact covers_one (wr_mem hp).2.1

omit hp in
/-- A part of the inner state. -/
theorem in_sub {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ (inR (H := H.st) s₀) := by
  rw [inR_eq hz]; exact Offset.sub_base _ h

theorem save_in {a n : Nat} (h : a + n ≤ H.N + H.B) :
    (saveR H.st (scr s₀)).Disjoint ⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ :=
  (hp.i_s.symm.sub_left (save_sub hp)).sub_right (in_sub hz h)

/-- `KR` after code that writes only a part of the inner state and `eax`,
`ecx` and `edx`. -/
theorem kr_write {s s' : State} (h : KR (H := H.st) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) {a n : Nat} (hl : a + n ≤ H.N + H.B)
    (hf : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩] s.mem s'.mem) : KR (H := H.st) sc s₀ s' :=
  h.keep hrd hwr (fun r hr => hg r (by revert hr; decide +revert) (by revert hr; decide +revert)
    (by revert hr; decide +revert)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact save_in hz hp hl)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, in_sub hz hl⟩)

/-- The arguments of the compression of the inner buffer. -/
theorem cmpArgs {s : State} (hk : KR (H := H.st) sc s₀ s) (hax : s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N) :
    CmpArgs H.N H.B H.so s (inn s₀) (scr s₀) := by
  have := bounds hz hp
  exact
    { ebx := hk.ebx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := cov_in hz hp hk.wr
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨scR sc s₀, (wr_mem hp).1, 0, by simp, by simp only; omega⟩
      st_sc := by rw [← inR_eq hz]; exact hp.i_s.sub_right (cmp_sub hz hp)
      b_st := by rw [stk_eq hk, ← inR_eq hz]; exact hp.b_i
      b_sc := by rw [stk_eq hk]; exact hp.b_s.sub_right (cmp_sub hz hp)
      nst := by omega
      nsc := by omega }

end

/-! ## The outer block -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre (H := H.st) sc s₀)
include hO hp

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it, and `eax` at the buffer. -/
theorem mid_ok {s : State} (hk : KR (H := H.st) sc s₀ s) (hsi : s.gpr .esi = outer s₀) :
    WP isa (.block H.finMid) s fun t => KR (H := H.st) sc s₀ t ∧ t.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N ∧
      hO.md.stateAt t.mem ((inn s₀).setWidth 64) = hO.md.stateAt s.mem ((outer s₀).setWidth 64) ∧
      bytesAt t.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D = bytesAt s.mem (T (H := H.st) s₀) H.D ∧
      bytesAt t.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB ∧
      Frame [inR (H := H.st) s₀] s.mem t.mem := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := bounds hz hp
  have hN4 := hz.N.2.2; have hD4 := hz.D.2.2; have tl := hz.tail_length; have hDL := hz.DL
  have hn4 : 4 * (H.N / 4) = H.N := by omega
  have hd4 : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have oc : Covers [⟨(outer s₀).setWidth 64, H.N + H.B⟩] (s.rd ++ s.wr) :=
    covers_one (by rw [hk.rd, hp.rd, ← hS]; simp)
  have sc' : Covers [scR sc s₀] (s.rd ++ s.wr) := covers_one (by rw [hk.rd, hk.wr, hp.wr]; simp)
  have ic := cov_in hz hp hk.wr
  simp only [Hash.finMid, List.append_assoc]
  -- The outer hash value.
  refine copyW_ok (by decide) (by decide) (H.N / 4) _ s _ hsi hk.ebx (by omega) (by omega)
    (fun j hj => by rw [addr_eq (by omega)]; exact inReg oc (by omega) (by omega))
    (fun j hj => by rw [addr_eq (by omega)]; exact inReg ic (by omega) (by omega)) ?_ fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · rw [hn4, BitVec.add_zero, BitVec.add_zero]
    have c₁ : (outerR (H := H.st) s₀).Contains ((outer s₀).setWidth 64) H.N :=
      Memory.contains_base (show H.N ≤ H.st.S by rw [show H.st.S = H.N + H.B from hz.S]; omega)
    have c₂ : (inR (H := H.st) s₀).Contains ((inn s₀).setWidth 64) H.N :=
      Memory.contains_base (show H.N ≤ H.st.S by rw [show H.st.S = H.N + H.B from hz.S]; omega)
    exact hp.i_o.symm.sep c₁ c₂
  rw [hn4, BitVec.add_zero, BitVec.add_zero] at m₁
  have f₁ : Frame [⟨(inn s₀).setWidth 64, H.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  -- The digest.
  refine copyW_ok (by decide) (by decide) (H.D / 4) _ s₁ _ (by rw [g₁ _ (by decide), hk.ebp])
    (by rw [g₁ _ (by decide), hk.ebx]) (by omega) (by omega)
    (fun j hj => by rw [addr_eq (by omega), rd₁, wr₁]; exact inReg sc' (by omega) (by omega))
    (fun j hj => by rw [addr_eq (by omega), wr₁]; exact inReg ic (by omega) (by omega)) ?_ fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  · rw [hd4]
    exact hp.i_s.symm.sep (Offset.contains_base _ (by omega) (by omega))
      (by rw [inR_eq hz]; exact Offset.contains_base _ (by omega) (by omega))
  rw [hd4] at m₂
  have f₂ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  -- The padding, and `eax` at the buffer.
  refine pad_ok hz (x := inn s₀) (by rw [g₂ _ (by decide), g₁ _ (by decide), hk.ebx]) (by omega)
    (by rw [wr₂, wr₁]; exact ic) fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  rw [← List.append_nil H.atBlk]
  refine atBlk_ok fun s₄ e₄ g₄ m₄ rd₄ wr₄ => WP.block_nil ?_
  have f₃ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D), H.B - H.D⟩] s₂.mem s₄.mem := by
    rw [m₄, m₃]; exact writeBytes_frame _ _ _ (by rw [tl]; exact Region.contains_self _ _)
  have fI : Frame [inR (H := H.st) s₀] s.mem s₄.mem :=
    ((f₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega); rw [BitVec.add_zero] at this
        exact ⟨_, List.mem_singleton_self _, this⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, in_sub hz (by omega)⟩)).trans
      (f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, in_sub hz (by omega)⟩)
  have k₄ : KR (H := H.st) sc s₀ s₄ := hk.keep (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁])
    (fun r hr => by
      rw [g₄ r (by revert hr; decide +revert), g₃ r (by revert hr; decide +revert),
        g₂ r (by revert hr; decide +revert), g₁ r (by revert hr; decide +revert)]) fI
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.i_s.symm.sub_left (save_sub hp))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- The bytes before the padding are not written by it, and those before the digest not by it.
  have d₃ : ∀ {a n : Nat}, a + n ≤ H.N + H.D →
      ∀ r ∈ [(⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D), H.B - H.D⟩ : Region)],
        Region.Disjoint ⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl h) (by omega) (by omega)
  refine ⟨k₄, by rw [e₄, g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hk.ebx], ?_, ?_, ?_, fI⟩
  · refine hO.reloc _ _ _ _ fun i hi => ?_
    have dN : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
        ∀ r ∈ [(⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ : Region)],
          Region.Disjoint ⟨(inn s₀).setWidth 64, H.N⟩ r := by
      intro a n h₁ h₂ r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ h₁ (by omega)
    rw [f₃.bytes (R := ⟨(inn s₀).setWidth 64, H.N⟩) (dN (by omega) (by omega)) (by show H.N ≤ 2 ^ 64; omega) hi,
      f₂.bytes (R := ⟨(inn s₀).setWidth 64, H.N⟩) (dN (by omega) (by omega)) (by show H.N ≤ 2 ^ 64; omega) hi, m₁,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega), bytesAt_getD' _ _ hi]
  · rw [Memory.frame_bytesAt f₃ (d₃ (by omega)) (by omega), m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    have dT : ∀ r ∈ [(⟨(inn s₀).setWidth 64, H.N⟩ : Region)], Region.Disjoint ⟨T (H := H.st) s₀, H.D⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      refine (hp.i_s.symm.sub_left fun a ha => t_sub hp a (Region.sub_prefix hDF a ha)).sub_right ?_
      rw [inR_eq hz]; exact Region.sub_prefix (by omega)
    exact Memory.frame_bytesAt f₁ dT (by omega)
  · rw [m₄, m₃, ← tl, bytesAt_writeBytes_self' rfl (by omega)]

/-- The compression of the inner buffer into the outer hash value. -/
theorem cmpF_ok {s : State} (hk : KR (H := H.st) sc s₀ s) (hax : s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (k : ∀ s', KR (H := H.st) sc s₀ s' →
      Frame [⟨(inn s₀).setWidth 64, H.N⟩, cmpR H s₀, stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((inn s₀).setWidth 64) = hO.md.compress (hO.md.stateAt s.mem ((inn s₀).setWidth 64))
        (hO.md.blockAt s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, -⟩ := bounds hz hp
  have hB := hz.B4
  refine cmp_ok hO.comp (by omega) (cmpArgs hz hp hk hax) fun s₃ ha e₃ => ?_
  have f := ha.frame
  rw [stk_eq hk] at f
  have sI : Region.Sub ⟨(inn s₀).setWidth 64, H.N⟩ (inR (H := H.st) s₀) := by
    have := in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega); rwa [BitVec.add_zero] at this
  refine k s₃ (hk.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f ?_ ?_) (f.mono (by simp)) e₃
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hp.i_s.symm.sub_left (save_sub hp)).sub_right sI
    · exact save_cmp hz hp
    · exact hp.b_s.symm.sub_left (save_sub hp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨_, by simp, sI⟩
    · exact ⟨scR sc s₀, by simp, cmp_sub hz hp⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : KR (H := H.st) sc s₀ s) :
    WP isa (.block H.finOut) s fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem ((op s₀).setWidth 64) H.D = (hO.md.digest (hO.md.stateAt s.mem ((inn s₀).setWidth 64))).take H.D := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := bounds hz hp
  have hD4 := hz.D.2.2
  have hd4 : 4 * (H.D / 4) = H.D := by omega
  have eD : H.st.D = H.D := rfl
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have ic := cov_in hz hp hk.wr
  have hdl := hO.md.digest_length (hO.md.stateAt s.mem ((inn s₀).setWidth 64))
  have sI : Region.Sub ⟨(inn s₀).setWidth 64, H.N⟩ (inR (H := H.st) s₀) := by
    have := in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega); rwa [BitVec.add_zero] at this
  have hL : 8 * H.st.W + 16 ≤ 8 * sc := by omega
  -- The epilogue, from the state the MAC is written in.
  have epi : ∀ t, KR (H := H.st) sc s₀ t → bytesAt t.mem ((op s₀).setWidth 64) H.D =
      (hO.md.digest (hO.md.stateAt s.mem ((inn s₀).setWidth 64))).take H.D →
      WP isa (.block H.st.restore) t fun s' => abiPreserved s₀ s' ∧
        bytesAt s'.mem ((op s₀).setWidth 64) H.D =
          (hO.md.digest (hO.md.stateAt s.mem ((inn s₀).setWidth 64))).take H.D := fun t kt ht =>
    WP.mono (restore_ok H.st kt.ebp kt.saved (by rw [kt.wr]; exact sR) hL hw)
      fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => by
          by_cases he : r = .esp
          · subst he; rw [ho _ (by decide) (by decide), kt.esp]
          · exact hg r (callee_saved r hr he), by rw [hm]; exact kt.ret hp⟩, by rw [hm]; exact ht⟩
  by_cases hDN' : H.D < H.N
  · simp only [Hash.finOut, hDN', ite_true, List.append_assoc]
    refine atBlk_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ => ?_
    have k₁ : KR (H := H.st) sc s₀ s₁ := kr_write hz hp hk rd₁ wr₁ (fun r h1 _ _ => g₁ r h1) (a := 0) (n := 0)
      (by omega) (by rw [m₁]; exact Frame.refl _ _)
    have aN : (inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 = (inn s₀).setWidth 64 + BitVec.ofNat 64 H.N :=
      setWidth_add (by omega)
    have tN : (inn s₀ + BitVec.ofNat 32 H.N).toNat = (inn s₀).toNat + H.N := toNat_add_ofNat (by omega)
    rw [WP.block_append_iff]
    refine WP.mono (hO.out s₁ (by rw [k₁.ebx]; omega) (by rw [e₁, hk.ebx, tN]; omega) ?_ ?_ ?_)
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    · rw [k₁.ebx, k₁.rd, k₁.wr]
      have := inReg (o := 0) (n := H.N) (cov_in hz hp (s := s₀) rfl) (by omega) (by omega)
      rw [BitVec.add_zero] at this
      exact InRegions.right' this
    · rw [e₁, hk.ebx, aN, k₁.wr]; exact inReg (cov_in hz hp (s := s₀) rfl) (by omega) (by omega)
    · rw [k₁.ebx, e₁, hk.ebx, aN]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    rw [e₁, hk.ebx, aN, k₁.ebx, m₁] at m₂
    have f₂ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.N⟩] s₁.mem s₂.mem := by
      rw [m₂, m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    have k₂ : KR (H := H.st) sc s₀ s₂ := kr_write hz hp k₁ rd₂ wr₂ (fun r _ h2 h3 => g₂ r h2 h3) (by omega) f₂
    refine copyW_ok (by decide) (by decide) (H.D / 4) _ s₂ _ k₂.ebx k₂.edi (by omega) (by omega)
      (fun j hj => by
        rw [addr_eq (by omega)]; exact InRegions.right' (inReg (cov_in hz hp k₂.wr) (by omega) (by omega)))
      (fun j hj => by
        rw [addr_eq (by omega), k₂.wr]; exact ⟨_, pR, Offset.contains_base _ (by omega) (by omega)⟩) ?_
      fun s₃ g₃ rd₃ wr₃ m₃ => ?_
    · rw [hd4, BitVec.add_zero]
      exact hp.i_p.sep (by rw [inR_eq hz]; exact Offset.contains_base _ (by omega) (by omega))
        (Region.contains_self _ _)
    rw [hd4, BitVec.add_zero] at m₃
    have f₃ : Frame [opR (H := H.st) s₀] s₂.mem s₃.mem := by
      rw [m₃]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    have k₃ : KR (H := H.st) sc s₀ s₃ := k₂.keep rd₃ wr₃ (fun r hr => g₃ r (by revert hr; decide +revert)) f₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.p_s.symm.sub_left (save_sub hp))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    refine epi s₃ k₃ ?_
    rw [m₃, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), m₂,
      bytesAt_take _ _ (Nat.le_of_lt hDN'), bytesAt_writeBytes_self' hdl (by omega)]
  · have e : H.D = H.N := by omega
    simp only [Hash.finOut, hDN', ite_false, List.cons_append]
    refine wp_mov fun s₁ u₁ => ?_
    have k₁ : KR (H := H.st) sc s₀ s₁ := kr_write hz hp hk u₁.rd u₁.wr (fun r h1 _ _ => u₁.other r h1) (a := 0) (n := 0)
      (by omega) (by rw [u₁.mem]; exact Frame.refl _ _)
    rw [WP.block_append_iff]
    refine WP.mono (hO.out s₁ (by rw [k₁.ebx]; omega) (by rw [u₁.gpr, hk.edi]; omega) ?_ ?_ ?_)
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    · rw [k₁.ebx, k₁.rd, k₁.wr]
      have := inReg (o := 0) (n := H.N) (cov_in hz hp (s := s₀) rfl) (by omega) (by omega)
      rw [BitVec.add_zero] at this
      exact InRegions.right' this
    · rw [u₁.gpr, hk.edi, k₁.wr]; exact ⟨_, pR, Memory.contains_base (by omega)⟩
    · rw [k₁.ebx, u₁.gpr, hk.edi]; exact hp.i_p.sub_left sI |>.sub_right (Region.sub_prefix (by omega))
    rw [u₁.gpr, hk.edi, k₁.ebx, u₁.mem] at m₂
    have f₂ : Frame [opR (H := H.st) s₀] s₁.mem s₂.mem := by
      rw [m₂, u₁.mem]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Memory.contains_base (by omega))
    have k₂ : KR (H := H.st) sc s₀ s₂ := k₁.keep rd₂ wr₂
      (fun r hr => g₂ r (by revert hr; decide +revert) (by revert hr; decide +revert)) f₂
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.p_s.symm.sub_left (save_sub hp))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    refine epi s₂ k₂ ?_
    rw [m₂, List.take_of_length_le (by omega), bytesAt_take _ _ (Nat.le_of_eq e) (F := H.N),
      bytesAt_writeBytes_self' hdl (by omega), List.take_of_length_le (by omega)]

theorem correct : WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hO.hH.SH sc).post s₀ s' := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := bounds hz hp
  have hl := hO.link
  have tl := hz.tail_length; have hDL := hz.DL
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨k₁, si₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hO.hH hp k₁) fun t₁ ⟨kt₁, a₁, st₁, m₁⟩ =>
    finCall_ok hO.hH hp kt₁ a₁ fun s₂ k₂ si₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (mid_ok hO hp k₂ (by rw [si₂, st₁, si₁])) fun s₃ ⟨k₃, ax₃, e₃, b₃, p₃, f₃⟩ => ?_)
  refine WP.seq (cmpF_ok hO hp k₃ ax₃ fun s₄ k₄ f₄ e₄ => ?_)
  refine WP.mono (out_ok hO hp k₄) fun s' ⟨habi, hmac⟩ => ⟨habi, ?_⟩
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hO.hH.hB] at hk0 hcnt
  have hl0 : (xorPad k0 ipad ++ text).length = H.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until it is copied.
  have oI : ∀ r ∈ [saveR H.st (scr s₀)], Region.Disjoint (outerR (H := H.st) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (save_sub hp)
  have o₂ : ∀ r ∈ [inR (H := H.st) s₀, tR (H := H.st) s₀, calR hO.hH s₀, stkR s₀],
      Region.Disjoint (outerR (H := H.st) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (t_sub hp)
    · exact hp.o_s.sub_right (VG.Proof.Hmac.Generic.X86.Finalize.cal_sub hO.hH hp)
    · exact hp.b_o.symm
  have rO₂ := Hmac.Generic.X86.Init.repr_keep hO.hH f₂ o₂ (m₁ ▸ Hmac.Generic.X86.Init.repr_keep hO.hH f₁ oI hrO)
  -- The inner digest.
  have dig := d₂ _ (m₁ ▸ Hmac.Generic.X86.Init.repr_keep hO.hH f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [show arg s₀ 3 ++ arg s₀ 2 = Hmac.Generic.X86.countF s₀ from rfl, hcnt, hl0])
  rw [← bytesAt_take _ _ hDF] at dig
  -- The outer hash value.
  have lo : (xorPad k0 opad).length = H.B := by simp [xorPad, hk0]
  have so₂ : hO.md.stateAt s₂.mem ((outer s₀).setWidth 64) = hO.md.compressList hO.iv (xorPad k0 opad) 1 :=
    Md.stateAt_of_repr (by omega) lo (hl.repr _ _ _ rO₂)
  have pad₃ : bytesAt s₃.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 H.D) (H.B - H.D) =
      hO.md.tailPad H.D := by rw [Memory.add_ofNat, p₃, hO.tail]
  rw [e₄, e₃, so₂, Md.blockAt_tailPad (by omega) pad₃, b₃, dig] at hmac
  show bytesAt s'.mem ((op s₀).setWidth 64) hO.hH.SH.digestBytes = hmacBlockKey hO.hH.SH.H k0 text
  rw [hO.hH.hD, hmac, hl.hmac_outer (by rw [hk0]) text]

end

end VG.Proof.Pbkdf2.Md.X86.HmacFin
