import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Instances

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `finalize`

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Pbkdf2/Md/X86_64/HmacFin.lean`): HMAC's `finalize`
(`Impl/Pbkdf2/Md/AArch64.lean`) differs from the generic one
(`Proof/Hmac/Generic/AArch64/Finalize.lean`) only between its two calls of
`finalize`: instead of copying the outer state over the inner one and
absorbing the inner digest into it with `update`, it writes the outer hash
value and the digest over the inner state (`finMid`), which then represents
the outer block followed by the digest (`md.Repr`), and copies the MAC out
in words (`finOut`). Everything else is the generic proof's, for the hash
function's streaming functions (`HashOK.stream`); constant time likewise,
from the taint checks of the pieces between the calls (`Checks`).
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacFin

open VG.AArch64 VG.Proof.MdStream
open VG.Proof.MdStream.AArch64 (add_ofNat)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (copy32_ok)
open VG.Proof.Hmac.Generic.AArch64 (finG FinArgs rel_taint rel_wp fin_rel restore_ok saveR)
open VG.Proof.Hmac.Generic.AArch64.Finalize (Pre KR kregs inn outer op scr T tR calR stkR inR outerR opR scR
  pre_of wr_mem t_sub save_sub cal_sub pro_ok fin1Args_ok fin2Args_ok finCall_ok fin1Block fin2Block abi_of
  pubRegs)
open VG.Proof.Hmac.Generic.AArch64.Init (repr_keep PubEq args)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

/-- The taint checks of the pieces of `finalize` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.stream.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin1Block H.stream)) hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.finMid) hc).isSome = true
  fin2 : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block (fin2Block H.stream)) hc).isSome = true
  out : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.finOut) hc).isSome = true

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H.stream) sc s₀)
include hH hp

/-- The sizes the copies need. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.D % 4 = 0 ∧ H.D + 4 ≤ H.P.B ∧ 0 < H.D ∧ H.D ≤ H.P.N ∧
    H.stream.buf + H.P.N ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 ∧ H.P.N + H.P.B ≤ 256 ∧ H.stream.buf + 64 ≤ 4096 := by
  have := hH.sizes.N4; have := hH.sizes.D4; have := hH.sizes.pad; have := hH.sizes.D0; have := hH.sizes.DN
  have := hp.nw; have := hp.hS; have := hp.hW
  have f : H.stream.buf + H.P.N ≤ 8 * sc := hp.fits
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have hb : H.stream.buf = 8 * H.stream.W + 56 := rfl
  omega

/-- The outer hash value and the inner digest, over the inner state. -/
theorem mid_ok {s : State} (hk : KR (H := H.stream) s₀ s) :
    WP isa (.block H.finMid) s fun t => KR (H := H.stream) s₀ t ∧
      (∀ i < H.P.N, t.mem (inn s₀ + BitVec.ofNat 64 i) = s.mem (outer s₀ + BitVec.ofNat 64 i)) ∧
      bytesAt t.mem (inn s₀ + BitVec.ofNat 64 H.P.N) H.D = bytesAt s.mem (T (H := H.stream) s₀) H.D := by
  obtain ⟨hN4, hD4, hDB, hD0, hDN, hf, h8, hSB, hb⟩ := sizes hH hp
  have hS : H.stream.S = H.P.N + H.P.B := rfl
  have eN : 4 * (H.P.N / 4) = H.P.N := by omega
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have oR : outerR (H := H.stream) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have tsub : Region.Sub ⟨T (H := H.stream) s₀, H.D⟩ (scR sc s₀) := Offset.sub_base _ (by omega)
  have isub : Region.Sub ⟨inn s₀, H.P.N⟩ (inR (H := H.stream) s₀) := Region.sub_prefix (by omega)
  have nsub : Region.Sub ⟨inn s₀ + BitVec.ofNat 64 H.P.N, H.D⟩ (inR (H := H.stream) s₀) :=
    Offset.sub_base _ (by omega)
  unfold Hash.finMid Hash.copy32
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
  rw [← List.append_nil ((List.range (H.D / 4)).flatMap _)]
  have x23 : s₁.gpr .x23 = scr s₀ := by rw [g₁ _ (by decide), hk.x23]
  have x19 : s₁.gpr .x19 = inn s₀ := by rw [g₁ _ (by decide), hk.x19]
  refine copy32_ok (src := .x23) (dst := .x19) (by decide) (by decide) H.stream.buf H.P.N (H.D / 4)
    ⟨by show (8 * H.stream.W + 56) % 4 = 0; omega, by omega⟩ ⟨hN4, by omega⟩ [] s₁ _
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
    fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => WP.block_nil ?_
  rw [x23, x19, eD] at m₂
  have f₁ : Frame [inR (H := H.stream) s₀] s.mem s₁.mem := by
    rw [m₁]
    exact (writeBytes_frame _ _ _ (R := ⟨inn s₀, H.P.N⟩) (by rw [bytesAt_length]; exact Region.contains_self _ _)).sub
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, isub⟩
  have f₂ : Frame [inR (H := H.stream) s₀] s₁.mem s₂.mem := by
    rw [m₂]
    exact (writeBytes_frame _ _ _ (R := ⟨inn s₀ + BitVec.ofNat 64 H.P.N, H.D⟩) (by
      rw [bytesAt_length]; exact Region.contains_self _ _)).sub
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, nsub⟩
  refine ⟨hk.keep (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁]) (fun r hr => by
      have : r ≠ .x9 := fun e => by subst e; revert hr; decide
      rw [g₂ r this, g₁ r this]) (f₁.trans f₂)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (save_sub hp)), fun i hi => ?_, ?_⟩
  · have hd : ∀ r ∈ [(⟨inn s₀ + BitVec.ofNat 64 H.P.N, H.D⟩ : Region)],
        Region.Disjoint ⟨inn s₀, H.P.N⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)
    rw [(m₂ ▸ writeBytes_frame _ _ _ (R := ⟨inn s₀ + BitVec.ofNat 64 H.P.N, H.D⟩) (by
        rw [bytesAt_length]; exact Region.contains_self _ _) : Frame _ s₁.mem s₂.mem).bytes
        (R := ⟨inn s₀, H.P.N⟩) hd (by show H.P.N ≤ 2 ^ 64; omega) hi,
      m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ hi]
  · rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    exact bytes_keep f₁ (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.i_s.sub_right tsub).symm) (by omega)

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : KR (H := H.stream) s₀ s) :
    WP isa (.block H.finOut) s fun s' => ∃ t, KR (H := H.stream) s₀ t ∧
      t.mem = writeBytes s.mem (op s₀) (bytesAt s.mem (T (H := H.stream) s₀) H.D) ∧ s'.mem = t.mem ∧
      s'.sp = t.sp ∧ (∀ r ∈ Hmac.Generic.AArch64.savedRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ Hmac.Generic.AArch64.savedRegs → s'.gpr r = t.gpr r) := by
  obtain ⟨hN4, hD4, hDB, hD0, hDN, hf, h8, hSB, hb⟩ := sizes hH hp
  have eD : 4 * (H.D / 4) = H.D := by omega
  obtain ⟨sR, _, pR⟩ := wr_mem hp
  have z : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := BitVec.add_zero
  have tsub : Region.Sub ⟨T (H := H.stream) s₀, H.D⟩ (scR sc s₀) := Offset.sub_base _ (by omega)
  unfold Hash.finOut Hash.copy32
  refine copy32_ok (src := .x23) (dst := .x21) (by decide) (by decide) H.stream.buf 0 (H.D / 4)
    ⟨by show (8 * H.stream.W + 56) % 4 = 0; omega, by omega⟩ ⟨rfl, by omega⟩ _ s _
    (fun j hj => by
      rw [hk.x23, add_ofNat, hk.rd, hk.wr]
      exact ⟨_, List.mem_append_right _ sR, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [hk.x21, add_ofNat, hk.wr]
      exact ⟨_, pR, Offset.contains_base _ (by show 0 + 4 * j + 4 ≤ H.D; omega) (by omega)⟩)
    (by
      rw [hk.x23, hk.x21, eD]
      exact hp.p_s.symm.sep (Offset.contains_base _ (by omega) (by omega))
        (Offset.contains_base _ (by show 0 + H.D ≤ H.D; omega) (by omega)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  rw [hk.x23, hk.x21, eD, z] at m₁
  have k₁ : KR (H := H.stream) s₀ s₁ := hk.keep rd₁ wr₁ sp₁ (fun r hr => g₁ r (fun e => by
      subst e; revert hr; decide))
    (m₁ ▸ writeBytes_frame _ _ _ (R := opR (H := H.stream) s₀) (by
      rw [bytesAt_length]; exact Region.contains_self _ _))
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp))
  have hL : 8 * H.stream.W + 56 ≤ 8 * sc := by
    have : H.stream.buf = 8 * H.stream.W + 56 := rfl
    omega
  exact WP.mono (restore_ok H.stream k₁.x23 (Nat.le_trans hp.hW (by decide)) k₁.saved (by rw [k₁.wr]; exact sR) hL)
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨s₁, k₁, m₁, hm, hsp, hg, ho⟩

/-! ## Correctness -/

theorem correct : WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  obtain ⟨hN4, hD4, hDB, hD0, hDN, hf, h8, hSB, hb⟩ := sizes hH hp
  have hD := hp.hD
  have hB0 := hH.B_pos
  refine WP.seq (WP.mono (WP.preservedV (pro_ok hp) (by rfl)) fun s₁ ⟨⟨k₁, di₁, dx₁, f₁⟩, hv₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (WP.preservedV (fin1Args_ok hH.stream hp k₁ di₁ dx₁) (by rfl)) fun t₁ ⟨⟨kt₁, a₁, si₁, m₁⟩, hva₁⟩ =>
    finCall_ok hH.stream hp kt₁ a₁ fun s₂ hv₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (WP.preservedV (mid_ok hH hp k₂) (by rw [Code.allInstrs_eq]; simp [Hash.finMid, Hash.copy32, Impl.Pbkdf2.AArch64.cp32, instrs, keepsV, vdstOf])) fun s₃ ⟨⟨k₃, i₃, b₃⟩, hv₃⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (WP.preservedV (fin2Args_ok hH.stream hp k₃) (by rfl)) fun t₃ ⟨⟨kt₃, a₃, si₃, mt₃⟩, hva₃⟩ =>
    finCall_ok hH.stream hp kt₃ a₃ fun s₄ hv₄ k₄ f₄ d₄ => ?_))
  refine WP.mono (WP.preservedV (out_ok hH hp k₄) (by
    rw [Code.allInstrs_eq]; simp [Hash.finOut, Hash.copy32, Impl.Pbkdf2.AArch64.cp32,
      Impl.Hmac.Generic.AArch64.Hash.restore, Impl.Hmac.Generic.AArch64.Hash.saved, instrs, keepsV, vdstOf]))
    fun s' ⟨⟨s₅, k₅, m₅, hm, hsp, hg, ho⟩, hv₅⟩ => ⟨abi_of k₅ hsp (fun r hr => by
      rw [hv₅ r hr, hv₄ r hr, hva₃ r hr, hv₃ r hr, hv₂ r hr, hva₁ r hr, hv₁ r hr]) hg ho, ?_⟩
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
  have dig : (bytesAt s₂.mem (T (H := H.stream) s₀) H.P.N).take H.D = _ := d₂ _ (m₁ ▸ repr_keep hH.stream f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [si₁, hcnt, hl0])
  -- The inner state now represents the outer block and the digest.
  have hxl : (xorPad k0 opad).length = H.P.B := by rw [xorPad_length, hk0]
  have e1 : (H.P.B + H.D) / H.P.B = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hB0, Nat.div_eq_of_lt (by omega)]
  have e2 : (H.P.B + H.D) % H.P.B = H.D := by
    rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have rO := (hH.repr _ _ _).1 rO₂
  have hl₃ : (xorPad k0 opad ++ bytesAt s₂.mem (T (H := H.stream) s₀) H.D).length = H.P.B + H.D := by
    rw [List.length_append, hxl, bytesAt_length]
  have rI₃ : hH.SH.Repr s₃.mem (inn s₀) (xorPad k0 opad ++ bytesAt s₂.mem (T (H := H.stream) s₀) H.D) := by
    refine (hH.repr _ _ _).2 ⟨?_, ?_⟩
    · rw [hl₃, e1, hH.reloc s₂.mem s₃.mem (outer s₀) (inn s₀) i₃, rO.1, hxl, Nat.div_self hB0]
      exact (hH.md.compressList_append (by rw [hxl]; omega)).symm
    · rw [hl₃, e2, e1, Nat.mul_one, List.drop_left' hxl, b₃]
  have dig₂ : (bytesAt s₄.mem (T (H := H.stream) s₀) H.P.N).take H.D = _ :=
    d₄ _ (mt₃ ▸ rI₃) (by rw [hl₃]; omega) (by rw [si₃, hl₃]; rfl)
  show bytesAt s'.mem (op s₀) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hH.hD, hm, m₅, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), bytesAt_take _ _ hDN, dig₂,
    bytesAt_take _ _ hDN, dig]
  rfl

end

/-! ## Constant time -/

section
open VG.Proof.Hmac.Generic.AArch64.Finalize (kr_agree eqs kr_rel fin_rel')

variable {sc : Nat} {s₀ s₀' : State} (hp : Pre (H := H.stream) sc s₀) (hp' : Pre (H := H.stream) sc s₀')
  (hq : PubEq s₀ s₀')
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
  have fin2 := fin_rel' hH.stream hp hp' hq (c := BitVec.ofNat 64 (H.stream.B + H.stream.D))
    (F := KR (H := H.stream) s₀) (F' := KR (H := H.stream) s₀') hc.fin2
    (fun _ _ h h' => kr_agree hq h h')
    (fun s k => fin2Args_ok hH.stream hp k) (fun s k => fin2Args_ok hH.stream hp' k)
  have mid := kr_rel hp hp' hq hc.mid fun hp s k => WP.mono (mid_ok hH hp k) fun _ h => h.1
  obtain ⟨_, hr⟩ := hc.out
  have out : RelCT isa (fun s s' => KR (H := H.stream) s₀ s ∧ KR (H := H.stream) s₀' s') (.block H.finOut)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 h.2
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact pro.seq (fin1.seq (mid.seq (fin2.seq out)))

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
