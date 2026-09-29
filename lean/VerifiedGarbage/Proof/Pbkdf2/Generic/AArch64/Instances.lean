import VerifiedGarbage.Impl.Pbkdf2.Generic.AArch64
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Hashes

/-!
# PBKDF2-HMAC over any streaming hash function on AArch64: `iterate`, correct

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Pbkdf2/Generic/X86_64/Instances.lean`), from the state `s₀` before the
first instruction, which zero-extends `n`.
-/

namespace VG.Proof.Pbkdf2.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash copy)
open VG.Impl.Pbkdf2.Generic.AArch64 (stO tmpO uO xorLoop count2 atSt body prologue main iterate)
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.Hmac.Generic.AArch64.Init (untouched)
open VG.Proof.Hmac.Generic.AArch64.Finalize (add_zero')
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub xorBytes_length')
open VG.Proof.Hmac.Generic.Common (sub_of_off sub_of_self bytes_keep)
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (xorPad_length)
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt sub_offset)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_movz wp_addImm wp_subImm eval_zero eval_nonzero
  ofNat_beq_zero)
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev key : Addr := s₀.gpr .x0
abbrev up : Addr := s₀.gpr .x1
abbrev tp : Addr := s₀.gpr .x3
abbrev scr : Addr := s₀.gpr .x4
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .x2).setWidth 32).toNat
abbrev keyR : Region := ⟨key s₀, 2 * H.S⟩
abbrev uR : Region := ⟨up s₀, H.D⟩
abbrev tR : Region := ⟨tp s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev stkR : Region := below s₀.sp 16
/-- The state being hashed, the inner digest and `U`, in `scratch`. -/
abbrev ST : Addr := scr s₀ + BitVec.ofNat 64 (stO H)
abbrev TM : Addr := scr s₀ + BitVec.ofNat 64 (tmpO H)
abbrev UA : Addr := scr s₀ + BitVec.ofNat 64 (uO H)
abbrev calR : Region := ⟨scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR (H := H) s₀, uR (H := H) s₀]
  wr : s₀.wr = [tR (H := H) s₀, scR sc s₀]
  k_t : (keyR (H := H) s₀).Disjoint (tR (H := H) s₀)
  k_s : (keyR (H := H) s₀).Disjoint (scR sc s₀)
  u_t : (uR (H := H) s₀).Disjoint (tR (H := H) s₀)
  u_s : (uR (H := H) s₀).Disjoint (scR sc s₀)
  t_s : (tR (H := H) s₀).Disjoint (scR sc s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_k : (stkR s₀).Disjoint (keyR (H := H) s₀)
  stk_u : (stkR s₀).Disjoint (uR (H := H) s₀)
  stk_t : (stkR s₀).Disjoint (tR (H := H) s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  knw : (key s₀).toNat + 2 * H.S ≤ 2 ^ 64
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + H.S + 2 * H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (iterG hH.SH sc).pre s₀) (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hfit,
    ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem bounds : H.buf = 8 * H.W + 56 ∧ H.buf + H.S + 2 * H.F ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 64 ∧
    H.W ≤ 64 ∧ 0 < H.S ∧ H.S ≤ 256 ∧ 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64 ∧ 0 < H.B ∧ H.B ≤ 128 :=
  ⟨rfl, hp.fits, hp.nw, hp.hW, hp.hS.1, hp.hS.2, hp.hD.1, hp.hD.2.1, hp.hD.2.2, hp.hB.1, hp.hB.2⟩

theorem off_sub {o n : Nat} (h : o + n ≤ 8 * sc) (hn : 0 < n) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega)

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := bounds hp; exact off_sub hp (by omega) (by omega)

theorem st_sub : Region.Sub ⟨ST (H := H) s₀, H.S⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -, -, h0, -⟩ := bounds hp; exact off_sub hp (by simp only [stO]; omega) h0

theorem tm_sub : Region.Sub ⟨TM (H := H) s₀, H.F⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -, -, -, -, h0, h1, -⟩ := bounds hp; exact off_sub hp (by simp only [tmpO]; omega) (by omega)

theorem ua_sub : Region.Sub ⟨UA (H := H) s₀, H.F⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -, -, -, -, h0, h1, -⟩ := bounds hp; exact off_sub hp (by simp only [uO]; omega) (by omega)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; obtain ⟨hb, hf, -⟩ := bounds hp
  exact Region.sub_prefix (by omega)

/-- The parts of `scratch` do not overlap. -/
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 8 * sc) (hb : b + n ≤ 8 * sc)
    (hm : 0 < m) (hn : 0 < n) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 a, m⟩ ⟨scr s₀ + BitVec.ofNat 64 b, n⟩ := by
  have := hp.nw
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

include hH in
theorem cal_disj {b n : Nat} (h : 8 * H.W ≤ b) (hb : b + n ≤ 8 * sc) :
    (calR hH s₀).Disjoint ⟨scr s₀ + BitVec.ofNat 64 b, n⟩ := by
  have := hH.hWb; have := hp.nw
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

end

/-! ## What the pieces keep -/

/-- The registers and memory kept from the prologue on, with `m` steps left:
everything written is in `T`, `scratch` or the stack below the stack
pointer. -/
structure KR (s₀ : State) (m : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = key s₀
  x20 : s.gpr .x20 = tp s₀
  x22 : s.gpr .x22 = BitVec.ofNat 64 m
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame [tR (H := H) s₀, scR sc s₀, stkR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x22, .x23, .x25, .x26, .x27, .x28, .x29]

theorem untouched_kregs : ∀ r ∈ untouched, r ∈ kregs := by decide
theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide
theorem kregs_clob : ∀ r ∈ kregs, r ∉ clob := by decide
theorem untouched_pro : ∀ r ∈ untouched, r ∉ [.x22, .x19, .x20, .x23, .x2] := by decide
theorem untouched_x22 : ∀ r ∈ untouched, r ≠ .x22 := by decide

section
variable {sc : Nat}

/-- `KR` survives changes to other registers, and to memory in `T`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ : State} {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [tR (H := H) s₀, scR sc s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) sc s₀ m s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x22, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (untouched_kregs r hr)).trans (h.cs r hr), h.saved.frame H hf hs,
    h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ : State} {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) {d : Reg} (hd : d ∉ kregs)
    {v : BitVec 64} (u : Upd s s' d v) : KR (H := H) sc s₀ m s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := []) (by rw [u.mem]; exact Frame.refl _ _)
    (by simp) (by simp)

end

theorem _root_.VG.Proof.Hmac.Generic.AArch64.SavedRegs.of_upd {scr : Addr} {s₀ s : State} {m : Mem} {v : BitVec 64} (h : SavedRegs H scr s m)
    (u : Upd s₀ s .x2 v) : SavedRegs H scr s₀ m :=
  ⟨h.x19.trans (u.other _ (by decide)), h.x20.trans (u.other _ (by decide)), h.x21.trans (u.other _ (by decide)),
    h.x22.trans (u.other _ (by decide)), h.x24.trans (u.other _ (by decide)), h.x30.trans (u.other _ (by decide)),
    h.x23.trans (u.other _ (by decide))⟩

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem KR.call {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ ws, Region.Sub r (scR sc s₀)) :
    KR (H := H) sc s₀ m s' := by
  have f := ha.frame
  rw [h.sp] at f
  refine h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.stk_s.symm.sub_left (save_sub hp)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨scR sc s₀, by simp, hsub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem mem_wr : scR sc s₀ ∈ s₀.wr ∧ tR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem save_off {o n : Nat} (ho : 8 * H.W + 56 ≤ o) (h : o + n ≤ 8 * sc) (hn : 0 < n) :
    (saveR H (scr s₀)).Disjoint ⟨scr s₀ + BitVec.ofNat 64 o, n⟩ :=
  part_disj hp (a := 8 * H.W) (m := 56) (by omega) (by have := hp.fits; simp only [Hash.buf] at this; omega)
    h (by omega) hn

theorem off_lt {o : Nat} (ho : o ≤ uO H) : o < 4096 := by
  obtain ⟨hb, -, -, hW, -, hS, -, -, hF, -⟩ := bounds hp
  simp only [uO] at ho; omega

/-! ## The copies of the key's states -/

theorem copyKey_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = 0 ∨ o = H.S) :
    WP isa (copy .x19 o .x23 (stO H) H.S) s fun t => KR (H := H) sc s₀ m t ∧
      Frame [⟨ST (H := H) s₀, H.S⟩] s.mem t.mem ∧
      ∀ msg, hH.SH.Repr s₀.mem (key s₀ + BitVec.ofNat 64 o) msg → hH.SH.Repr t.mem (ST (H := H) s₀) msg := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, -⟩ := bounds hp
  have hkn := hp.knw
  have ksub : Region.Sub ⟨key s₀ + BitVec.ofNat 64 o, H.S⟩ (keyR (H := H) s₀) :=
    sub_offset (by rcases ho with rfl | rfl <;> omega) (by rcases ho with rfl | rfl <;> omega)
  have kR : keyR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have sR : scR sc s₀ ∈ s.wr := by rw [hk.wr]; exact (mem_wr hp).1
  have stsub := st_sub hp
  refine WP.mono (copy_ok (so := o) (d := stO H) (n := H.S) (by decide) (by decide)
    (by rcases ho with rfl | rfl <;> omega) (off_lt hp (by simp only [stO, uO]; omega)) hS0 (by omega)
    (fun k hk' => by rw [hk.x19]; exact inRegions_of_sub kR ksub (by omega) hk')
    (fun k hk' => by rw [hk.x23]; exact inRegions_of_sub sR stsub (by omega) hk')
    (by rw [hk.x19, hk.x23]; exact (hp.k_s.sub_left ksub).sub_right stsub)) fun t c => ?_
  rw [hk.x19, hk.x23] at c
  have fr : Frame [⟨ST (H := H) s₀, H.S⟩] s.mem t.mem :=
    c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have sd : (saveR H (scr s₀)).Disjoint ⟨ST (H := H) s₀, H.S⟩ :=
    save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega) hS0
  refine ⟨hk.keep c.rd c.wr c.sp (fun r hr => c.other r (kregs_clob r hr))
    fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sd)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, stsub⟩),
    fr, fun msg hr => ?_⟩
  refine hH.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [c.mem, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi]
  -- The key's bytes are those of the initial memory.
  refine hk.frame.bytes (R := ⟨key s₀ + BitVec.ofNat 64 o, H.S⟩) ?_ (by show H.S ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.k_t.sub_left ksub
  · exact hp.k_s.sub_left ksub
  · exact hp.stk_k.symm.sub_left ksub

/-! ## The calls -/

theorem updArgs_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = uO H ∨ o = tmpO H) :
    WP isa (.block (atSt H ++ [.movz .x .x1 (BitVec.ofNat 16 H.B) 0, .addImm .x .x2 .x23 o,
      .movz .x .x3 (BitVec.ofNat 16 H.D) 0, mov .x4 .x23])) s fun t =>
        KR (H := H) sc s₀ m t ∧ UpdArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) H.D ∧
        t.gpr .x1 = BitVec.ofNat 64 H.B ∧ t.mem = s.mem := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by rcases ho with rfl | rfl <;> omega
  have sR : scR sc s₀ ∈ s₀.wr := (mem_wr hp).1
  have dsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  simp only [atSt, List.cons_append, List.nil_append]
  refine wp_addImm (off_lt hp (by omega)) fun s₁ u₁ => wp_movz fun s₂ u₂ =>
    wp_addImm (off_lt hp (by omega)) fun s₃ u₃ => wp_movz fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k₅ : KR (H := H) sc s₀ m s₅ :=
    ((((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅
  refine ⟨k₅, ?_, by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      movz_ofNat (by omega)], by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, hk.x23]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), hk.x23]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, movz_ofNat (by omega), toNat_ofNat_lt (by omega)]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), hk.x23]
      cd := by
        rw [k₅.rd, k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (List.mem_append_right _ sR) (by omega)
      cw := by
        rw [k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_off sR (by omega)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_sc := (cal_disj hH hp (by omega) (by omega)).symm
      d_st := part_disj hp (by omega) (by omega) (by omega) hD0 hS0
      d_sc := (cal_disj hH hp (by omega) (by omega)).symm
      sp16 := by rw [k₅.sp]; exact hp.sp16
      stk_st := by rw [k₅.sp]; exact hp.stk_s.sub_right (st_sub hp)
      stk_d := by rw [k₅.sp]; exact hp.stk_s.sub_right dsub
      stk_sc := by rw [k₅.sp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem updCall_ok {m : Nat} {t : State} (hk : KR (H := H) sc s₀ m t) {d : Addr}
    (ha : UpdArgs hH t (ST (H := H) s₀) d (scr s₀) H.D) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ m s' → Frame [⟨ST (H := H) s₀, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ msg, hH.SH.Repr t.mem (ST (H := H) s₀) msg → t.gpr .x1 = BitVec.ofNat 64 msg.length →
        hH.SH.Repr s'.mem (ST (H := H) s₀) (msg ++ bytesAt t.mem d H.D)) → Q s') :
    WP isa (.call H.updN H.updC) t Q := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  refine upd_call hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [hk.sp] at f
  refine hQ s' (hk.call hp ha' ?_ ?_) f hpost
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega) hS0
    · exact ((cal_disj hH hp (b := 8 * H.W) (n := 56) (Nat.le_refl _) (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact st_sub hp
    · exact cal_sub hH hp

theorem finArgs_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = uO H ∨ o = tmpO H) :
    WP isa (.block (atSt H ++ count2 H ++ [.addImm .x .x2 .x23 o, mov .x3 .x23])) s fun t =>
        KR (H := H) sc s₀ m t ∧ FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) ∧
        t.gpr .x1 = BitVec.ofNat 64 (H.B + H.D) ∧ t.mem = s.mem := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by rcases ho with rfl | rfl <;> omega
  have sR : scR sc s₀ ∈ s₀.wr := (mem_wr hp).1
  have osub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, H.F⟩ (scR sc s₀) := off_sub hp (by omega) (by omega)
  simp only [atSt, count2, List.cons_append, List.nil_append]
  refine wp_addImm (off_lt hp (by omega)) fun s₁ u₁ => wp_movz fun s₂ u₂ =>
    wp_addImm (off_lt hp (by omega)) fun s₃ u₃ => wp_mov fun s₄ u₄ => WP.block_nil ?_
  have k₄ : KR (H := H) sc s₀ m s₄ :=
    (((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  refine ⟨k₄, ?_, by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, movz_ofNat (by omega)],
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { x0 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.x23]
      x2 := by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.x23]
      x3 := by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.x23]
      cw := by
        rw [k₄.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_off sR (by omega)
          · exact sub_of_off sR (by omega)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_o := part_disj hp (by omega) (by omega) (by omega) hS0 (by omega)
      st_sc := (cal_disj hH hp (by omega) (by omega)).symm
      o_sc := (cal_disj hH hp (by omega) (by omega)).symm
      sp16 := by rw [k₄.sp]; exact hp.sp16
      stk_st := by rw [k₄.sp]; exact hp.stk_s.sub_right (st_sub hp)
      stk_o := by rw [k₄.sp]; exact hp.stk_s.sub_right osub
      stk_sc := by rw [k₄.sp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem finCall_ok {m : Nat} {t : State} (hk : KR (H := H) sc s₀ m t) {o : Nat} (ho : o = uO H ∨ o = tmpO H)
    (ha : FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀)) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ m s' →
      Frame [⟨ST (H := H) s₀, H.S⟩, ⟨scr s₀ + BitVec.ofNat 64 o, H.F⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ msg, hH.SH.Repr t.mem (ST (H := H) s₀) msg → msg.length < 2 ^ 64 →
        t.gpr .x1 = BitVec.ofNat 64 msg.length →
        (bytesAt s'.mem (scr s₀ + BitVec.ofNat 64 o) H.F).take H.D = hH.SH.H.hash msg) → Q s') :
    WP isa (.call H.finN H.finC) t Q := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by rcases ho with rfl | rfl <;> omega
  refine fin_call hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [hk.sp] at f
  refine hQ s' (hk.call hp ha' ?_ ?_) f hpost
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact save_off hp (by omega) (by omega) hS0
    · exact save_off hp (by omega) (by omega) (by omega)
    · exact ((cal_disj hH hp (b := 8 * H.W) (n := 56) (Nat.le_refl _) (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact st_sub hp
    · exact off_sub hp (by omega) (by omega)
    · exact cal_sub hH hp

/-! ## `T ← T ⊕ U` and the count -/

theorem xor'_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) :
    WP isa (xorLoop H) s fun t => KR (H := H) sc s₀ m t ∧
      t.mem = writeBytes s.mem (tp s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp s₀) H.D)
        (bytesAt s.mem (UA (H := H) s₀) H.D)) := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = H.buf + H.S + H.F := rfl
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have usub : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  refine WP.mono (xor_ok (uo := uO H) (n := H.D) (off_lt hp (Nat.le_refl _)) hD0 (by omega)
    (fun k hk' => by
      rw [hk.x23, hk.rd, hk.wr]; exact inRegions_of_sub (List.mem_append_right _ sR) usub (by omega) hk')
    (fun k hk' => by rw [hk.x20, hk.wr]; exact inRegions_of_sub tR' (fun _ h => h) (by omega) hk')
    (by rw [hk.x23, hk.x20]; exact hp.t_s.symm.sub_left usub)) fun t x => ?_
  rw [hk.x23, hk.x20] at x
  refine ⟨hk.keep x.rd x.wr x.sp (fun r hr => x.other r (kregs_clob r hr))
    (x.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := tR (H := H) s₀) (by
      rw [xorBytes_length' _ _ (by simp [bytesAt_length]), bytesAt_length]; exact Region.contains_self _ _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.symm.sub_left (save_sub hp))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩), x.mem⟩

omit hp in
theorem dec_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) {s : State} (hk : KR (H := H) sc s₀ m s) :
    WP isa (.block [.subImm .x .x22 .x22 1]) s fun t => KR (H := H) sc s₀ (m - 1) t ∧ t.mem = s.mem :=
  wp_subImm (by decide) fun t u => WP.block_nil ⟨⟨by rw [u.rd, hk.rd], by rw [u.wr, hk.wr],
    by rw [u.sp, hk.sp], by rw [u.other _ (by decide), hk.x19], by rw [u.other _ (by decide), hk.x20],
    by rw [u.gpr, hk.x22, sub_ofNat' hm hn], by rw [u.other _ (by decide), hk.x23],
    fun r hr => (u.other r (untouched_x22 r hr)).trans (hk.cs r hr), u.mem ▸ hk.saved, u.mem ▸ hk.frame⟩,
    u.mem⟩

end

/-! ## One step -/

/-- The key's states represent `K₀ ⊕ ipad` and `K₀ ⊕ opad`. -/
def KeyOK (s₀ : State) (k0 : List Byte) : Prop :=
  k0.length = H.B ∧ hH.SH.Repr s₀.mem (key s₀) (xorPad k0 ipad) ∧
    hH.SH.Repr s₀.mem (key s₀ + BitVec.ofNat 64 H.S) (xorPad k0 opad)

/-- With `m` steps left, what is left to compute is the rest of the whole. -/
structure Inv (s₀ : State) (m : Nat) (s : State) : Prop where
  kr : KR (H := H) sc s₀ m s
  it : ∀ k0, KeyOK hH s₀ k0 →
    Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (nn s₀) (bytesAt s₀.mem (up s₀) H.D)
        (bytesAt s₀.mem (tp s₀) H.D) =
      Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) m (bytesAt s.mem (UA (H := H) s₀) H.D)
        (bytesAt s.mem (tp s₀) H.D)

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem body_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) {s : State} (h : Inv hH sc s₀ m s) :
    WP isa (body H) s (Inv hH sc s₀ (m - 1)) := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have hwb := hH.hWb
  -- Where things are.
  have stk := hp.stk_s
  have ua : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  have tmD : Region.Sub ⟨TM (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  have dM₁ : Region.Disjoint ⟨TM (H := H) s₀, H.D⟩ ⟨ST (H := H) s₀, H.S⟩ :=
    part_disj hp (by omega) (by omega) (by omega) hD0 hS0
  have dU₁ : Region.Disjoint ⟨UA (H := H) s₀, H.D⟩ ⟨ST (H := H) s₀, H.S⟩ :=
    part_disj hp (by omega) (by omega) (by omega) hD0 hS0
  have dT : ∀ r : Region, Region.Sub r (scR sc s₀) → Region.Disjoint (tR (H := H) s₀) r :=
    fun r hr => hp.t_s.sub_right hr
  have dT₄ : Region.Disjoint (tR (H := H) s₀) (stkR s₀) := hp.stk_t.symm
  have hDn : H.D ≤ 2 ^ 64 := by omega
  -- The pieces.
  refine WP.seq (WP.mono (copyKey_ok hH hp h.kr (.inl rfl)) fun c₁ ⟨kc₁, fc₁, rc₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp kc₁ (.inl rfl)) fun a₁ ⟨ka₁, aa₁, sa₁, ma₁⟩ =>
    updCall_ok hH hp ka₁ aa₁ fun u₁ ku₁ fu₁ ru₁ => ?_))
  refine WP.seq (WP.seq (WP.mono (finArgs_ok hH hp ku₁ (.inr rfl)) fun b₁ ⟨kb₁, ab₁, sb₁, mb₁⟩ =>
    finCall_ok hH hp kb₁ (.inr rfl) ab₁ fun f₁ kf₁ ff₁ rf₁ => ?_))
  refine WP.seq (WP.mono (copyKey_ok hH hp kf₁ (.inr rfl)) fun c₂ ⟨kc₂, fc₂, rc₂⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp kc₂ (.inr rfl)) fun a₂ ⟨ka₂, aa₂, sa₂, ma₂⟩ =>
    updCall_ok hH hp ka₂ aa₂ fun u₂ ku₂ fu₂ ru₂ => ?_))
  refine WP.seq (WP.seq (WP.mono (finArgs_ok hH hp ku₂ (.inl rfl)) fun b₂ ⟨kb₂, ab₂, sb₂, mb₂⟩ =>
    finCall_ok hH hp kb₂ (.inl rfl) ab₂ fun f₂ kf₂ ff₂ rf₂ => ?_))
  refine WP.seq (WP.mono (xor'_ok hp kf₂) fun x ⟨kx, mx⟩ => ?_)
  refine WP.mono (dec_ok hm hn kx) fun t ⟨kt, mt⟩ => ⟨kt, fun k0 hk => ?_⟩
  -- The bytes of `U` and `T` at each point.
  obtain ⟨hl0, hrI, hrO⟩ := hk
  have U₁ : bytesAt c₁.mem (UA (H := H) s₀) H.D = bytesAt s.mem (UA (H := H) s₀) H.D :=
    bytes_keep fc₁ (by simp only [List.mem_singleton]; rintro r rfl; exact dU₁) hDn
  have T₁ : bytesAt c₁.mem (tp s₀) H.D = bytesAt s.mem (tp s₀) H.D :=
    bytes_keep fc₁ (by simp only [List.mem_singleton]; rintro r rfl; exact dT _ (st_sub hp)) hDn
  have T₂ : bytesAt u₁.mem (tp s₀) H.D = bytesAt c₁.mem (tp s₀) H.D := by
    rw [← ma₁]; exact bytes_keep fu₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₃ : bytesAt f₁.mem (tp s₀) H.D = bytesAt u₁.mem (tp s₀) H.D := by
    rw [← mb₁]; exact bytes_keep ff₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (tm_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₄ : bytesAt c₂.mem (tp s₀) H.D = bytesAt f₁.mem (tp s₀) H.D :=
    bytes_keep fc₂ (by simp only [List.mem_singleton]; rintro r rfl; exact dT _ (st_sub hp)) hDn
  have T₅ : bytesAt u₂.mem (tp s₀) H.D = bytesAt c₂.mem (tp s₀) H.D := by
    rw [← ma₂]; exact bytes_keep fu₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₆ : bytesAt f₂.mem (tp s₀) H.D = bytesAt u₂.mem (tp s₀) H.D := by
    rw [← mb₂]; exact bytes_keep ff₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (ua_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have M₄ : bytesAt c₂.mem (TM (H := H) s₀) H.D = bytesAt f₁.mem (TM (H := H) s₀) H.D :=
    bytes_keep fc₂ (by simp only [List.mem_singleton]; rintro r rfl; exact dM₁) hDn
  -- The inner hash.
  have rI₁ := rc₁ _ (by rw [add_zero']; exact hrI)
  have rU₁ := ru₁ _ (ma₁ ▸ rI₁) (by rw [sa₁, xorPad_length, hl0])
  rw [ma₁, U₁] at rU₁
  have hl₁ : (xorPad k0 ipad ++ bytesAt s.mem (UA (H := H) s₀) H.D).length = H.B + H.D := by
    rw [List.length_append, xorPad_length, hl0, bytesAt_length]
  have dig₁ := rf₁ _ (mb₁ ▸ rU₁) (by rw [hl₁]; omega) (by rw [sb₁, hl₁])
  -- The outer hash.
  have rO₂ := rc₂ _ hrO
  have rU₂ := ru₂ _ (ma₂ ▸ rO₂) (by rw [sa₂, xorPad_length, hl0])
  rw [ma₂, M₄, bytesAt_take _ _ hDF, dig₁] at rU₂
  have hl₂ : (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ bytesAt s.mem (UA (H := H) s₀) H.D)).length =
      H.B + H.D := by
    rw [List.length_append, xorPad_length, hl0, ← dig₁, List.length_take, bytesAt_length, Nat.min_eq_left hDF]
  have dig₂ := rf₂ _ (mb₂ ▸ rU₂) (by rw [hl₂]; omega) (by rw [sb₂, hl₂])
  rw [← bytesAt_take _ _ hDF] at dig₂
  -- `T ← T ⊕ U`.
  have hx : (Spec.Pbkdf2.xorBytes (bytesAt f₂.mem (tp s₀) H.D) (bytesAt f₂.mem (UA (H := H) s₀) H.D)).length =
      H.D := by rw [xorBytes_length' _ _ (by simp [bytesAt_length]), bytesAt_length]
  have Ux : bytesAt t.mem (UA (H := H) s₀) H.D = bytesAt f₂.mem (UA (H := H) s₀) H.D := by
    rw [mt, mx]
    exact bytes_keep (Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := tR (H := H) s₀) (by
      rw [hx]; exact Region.contains_self _ _)) (by
        simp only [List.mem_singleton]; rintro r rfl; exact (dT _ ua).symm) hDn
  have Tx : bytesAt t.mem (tp s₀) H.D = Spec.Pbkdf2.xorBytes (bytesAt f₂.mem (tp s₀) H.D)
      (bytesAt f₂.mem (UA (H := H) s₀) H.D) := by
    rw [mt, mx]; exact bytesAt_writeBytes_self' hx (by omega)
  rw [h.it k0 ⟨hl0, hrI, hrO⟩, show m = (m - 1) + 1 by omega, Ux, Tx, dig₂, T₆, T₅, T₄, T₃, T₂, T₁,
    Nat.add_sub_cancel]
  rfl

/-! ## The prologue and the loop -/

omit hp in
theorem nn_lt : nn s₀ < 2 ^ 32 := ((s₀.gpr .x2).setWidth 32).isLt

omit hp in
theorem zx32 (x : BitVec 64) :
    (x.setWidth 32 + BitVec.ofNat 32 0).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit hp in
/-- The first instruction zero-extends `n`. -/
theorem zext_ok : WP isa (.block [.addImm .w .x2 .x2 0]) s₀ fun s => Upd s₀ s .x2 (BitVec.ofNat 64 (nn s₀)) :=
  Proof.MdStream.AArch64.WP.cons (s' := s₀.write .w .x2 ((s₀.gpr .x2).setWidth 32 + BitVec.ofNat 32 0))
    (by simp [exec, State.read]) (WP.block_nil (by
      have u := Upd.write s₀ .w .x2 ((s₀.gpr .x2).setWidth 32 + BitVec.ofNat 32 0)
      exact ⟨by rw [u.gpr]; exact zx32 _, u.other, u.mem, u.rd, u.wr, u.sp⟩))

theorem pro_ok {s : State} (u : Upd s₀ s .x2 (BitVec.ofNat 64 (nn s₀))) :
    WP isa (.block (prologue H)) s fun t => KR (H := H) sc s₀ (nn s₀) t ∧ t.gpr .x1 = up s₀ ∧
      Frame [saveR H (scr s₀)] s₀.mem t.mem := by
  have hL : 8 * H.W + 56 ≤ 8 * sc := by have := hp.fits; simp only [Hash.buf] at this; omega
  refine save_ok H (scr := scr s₀) (u.other _ (by decide)) hp.hW (by rw [u.wr]; exact (mem_wr hp).1) hL
    fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k : ∀ r, r ∉ [.x22, .x19, .x20, .x23, .x2] → s₅.gpr r = s₀.gpr r := fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h1, g₁, u.other r h5]
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have fs : Frame [saveR H (scr s₀)] s₀.mem s₅.mem := by rw [hm, ← u.mem]; exact f₁
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, u.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, u.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁, u.sp],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁,
      u.other _ (by decide)],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁,
      u.other _ (by decide)],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁, u.gpr],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁,
      u.other _ (by decide)],
    fun r hr => k r (untouched_pro r hr), hm ▸ sv₁.of_upd u,
    fs.sub (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨scR sc s₀, by simp, save_sub hp⟩)⟩,
    k _ (by decide), fs⟩

/-- `U` into `scratch`. -/
theorem copyU_ok {s : State} (hk : KR (H := H) sc s₀ (nn s₀) s) (hx1 : s.gpr .x1 = up s₀)
    (hf : Frame [saveR H (scr s₀)] s₀.mem s.mem) :
    WP isa (copy .x1 0 .x23 (uO H) H.D) s (Inv hH sc s₀ (nn s₀)) := by
  obtain ⟨hb, hf', hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = H.buf + H.S + H.F := rfl
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have uR' : uR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have usub : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  refine WP.mono (copy_ok (so := 0) (d := uO H) (n := H.D) (by decide) (by decide) (by decide)
    (off_lt hp (Nat.le_refl _)) hD0 (by omega)
    (fun k hk' => by rw [hx1, add_zero']; exact inRegions_of_sub uR' (fun _ h => h) (by omega) hk')
    (fun k hk' => by rw [hk.x23, hk.wr]; exact inRegions_of_sub sR usub (by omega) hk')
    (by rw [hx1, hk.x23, add_zero']; exact hp.u_s.sub_right usub)) fun t c => ?_
  rw [hx1, hk.x23, add_zero'] at c
  have fc : Frame [⟨UA (H := H) s₀, H.D⟩] s.mem t.mem :=
    c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨hk.keep c.rd c.wr c.sp (fun r hr => c.other r (kregs_clob r hr))
    fc (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact save_off hp (by omega) (by omega) hD0)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, usub⟩), fun k0 _ => ?_⟩
  congr 1
  · rw [c.mem, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    exact (bytes_keep hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.u_s.sub_right (save_sub hp)) (by omega)).symm
  · exact ((bytes_keep fc (by simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right usub)
      (by omega)).trans (bytes_keep hf (by
        simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right (save_sub hp)) (by omega))).symm

omit hp in
theorem zero_eval {s : State} {m : Nat} (hk : KR (H := H) sc s₀ m s) (hm : m < 2 ^ 64) :
    isa.eval (.zero .x .x22) s = some (decide (m = 0)) := by
  show VG.AArch64.eval (.zero .x .x22) s = _
  rw [eval_zero, hk.x22, ofNat_beq_zero hm]

omit hp in
theorem nonzero_eval {s : State} {m : Nat} (hk : KR (H := H) sc s₀ m s) (hm : m < 2 ^ 64) :
    isa.eval (.nonzero .x .x22) s = some (decide (m ≠ 0)) := by
  show VG.AArch64.eval (.nonzero .x .x22) s = _
  rw [eval_nonzero, hk.x22, ofNat_ne_zero hm]

theorem loop_ok {s : State} (h : Inv hH sc s₀ (nn s₀) s) :
    WP isa (.ite (.zero .x .x22) (.block []) (.loop (body H) (.nonzero .x .x22))) s (Inv hH sc s₀ 0) := by
  have hlt := nn_lt (s₀ := s₀)
  refine WP.ite (decide (nn s₀ = 0)) (zero_eval h.kr (by omega)) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have e : nn s₀ = 0 := by simpa using h0
    exact e ▸ h
  · have hpos : 1 ≤ nn s₀ := by have := of_decide_eq_false h0; omega
    refine WP.loop (M := isa) (fun k t => ∃ m, k = m ∧ 1 ≤ m ∧ m ≤ nn s₀ ∧ Inv hH sc s₀ m t) ?_ (nn s₀) s
      ⟨nn s₀, rfl, hpos, (Nat.le_refl _), h⟩
    rintro k t ⟨m, hkm, h1, h2, ht⟩
    refine WP.mono (body_ok hH hp h1 (by omega) ht) fun t' ht' => ?_
    have hz := nonzero_eval ht'.kr (show m - 1 < 2 ^ 64 by omega)
    by_cases hl : m - 1 = 0
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ ht'⟩
    · exact .inr ⟨by rw [hz]; simp [hl], m - 1, by omega, m - 1, rfl, by omega, by omega, ht'⟩

omit hp in
/-- The end: `abiPreserved`, from `KR` and `restore`. -/
theorem abi_of {m : Nat} {s s' : State} (hk : KR (H := H) sc s₀ m s) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) (ho : ∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, by rw [hsp, hk.sp]⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hg _ (by decide)
    | exact (ho _ (by decide)).trans (hk.cs _ (by decide))

theorem correct : WP isa (iterate H) s₀ fun s' => abiPreserved s₀ s' ∧ (iterG hH.SH sc).post s₀ s' := by
  obtain ⟨hb, hf', hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  refine WP.seq (WP.mono (zext_ok (s₀ := s₀)) fun s₁ u₁ => ?_)
  refine WP.seq (WP.mono (pro_ok hp u₁) fun s₂ ⟨k₂, x₂, f₂⟩ => ?_)
  refine WP.seq (WP.mono (copyU_ok hH hp k₂ x₂ f₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop_ok hH hp h₃) fun s₄ h₄ => ?_)
  have k₄ := h₄.kr
  have hL : 8 * H.W + 56 ≤ 8 * sc := by omega
  refine WP.mono (restore_ok H k₄.x23 hW k₄.saved (by rw [k₄.wr]; exact (mem_wr hp).1) hL)
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨abi_of k₄ hsp hg ho, ?_⟩
  intro k0 hl hrI hrO
  have hS' := hH.hS; have hD' := hH.hD; have hB' := hH.hB
  rw [hB'] at hl
  rw [hS'] at hrO
  show bytesAt s'.mem (tp s₀) hH.SH.digestBytes = _
  rw [hD', hm, h₄.it k0 ⟨hl, hrI, hrO⟩]
  rfl

end

end VG.Proof.Pbkdf2.Generic.AArch64

/-!
# PBKDF2-HMAC over any streaming hash function on AArch64: `iterate`, constant time

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Pbkdf2/Generic/X86_64/Instances.lean`).
-/

namespace VG.Proof.Pbkdf2.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash copy)
open VG.Impl.Pbkdf2.Generic.AArch64 (stO tmpO uO xorLoop count2 atSt body prologue main iterate)
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.MdStream.AArch64 (Upd)
open VG.Proof.Hmac.Generic.AArch64

/-- The arguments, once `n` is zero-extended. -/
abbrev args : List Reg := [.x0, .x1, .x2, .x3, .x4]

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x22, .x23]

/-- The block that sets up a call of `update` on the state, with `D` bytes at `scratch + o`. -/
abbrev updBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ [.movz .x .x1 (BitVec.ofNat 16 H.B) 0, .addImm .x .x2 .x23 o,
    .movz .x .x3 (BitVec.ofNat 16 H.D) 0, mov .x4 .x23]

/-- The block that sets up a call of `finalize` on the state, into `scratch + o`. -/
abbrev finBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ count2 H ++ [.addImm .x .x2 .x23 o, mov .x3 .x23]

theorem zext_check :
    ∃ hc, (Taint.check taint (Taint.ofRegs []) (.block [.addImm .w .x2 .x2 0]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem skip_check : ∃ hc, (Taint.check taint (Taint.ofRegs []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block (prologue H)) hc).isSome = true
  copyU : ∃ hc, (Taint.check taint (Taint.ofRegs (.x1 :: pubRegs)) (copy .x1 0 .x23 (uO H) H.D) hc).isSome = true
  copyK : ∀ o ∈ [0, H.S], ∃ hc,
    (Taint.check taint (Taint.ofRegs pubRegs) (copy .x19 o .x23 (stO H) H.S) hc).isSome = true
  upd : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H o)) hc).isSome = true
  fin : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (Taint.check taint (Taint.ofRegs pubRegs) (.block (finBlock H o)) hc).isSome = true
  xor : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (xorLoop H) hc).isSome = true
  dec : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block [.subImm .x .x22 .x22 1]) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same (`n` in its 32 bits). -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : (s₀.gpr .x2).setWidth 32 = (s₀'.gpr .x2).setWidth 32
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

variable {H : Hash} (hH : HashOK H) {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : Generic.AArch64.nn s₀ = Generic.AArch64.nn s₀' := by
  show ((s₀.gpr .x2).setWidth 32).toNat = ((s₀'.gpr .x2).setWidth 32).toNat; rw [hq.x2]

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s)
    (h' : KR (H := H) sc s₀' m s') : s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, key, key, hq.x0]
  · rw [h.x20, h'.x20, tp, tp, hq.x3]
  · rw [h.x22, h'.x22]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]

theorem eqs (hq : PubEq s₀ s₀') :
    ST (H := H) s₀' = ST (H := H) s₀ ∧ scr s₀' = scr s₀ ∧
      ∀ o : Nat, scr s₀' + BitVec.ofNat 64 o = scr s₀ + BitVec.ofNat 64 o :=
  ⟨by show s₀'.gpr .x4 + _ = s₀.gpr .x4 + _; rw [hq.x4], hq.x4.symm, fun o => by rw [scr, scr, hq.x4]⟩

include hH hp hp' hq

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {m : Nat} {c : Prog isa}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) sc t₀ m s → WP isa c s (KR (H := H) sc t₀ m)) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') c
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
  rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

theorem upd_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callUpd (atSt H) H.B o H.D)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq (H := H)
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      UpdArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) H.D ∧ t.gpr .x1 = BitVec.ofNat 64 H.B)
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      UpdArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) H.D ∧ t.gpr .x1 = BitVec.ofNat 64 H.B)
    pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.upd o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (updArgs_ok hH hp h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (updArgs_ok hH hp' h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e3 o ▸ e2 ▸ a, x1⟩)
  exact ha.seq (rel_wp (upd_rel hH (st := ST (H := H) s₀) (d := scr s₀ + BitVec.ofNat 64 o) (sc := scr s₀)
    (len := H.D) fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k (e1.symm ▸ e3 o ▸ e2.symm ▸ a) fun _ k' _ _ => k'))

theorem fin_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callFin (atSt H) (count2 H) o)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq (H := H)
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 (H.B + H.D))
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) ∧
      t.gpr .x1 = BitVec.ofNat 64 (H.B + H.D))
    pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.fin o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (finArgs_ok hH hp h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (finArgs_ok hH hp' h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e3 o ▸ e2 ▸ a, x1⟩)
  exact ha.seq (rel_wp (fin_rel hH (st := ST (H := H) s₀) (o := scr s₀ + BitVec.ofNat 64 o) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k ho (e1.symm ▸ e3 o ▸ e2.symm ▸ a) fun _ k' _ _ => k'))

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') (body H)
      fun s s' => KR (H := H) sc s₀ (m - 1) s ∧ KR (H := H) sc s₀' (m - 1) s' := by
  have ck : ∀ {o : Nat}, (o = 0 ∨ o = H.S) → RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (copy .x19 o .x23 (stO H) H.S) fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
    fun ho => kr_rel hp hp' hq (m := m) (hc.copyK _ (by rcases ho with rfl | rfl <;> simp))
      fun hp s k => WP.mono (copyKey_ok hH hp k ho) fun _ h => h.1
  have x := kr_rel hp hp' hq (m := m) hc.xor fun hp s k => WP.mono (xor'_ok hp k) fun _ h => h.1
  have d := rel_taint (G := KR (H := H) sc s₀ (m - 1)) (G' := KR (H := H) sc s₀' (m - 1)) pubRegs
    (fun _ _ h h' => kr_agree hq h h') hc.dec
    (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1) (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1)
  exact (ck (.inl rfl)).seq ((upd_rel' hH hp hp' hq (.inl rfl) hc).seq ((fin_rel' hH hp hp' hq (.inr rfl) hc).seq
    ((ck (.inr rfl)).seq ((upd_rel' hH hp hp' hq (.inr rfl) hc).seq ((fin_rel' hH hp hp' hq (.inl rfl) hc).seq
    (x.seq d))))))

/-- The loop's invariant in two runs, with `n` steps left. -/
abbrev LoopInv (n : Nat) (s s' : State) : Prop :=
  1 ≤ n ∧ n ≤ nn s₀ ∧ Inv hH sc s₀ n s ∧ Inv hH sc s₀' n s'

theorem step_rel (hc : Checks H) (n : Nat) :
    RelCT isa (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n) (body H) fun s s' =>
      isa.eval (.nonzero .x .x22) s = isa.eval (.nonzero .x .x22) s' ∧
      (isa.eval (.nonzero .x .x22) s = some false → Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') ∧
      (isa.eval (.nonzero .x .x22) s = some true →
        ∃ m < n, LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') m s s') := by
  have hlt := nn_lt (s₀ := s₀)
  by_cases hn : 1 ≤ n ∧ n ≤ nn s₀
  · have b := (body_rel hH hp hp' hq hc hn.1 (by omega)).mono (P' := LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n)
      (fun _ _ (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) => ⟨h.2.2.1.kr, h.2.2.2.kr⟩)
      fun _ _ h => h
    refine (b.wp (F₁ := Inv hH sc s₀ (n - 1)) (F₂ := Inv hH sc s₀' (n - 1))
      fun s s' (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) =>
        ⟨body_ok hH hp hn.1 (by omega) h.2.2.1, body_ok hH hp' hn.1 (by omega) h.2.2.2⟩).mono
      (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨_, i, i'⟩ := h
    rw [nonzero_eval i.kr (by omega), nonzero_eval i'.kr (by omega)]
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : n - 1 = 0 := by simpa using hf
      exact ⟨hl ▸ i, hl ▸ i'⟩
    · have hl : n - 1 ≠ 0 := by simpa using ht
      exact ⟨n - 1, by omega, by omega, by omega, i, i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel (hc : Checks H) :
    RelCT isa (fun s s' => Inv hH sc s₀ (nn s₀) s ∧ Inv hH sc s₀' (nn s₀') s')
      (.ite (.zero .x .x22) (.block []) (.loop (body H) (.nonzero .x .x22)))
      fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s' := by
  have hN := hq.nn
  have hlt := nn_lt (s₀ := s₀)
  have hlt' := nn_lt (s₀ := s₀')
  refine RelCT.ite (fun s s' h => by rw [zero_eval h.1.kr (by omega), zero_eval h.2.kr (by omega), hN]) ?_ ?_
  · by_cases e : nn s₀ = 0
    · have e' : nn s₀' = 0 := hN ▸ e
      exact (rel_taint (c := .block []) (F := Inv hH sc s₀ (nn s₀)) (F' := Inv hH sc s₀' (nn s₀'))
        (G := Inv hH sc s₀ 0) (G' := Inv hH sc s₀' 0) []
        (fun s s' h h' => ⟨by rw [h.kr.sp, h'.kr.sp, hq.sp], by simp⟩) skip_check
        (fun s h => WP.block_nil (e ▸ h)) (fun s h => WP.block_nil (e' ▸ h))).mono (fun _ _ h => h.1)
        fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [zero_eval h.1.1.kr (by omega)] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀')) (step_rel hH hp hp' hq hc)
      (nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [zero_eval h.1.1.kr (by omega)] at z
    have e : nn s₀ ≠ 0 := by simpa using z
    exact ⟨by omega, (Nat.le_refl _), h.1.1, hN ▸ h.1.2⟩

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate H) fun _ _ => True := by
  have hN := hq.nn
  have zx := rel_taint (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => Upd s₀ s .x2 (BitVec.ofNat 64 (nn s₀))) (G' := fun s => Upd s₀' s .x2 (BitVec.ofNat 64 (nn s₀')))
    [] (fun s s' e e' => ⟨by rw [e, e', hq.sp], by simp⟩) zext_check
    (fun _ e => by rw [e]; exact zext_ok) (fun _ e => by rw [e]; exact zext_ok)
  have pro := rel_taint (F := fun s => Upd s₀ s .x2 (BitVec.ofNat 64 (nn s₀)))
    (F' := fun s => Upd s₀' s .x2 (BitVec.ofNat 64 (nn s₀')))
    (G := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .x1 = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (G' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .x1 = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    args (fun s s' u u' => ⟨by rw [u.sp, u'.sp, hq.sp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [u.other _ (by decide), u'.other _ (by decide), hq.x0]
        · rw [u.other _ (by decide), u'.other _ (by decide), hq.x1]
        · rw [u.gpr, u'.gpr, hN]
        · rw [u.other _ (by decide), u'.other _ (by decide), hq.x3]
        · rw [u.other _ (by decide), u'.other _ (by decide), hq.x4]⟩) hc.pro
    (fun _ u => pro_ok hp u) (fun _ u => pro_ok hp' u)
  have cu := rel_taint
    (F := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .x1 = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (F' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .x1 = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (G := Inv hH sc s₀ (nn s₀)) (G' := Inv hH sc s₀' (nn s₀')) (.x1 :: pubRegs)
    (fun s s' h h' => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1 (hN ▸ h'.1)
      refine ⟨sp, fun r hm => ?_⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [h.2.1, h'.2.1, up, up, hq.x1]
      · exact hr r hm) hc.copyU
    (fun s h => copyU_ok hH hp h.1 h.2.1 h.2.2) (fun s h => copyU_ok hH hp' h.1 h.2.1 h.2.2)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h => by
      obtain ⟨sp, hr⟩ := kr_agree hq h.1.kr h.2.kr
      exact ⟨sp, fun r hm => hr r (Taint.mem_ofRegs.mp hm)⟩) hr
  exact zx.seq (pro.seq (cu.seq ((loop_rel hH hp hp' hq hc).seq restore)))

end VG.Proof.Pbkdf2.Generic.AArch64

namespace VG.Proof.Pbkdf2.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64

/-- `iterate` is verified against `iterG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) (hsat : ∃ s, (iterG hH.SH sc).pre s) :
    Verified AArch64.target (VG.Impl.Pbkdf2.Generic.AArch64.iterate H) (iterG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Generic.AArch64

/-!
# PBKDF2-HMAC over the streaming hash functions on AArch64: the instances

Untrusted: everything here is checked by Lean. The generic proof
(above) at each hash function of
`Proof/Hmac/Generic/AArch64/Hashes.lean`, moved to the shared contract of
`Spec/Pbkdf2/Generic.lean` (`sig_implies`), which the artifacts are emitted
with.
-/

namespace VG.Proof.Pbkdf2.Generic.AArch64.Instances

open VG.AArch64
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.Pbkdf2.Generic.AArch64

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 sc` bytes of scratch space. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x3 => 0x30000 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x10000, 2 * S⟩, ⟨0x20000, D⟩]
  wr := [⟨0x30000, D⟩, ⟨0x40000, 8 * sc⟩]

/-- `iterG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem iterImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Pbkdf2.iterateContract S W AArch64.abi 16).pre s) :
    (iterG S W).Implies (Spec.Pbkdf2.iterateContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, iterG, stk, AArch64.abi, AArch64.argRegs] using h

/-! ## SHA-1 -/

theorem sha1_checks : Checks sha1H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  dec := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha1_imp : (iterG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract AArch64.abi 16) :=
  iterImp Spec.Hmac.sha1S 56 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterG, stk, AArch64.abi, AArch64.argRegs] using iterSat 84 20 56)

theorem sha1 : Verified AArch64.target (Impl.Pbkdf2.Generic.AArch64.iterate sha1H)
    (Spec.Hmac.sha1I.iterateContract AArch64.abi 16) :=
  (verified sha1OK sha1_checks (by decide) sha1_imp.sat_left).of_implies sha1_imp

/-! ## MD5 -/

theorem md5_checks : Checks md5H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  dec := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem md5_imp : (iterG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract AArch64.abi 16) :=
  iterImp Spec.Hmac.md5S 48 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, iterG, stk, AArch64.abi, AArch64.argRegs] using iterSat 80 16 48)

theorem md5 : Verified AArch64.target (Impl.Pbkdf2.Generic.AArch64.iterate md5H)
    (Spec.Hmac.md5I.iterateContract AArch64.abi 16) :=
  (verified md5OK md5_checks (by decide) md5_imp.sat_left).of_implies md5_imp

/-! ## SHA-384 -/

theorem sha384_checks : Checks sha384H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  dec := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha384_imp : (iterG Spec.Hmac.sha384S 96).Implies (Spec.Hmac.sha384I.iterateContract AArch64.abi 16) :=
  iterImp Spec.Hmac.sha384S 96 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterG, stk, AArch64.abi, AArch64.argRegs] using iterSat 192 48 96)

theorem sha384 : Verified AArch64.target (Impl.Pbkdf2.Generic.AArch64.iterate sha384H)
    (Spec.Hmac.sha384I.iterateContract AArch64.abi 16) :=
  (verified sha384OK sha384_checks (by decide) sha384_imp.sat_left).of_implies sha384_imp

/-! ## SHA-512 -/

theorem sha512_checks : Checks sha512H' where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  dec := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_imp : (iterG Spec.Hmac.sha512S 96).Implies (Spec.Hmac.sha512I.iterateContract AArch64.abi 16) :=
  iterImp Spec.Hmac.sha512S 96 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterG, stk, AArch64.abi, AArch64.argRegs] using iterSat 192 64 96)

theorem sha512 : Verified AArch64.target (Impl.Pbkdf2.Generic.AArch64.iterate sha512H')
    (Spec.Hmac.sha512I.iterateContract AArch64.abi 16) :=
  (verified sha512OK sha512_checks (by decide) sha512_imp.sat_left).of_implies sha512_imp

/-! ## SHA-512/224 -/

theorem sha512_224_checks : Checks sha512_224H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  dec := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_224_imp : (iterG Spec.Hmac.sha512_224S 96).Implies (Spec.Hmac.sha512_224I.iterateContract AArch64.abi 16) :=
  iterImp Spec.Hmac.sha512_224S 96 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, iterG, stk, AArch64.abi, AArch64.argRegs] using iterSat 192 28 96)

theorem sha512_224 : Verified AArch64.target (Impl.Pbkdf2.Generic.AArch64.iterate sha512_224H)
    (Spec.Hmac.sha512_224I.iterateContract AArch64.abi 16) :=
  (verified sha512_224OK sha512_224_checks (by decide) sha512_224_imp.sat_left).of_implies sha512_224_imp

/-! ## SHA-512/256 -/

theorem sha512_256_checks : Checks sha512_256H where
  pro := ⟨_, by taint_decide⟩
  copyU := ⟨_, by taint_decide⟩
  copyK := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  upd := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  fin := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  xor := ⟨_, by taint_decide⟩
  dec := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha512_256_imp : (iterG Spec.Hmac.sha512_256S 96).Implies (Spec.Hmac.sha512_256I.iterateContract AArch64.abi 16) :=
  iterImp Spec.Hmac.sha512_256S 96 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterG, stk, AArch64.abi, AArch64.argRegs] using iterSat 192 32 96)

theorem sha512_256 : Verified AArch64.target (Impl.Pbkdf2.Generic.AArch64.iterate sha512_256H)
    (Spec.Hmac.sha512_256I.iterateContract AArch64.abi 16) :=
  (verified sha512_256OK sha512_256_checks (by decide) sha512_256_imp.sat_left).of_implies sha512_256_imp

end VG.Proof.Pbkdf2.Generic.AArch64.Instances
