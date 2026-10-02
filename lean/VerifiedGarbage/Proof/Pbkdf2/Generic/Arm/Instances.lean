import VerifiedGarbage.Impl.Pbkdf2.Generic.Arm
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Finalize
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Hashes

/-!
# PBKDF2-HMAC over any streaming hash function on 32-bit ARM: `iterate`, correct

As on x86 (`Proof/Pbkdf2/Generic/X86/Iterate.lean`). `scratch` is a stack
argument, loaded into `r12` first; the loop counts the steps left in `r6` down
with `subs`, and branches on its result.
-/

namespace VG.Proof.Pbkdf2.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy scrAt)
open VG.Impl.Pbkdf2.Generic.Arm (stO tmpO uO xorLoop count2 atSt body prologue iterate)
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Hmac.Generic.Arm.Finalize (add_zero')
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub xorBytes_length')
open VG.Proof.Hmac.Generic.Common (sub_of_off sub_of_self bytes_keep)
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Hmac.Common (xorPad_length)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_subs wp_cmp wp_ldrSp op2_imm op2_reg sub_offset
  ofNat_beq_zero sub_ofNat eval_eq eval_ne)
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev key : BitVec 32 := s₀.gpr .r0
abbrev up : BitVec 32 := s₀.gpr .r1
abbrev tp : BitVec 32 := s₀.gpr .r3
abbrev scr : BitVec 32 := stackArg s₀ 0
/-- The number of steps. -/
abbrev nn : Nat := (s₀.gpr .r2).toNat
abbrev keyR : Region := ⟨State.addr (key s₀), 2 * H.S⟩
abbrev uR : Region := ⟨State.addr (up s₀), H.D⟩
abbrev tR : Region := ⟨State.addr (tp s₀), H.D⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 8 * sc⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev stkR : Region := below s₀
/-- Byte `o` of `scratch`, and its address as a register holds it. -/
abbrev SA (o : Nat) : Addr := State.addr (scr s₀) + BitVec.ofNat 64 o
abbrev sO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
/-- The state being hashed, the inner digest and `U`, in `scratch`. -/
abbrev ST : Addr := SA s₀ (stO H)
abbrev TM : Addr := SA s₀ (tmpO H)
abbrev UA : Addr := SA s₀ (uO H)
abbrev calR : Region := ⟨State.addr (scr s₀), hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR (H := H) s₀, uR (H := H) s₀, argR s₀]
  wr : s₀.wr = [tR (H := H) s₀, scR sc s₀]
  k_t : (keyR (H := H) s₀).Disjoint (tR (H := H) s₀)
  k_s : (keyR (H := H) s₀).Disjoint (scR sc s₀)
  u_t : (uR (H := H) s₀).Disjoint (tR (H := H) s₀)
  u_s : (uR (H := H) s₀).Disjoint (scR sc s₀)
  t_s : (tR (H := H) s₀).Disjoint (scR sc s₀)
  a_t : (argR s₀).Disjoint (tR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  b_k : (stkR s₀).Disjoint (keyR (H := H) s₀)
  b_u : (stkR s₀).Disjoint (uR (H := H) s₀)
  b_t : (stkR s₀).Disjoint (tR (H := H) s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  nk : (key s₀).toNat + 2 * H.S ≤ 2 ^ 32
  nu : (up s₀).toNat + H.D ≤ 2 ^ 32
  nt : (tp s₀).toNat + H.D ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.buf + H.S + 2 * H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (iterG hH.SH sc).pre s₀) (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hfit,
    ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem bounds : H.buf = 8 * H.W + 36 ∧ H.buf + H.S + 2 * H.F ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.W ≤ 64 ∧ 0 < H.S ∧ H.S ≤ 256 ∧ 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64 ∧ 0 < H.B ∧ H.B ≤ 128 :=
  ⟨rfl, hp.fits, hp.nw, hp.hW, hp.hS.1, hp.hS.2, hp.hD.1, hp.hD.2.1, hp.hD.2.2, hp.hB.1, hp.hB.2⟩

theorem off_sub {o n : Nat} (h : o + n ≤ 8 * sc) :
    Region.Sub ⟨SA s₀ o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega)

theorem addr_sO {o : Nat} (h : o < 8 * sc) : State.addr (sO s₀ o) = SA s₀ o :=
  addr_add (by have := hp.nw; omega)

theorem toNat_sO {o : Nat} (h : o < 8 * sc) : (sO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := bounds hp; exact off_sub hp (by omega)

theorem st_sub : Region.Sub ⟨ST (H := H) s₀, H.S⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := bounds hp; exact off_sub hp (by simp only [stO]; omega)

theorem tm_sub : Region.Sub ⟨TM (H := H) s₀, H.F⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := bounds hp; exact off_sub hp (by simp only [tmpO]; omega)

theorem ua_sub : Region.Sub ⟨UA (H := H) s₀, H.F⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := bounds hp; exact off_sub hp (by simp only [uO]; omega)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; obtain ⟨hb, hf, -⟩ := bounds hp
  exact Region.sub_prefix (by omega)

/-- The parts of `scratch` do not overlap. -/
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 8 * sc) (hb : b + n ≤ 8 * sc) :
    Region.Disjoint ⟨SA s₀ a, m⟩ ⟨SA s₀ b, n⟩ :=
  VG.Proof.Hmac.Generic.Common.off_disj _ h (by have := hp.nw; omega) (by have := hp.nw; omega)

include hH in
theorem cal_disj {b n : Nat} (h : 8 * H.W ≤ b) (hb : b + n ≤ 8 * sc) :
    (calR hH s₀).Disjoint ⟨SA s₀ b, n⟩ := by
  have := hH.hWb; have := hp.nw
  exact VG.Proof.Hmac.Generic.Common.off_disj0 _ (by omega) (by omega)

end

/-! ## What the pieces keep -/

/-- The registers and memory kept from the prologue on, with `m` steps left:
everything written is in `T`, `scratch` or the stack below the stack
pointer. -/
structure KR (s₀ : State) (m : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = key s₀
  r5 : s.gpr .r5 = tp s₀
  r6 : s.gpr .r6 = BitVec.ofNat 32 m
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame [tR (H := H) s₀, scR sc s₀, stkR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r4, .r5, .r6, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide
theorem kregs_clob : ∀ r ∈ kregs, r ∉ clob := by decide

section
variable {sc : Nat}

/-- `KR` survives changes to other registers, and to memory in `T`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ : State} {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [tR (H := H) s₀, scR sc s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) sc s₀ m s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r4,
    (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r6, (hg _ (by simp)).trans h.r11,
    h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ : State} {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) {d : Reg} (hd : d ∉ kregs)
    {v : BitVec 32} (u : Upd s s' d v) : KR (H := H) sc s₀ m s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := []) (by rw [u.mem]; exact Frame.refl _ _)
    (by simp) (by simp)

end

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem KR.call {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ ws, Region.Sub r (scR sc s₀)) :
    KR (H := H) sc s₀ m s' := by
  have f := ha.frame
  rw [below_eq h.sp] at f
  refine h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.b_s.symm.sub_left (save_sub hp)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨scR sc s₀, by simp, hsub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem mem_wr : scR sc s₀ ∈ s₀.wr ∧ tR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem save_off {o n : Nat} (ho : 8 * H.W + 36 ≤ o) (h : o + n ≤ 8 * sc) :
    (saveR H (scr s₀)).Disjoint ⟨SA s₀ o, n⟩ :=
  part_disj hp (a := 8 * H.W) (m := 36) (by omega) (by have := hp.fits; simp only [Hash.buf] at this; omega) h

theorem off_lt {o : Nat} (ho : o ≤ uO H) : o < 4096 := by
  obtain ⟨hb, -, -, hW, -, hS, -, -, hF, -⟩ := bounds hp
  simp only [uO] at ho; omega

/-! ## The copies of the key's states -/

theorem copyKey_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = 0 ∨ o = H.S) :
    WP isa (copy .r4 o .r11 (stO H) H.S) s fun t => KR (H := H) sc s₀ m t ∧
      Frame [⟨ST (H := H) s₀, H.S⟩] s.mem t.mem ∧
      ∀ msg, hH.SH.Repr s₀.mem (State.addr (key s₀) + BitVec.ofNat 64 o) msg →
        hH.SH.Repr t.mem (ST (H := H) s₀) msg := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, -⟩ := bounds hp
  have hkn := hp.nk
  have ksub : Region.Sub ⟨State.addr (key s₀) + BitVec.ofNat 64 o, H.S⟩ (keyR (H := H) s₀) :=
    sub_offset (by rcases ho with rfl | rfl <;> omega) (by rcases ho with rfl | rfl <;> omega)
  have kR : keyR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have sR : scR sc s₀ ∈ s.wr := by rw [hk.wr]; exact (mem_wr hp).1
  have stsub := st_sub hp
  refine WP.mono (copy_ok (so := o) (d := stO H) (n := H.S) (by decide) (by decide)
    (by rcases ho with rfl | rfl <;> omega) (off_lt hp (by simp only [stO, uO]; omega)) hS0 (by omega)
    (by rw [hk.r4]; rcases ho with rfl | rfl <;> omega) (by rw [hk.r11]; simp only [stO]; omega)
    (fun k hk' => by rw [hk.r4]; exact inRegions_of_sub kR ksub (by omega) hk')
    (fun k hk' => by rw [hk.r11]; exact inRegions_of_sub sR stsub (by omega) hk')
    (by rw [hk.r4, hk.r11]; exact (hp.k_s.sub_left ksub).sub_right stsub)) fun t c => ?_
  rw [hk.r4, hk.r11] at c
  have fr : Frame [⟨ST (H := H) s₀, H.S⟩] s.mem t.mem :=
    c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have sd : (saveR H (scr s₀)).Disjoint ⟨ST (H := H) s₀, H.S⟩ :=
    save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega)
  refine ⟨hk.keep c.rd c.wr c.sp (fun r hr => c.other r (not_cclob (kregs_clob r hr)))
    fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sd)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, stsub⟩),
    fr, fun msg hr => ?_⟩
  refine hH.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [c.mem, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi]
  -- The key's bytes are those of the initial memory.
  refine hk.frame.bytes (R := ⟨State.addr (key s₀) + BitVec.ofNat 64 o, H.S⟩) ?_ (by show H.S ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.k_t.sub_left ksub
  · exact hp.k_s.sub_left ksub
  · exact hp.b_k.symm.sub_left ksub

/-! ## The calls -/

theorem updArgs_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = uO H ∨ o = tmpO H) :
    WP isa (.block (atSt H ++ scrAt .r1 o ++ [.movw .r7 (BitVec.ofNat 16 H.D), .mov .r10 (.reg .r11),
      .movw .r2 (BitVec.ofNat 16 H.B), .mov .r3 (.imm 0)])) s fun t =>
        KR (H := H) sc s₀ m t ∧ UpdArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) H.D ∧
        count t = BitVec.ofNat 64 H.B ∧ t.mem = s.mem := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by rcases ho with rfl | rfl <;> omega
  have sR : scR sc s₀ ∈ s₀.wr := (mem_wr hp).1
  have dsub : Region.Sub ⟨SA s₀ o, H.D⟩ (scR sc s₀) := off_sub hp (by omega)
  have eS := addr_sO hp (o := stO H) (by omega)
  have eO := addr_sO hp (o := o) (by omega)
  simp only [atSt, scrAt, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => wp_movw fun s₃ u₃ =>
    wp_add (op2_reg _ _) fun s₄ u₄ => wp_movw fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ =>
    wp_movw fun s₇ u₇ => wp_mov (op2_imm (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have k₈ : KR (H := H) sc s₀ m s₈ :=
    (((((((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇).upd (by decide) u₈
  refine ⟨k₈, ?_, count_movw (by omega) (by rw [u₈.other _ (by decide), u₇.gpr]) u₈.gpr,
    by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { r0 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr,
          u₁.other _ (by decide), hk.r11, movw_ofNat (by omega)]
      r1 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
          u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), hk.r11, movw_ofNat (by omega)]
      r7 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
          movw_ofNat (by omega)]
      r10 := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
          hk.r11]
      hlen := by omega
      sp16 := by rw [k₈.sp]; exact hp.sp16
      cd := by
        rw [k₈.rd, k₈.wr, eO]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (List.mem_append_right _ sR) (by omega)
      cw := by
        rw [k₈.wr, eS]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_off sR (by omega)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_sc := by rw [eS]; exact (cal_disj hH hp (by omega) (by omega)).symm
      d_st := by rw [eO, eS]; exact part_disj hp (by omega) (by omega) (by omega)
      d_sc := by rw [eO]; exact (cal_disj hH hp (by omega) (by omega)).symm
      b_st := by rw [below_eq k₈.sp, eS]; exact hp.b_s.sub_right (st_sub hp)
      b_d := by rw [below_eq k₈.sp, eO]; exact hp.b_s.sub_right dsub
      b_sc := by rw [below_eq k₈.sp]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := by rw [toNat_sO hp (by omega)]; omega
      nd := by rw [toNat_sO hp (by omega)]; omega
      nsc := by omega }

theorem updCall_ok {m : Nat} {t : State} (hk : KR (H := H) sc s₀ m t) {o : Nat} (ho : o = uO H ∨ o = tmpO H)
    (ha : UpdArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) H.D) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ m s' → Frame [⟨ST (H := H) s₀, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ msg, hH.SH.Repr t.mem (ST (H := H) s₀) msg → count t = BitVec.ofNat 64 msg.length →
        hH.SH.Repr s'.mem (ST (H := H) s₀) (msg ++ bytesAt t.mem (SA s₀ o) H.D)) → Q s') :
    WP isa (.frame (.push upd4) (.call H.updN H.updC) (.pop .r1 16)) t Q := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by rcases ho with rfl | rfl <;> omega
  have eS := addr_sO hp (o := stO H) (by omega)
  have eO := addr_sO hp (o := o) (by omega)
  refine upd_frame hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [below_eq hk.sp, eS] at f
  rw [eS, eO] at hpost
  refine hQ s' (hk.call hp ha' ?_ ?_) f hpost
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [eS]
    rintro r (rfl | rfl)
    · exact save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega)
    · exact ((cal_disj hH hp (b := 8 * H.W) (n := 36) (Nat.le_refl _) (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [eS]
    rintro r (rfl | rfl)
    · exact st_sub hp
    · exact cal_sub hH hp

theorem finArgs_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = uO H ∨ o = tmpO H) :
    WP isa (.block (atSt H ++ count2 H ++ scrAt .r1 o ++ [.mov .r12 (.reg .r11)])) s fun t =>
        KR (H := H) sc s₀ m t ∧ FinArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) ∧
        count t = BitVec.ofNat 64 (H.B + H.D) ∧ t.mem = s.mem := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by rcases ho with rfl | rfl <;> omega
  have sR : scR sc s₀ ∈ s₀.wr := (mem_wr hp).1
  have osub : Region.Sub ⟨SA s₀ o, H.F⟩ (scR sc s₀) := off_sub hp (by omega)
  have eS := addr_sO hp (o := stO H) (by omega)
  have eO := addr_sO hp (o := o) (by omega)
  simp only [atSt, count2, scrAt, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => wp_movw fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_movw fun s₅ u₅ => wp_add (op2_reg _ _) fun s₆ u₆ =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have k₇ : KR (H := H) sc s₀ m s₇ :=
    ((((((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  refine ⟨k₇, ?_, count_movw (by omega) ?_ ?_, by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · exact
      { r0 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
            u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hk.r11,
            movw_ofNat (by omega)]
        r1 := by rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
            u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.r11, movw_ofNat (by omega)]
        r12 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
            u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.r11]
        sp16 := by rw [k₇.sp]; exact hp.sp16
        cw := by
          rw [k₇.wr, eS, eO]
          exact Covers.of_sub fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact sub_of_off sR (by omega)
            · exact sub_of_off sR (by omega)
            · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
        st_o := by rw [eS, eO]; exact part_disj hp (by omega) (by omega) (by omega)
        st_sc := by rw [eS]; exact (cal_disj hH hp (by omega) (by omega)).symm
        o_sc := by rw [eO]; exact (cal_disj hH hp (by omega) (by omega)).symm
        b_st := by rw [below_eq k₇.sp, eS]; exact hp.b_s.sub_right (st_sub hp)
        b_o := by rw [below_eq k₇.sp, eO]; exact hp.b_s.sub_right osub
        b_sc := by rw [below_eq k₇.sp]; exact hp.b_s.sub_right (cal_sub hH hp)
        nst := by rw [toNat_sO hp (by omega)]; omega
        no := by rw [toNat_sO hp (by omega)]; omega
        nsc := by omega }
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]

theorem finCall_ok {m : Nat} {t : State} (hk : KR (H := H) sc s₀ m t) {o : Nat} (ho : o = uO H ∨ o = tmpO H)
    (ha : FinArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀)) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ m s' →
      Frame [⟨ST (H := H) s₀, H.S⟩, ⟨SA s₀ o, H.F⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ msg, hH.SH.Repr t.mem (ST (H := H) s₀) msg → msg.length < 2 ^ 64 →
        count t = BitVec.ofNat 64 msg.length →
        (bytesAt s'.mem (SA s₀ o) H.F).take H.D = hH.SH.H.hash msg) → Q s') :
    WP isa (.frame (.push fin2) (.call H.finN H.finC) (.pop .r1 8)) t Q := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by rcases ho with rfl | rfl <;> omega
  have eS := addr_sO hp (o := stO H) (by omega)
  have eO := addr_sO hp (o := o) (by omega)
  refine fin_frame hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [below_eq hk.sp, eS, eO] at f
  rw [eS, eO] at hpost
  refine hQ s' (hk.call hp ha' ?_ ?_) f hpost
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [eS, eO]
    rintro r (rfl | rfl | rfl)
    · exact save_off hp (by omega) (by omega)
    · exact save_off hp (by omega) (by omega)
    · exact ((cal_disj hH hp (b := 8 * H.W) (n := 36) (Nat.le_refl _) (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [eS, eO]
    rintro r (rfl | rfl | rfl)
    · exact st_sub hp
    · exact off_sub hp (by omega)
    · exact cal_sub hH hp

/-! ## `T ← T ⊕ U` and the count -/

theorem xor'_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) :
    WP isa (xorLoop H) s fun t => KR (H := H) sc s₀ m t ∧
      t.mem = writeBytes s.mem (State.addr (tp s₀)) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (State.addr (tp s₀)) H.D)
        (bytesAt s.mem (UA (H := H) s₀) H.D)) := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = H.buf + H.S + H.F := rfl
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have nt := hp.nt
  have usub : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega)
  refine WP.mono (xor_ok (uo := uO H) (n := H.D) (off_lt hp (Nat.le_refl _)) hD0 (by omega)
    (by rw [hk.r11]; omega) (by rw [hk.r5]; omega)
    (fun k hk' => by
      rw [hk.r11, hk.rd, hk.wr]; exact inRegions_of_sub (List.mem_append_right _ sR) usub (by omega) hk')
    (fun k hk' => by rw [hk.r5, hk.wr]; exact inRegions_of_sub tR' (fun _ h => h) (by omega) hk')
    (by rw [hk.r11, hk.r5]; exact hp.t_s.symm.sub_left usub)) fun t x => ?_
  rw [hk.r11, hk.r5] at x
  refine ⟨hk.keep x.rd x.wr x.sp (fun r hr => x.other r (kregs_clob r hr))
    (x.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := tR (H := H) s₀) (by
      rw [xorBytes_length' _ _ (by simp [bytesAt_length]), bytesAt_length]; exact Region.contains_self _ _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.symm.sub_left (save_sub hp))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩), x.mem⟩

omit hp in
theorem dec_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (hk : KR (H := H) sc s₀ m s) :
    WP isa (.block [.subs .r6 .r6 (.imm 1)]) s fun t => KR (H := H) sc s₀ (m - 1) t ∧ t.mem = s.mem ∧
      t.z = decide (m - 1 = 0) :=
  wp_subs (op2_imm (by decide)) fun t u z => WP.block_nil ⟨⟨by rw [u.rd, hk.rd], by rw [u.wr, hk.wr],
    by rw [u.sp, hk.sp], by rw [u.other _ (by decide), hk.r4], by rw [u.other _ (by decide), hk.r5],
    by rw [u.gpr, hk.r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hm],
    by rw [u.other _ (by decide), hk.r11], u.mem ▸ hk.saved, u.mem ▸ hk.frame⟩,
    u.mem, by rw [z, hk.r6, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hm,
      ofNat_beq_zero (by omega)]⟩

end

/-! ## One step -/

/-- The key's states represent `K₀ ⊕ ipad` and `K₀ ⊕ opad`. -/
def KeyOK (s₀ : State) (k0 : List Byte) : Prop :=
  k0.length = H.B ∧ hH.SH.Repr s₀.mem (State.addr (key s₀)) (xorPad k0 ipad) ∧
    hH.SH.Repr s₀.mem (State.addr (key s₀) + BitVec.ofNat 64 H.S) (xorPad k0 opad)

/-- With `m` steps left, what is left to compute is the rest of the whole. -/
structure Inv (s₀ : State) (m : Nat) (s : State) : Prop where
  kr : KR (H := H) sc s₀ m s
  it : ∀ k0, KeyOK hH s₀ k0 →
    Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (nn s₀) (bytesAt s₀.mem (State.addr (up s₀)) H.D)
        (bytesAt s₀.mem (State.addr (tp s₀)) H.D) =
      Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) m (bytesAt s.mem (UA (H := H) s₀) H.D)
        (bytesAt s.mem (State.addr (tp s₀)) H.D)

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem body_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (h : Inv hH sc s₀ m s) :
    WP isa (body H) s fun t => Inv hH sc s₀ (m - 1) t ∧ t.z = decide (m - 1 = 0) := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = H.buf + H.S + H.F := rfl
  have et : tmpO H = H.buf + H.S := rfl
  have es : stO H = H.buf := rfl
  have hwb := hH.hWb
  -- Where things are.
  have ua : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega)
  have dM₁ : Region.Disjoint ⟨TM (H := H) s₀, H.D⟩ ⟨ST (H := H) s₀, H.S⟩ :=
    part_disj hp (by omega) (by omega) (by omega)
  have dU₁ : Region.Disjoint ⟨UA (H := H) s₀, H.D⟩ ⟨ST (H := H) s₀, H.S⟩ :=
    part_disj hp (by omega) (by omega) (by omega)
  have dT : ∀ r : Region, Region.Sub r (scR sc s₀) → Region.Disjoint (tR (H := H) s₀) r :=
    fun r hr => hp.t_s.sub_right hr
  have dT₄ : Region.Disjoint (tR (H := H) s₀) (stkR s₀) := hp.b_t.symm
  have hDn : H.D ≤ 2 ^ 64 := by omega
  -- The pieces.
  refine WP.seq (WP.mono (copyKey_ok hH hp h.kr (.inl rfl)) fun c₁ ⟨kc₁, fc₁, rc₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp kc₁ (.inl rfl)) fun a₁ ⟨ka₁, aa₁, sa₁, ma₁⟩ =>
    updCall_ok hH hp ka₁ (.inl rfl) aa₁ fun u₁ ku₁ fu₁ ru₁ => ?_))
  refine WP.seq (WP.seq (WP.mono (finArgs_ok hH hp ku₁ (.inr rfl)) fun b₁ ⟨kb₁, ab₁, sb₁, mb₁⟩ =>
    finCall_ok hH hp kb₁ (.inr rfl) ab₁ fun f₁ kf₁ ff₁ rf₁ => ?_))
  refine WP.seq (WP.mono (copyKey_ok hH hp kf₁ (.inr rfl)) fun c₂ ⟨kc₂, fc₂, rc₂⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp kc₂ (.inr rfl)) fun a₂ ⟨ka₂, aa₂, sa₂, ma₂⟩ =>
    updCall_ok hH hp ka₂ (.inr rfl) aa₂ fun u₂ ku₂ fu₂ ru₂ => ?_))
  refine WP.seq (WP.seq (WP.mono (finArgs_ok hH hp ku₂ (.inl rfl)) fun b₂ ⟨kb₂, ab₂, sb₂, mb₂⟩ =>
    finCall_ok hH hp kb₂ (.inl rfl) ab₂ fun f₂ kf₂ ff₂ rf₂ => ?_))
  refine WP.seq (WP.mono (xor'_ok hp kf₂) fun x ⟨kx, mx⟩ => ?_)
  refine WP.mono (dec_ok hm hn kx) fun t ⟨kt, mt, zt⟩ => ⟨⟨kt, fun k0 hk => ?_⟩, zt⟩
  -- The bytes of `U` and `T` at each point.
  obtain ⟨hl0, hrI, hrO⟩ := hk
  have U₁ : bytesAt c₁.mem (UA (H := H) s₀) H.D = bytesAt s.mem (UA (H := H) s₀) H.D :=
    bytes_keep fc₁ (by simp only [List.mem_singleton]; rintro r rfl; exact dU₁) hDn
  have T₁ : bytesAt c₁.mem (State.addr (tp s₀)) H.D = bytesAt s.mem (State.addr (tp s₀)) H.D :=
    bytes_keep fc₁ (by simp only [List.mem_singleton]; rintro r rfl; exact dT _ (st_sub hp)) hDn
  have T₂ : bytesAt u₁.mem (State.addr (tp s₀)) H.D = bytesAt c₁.mem (State.addr (tp s₀)) H.D := by
    rw [← ma₁]; exact bytes_keep fu₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₃ : bytesAt f₁.mem (State.addr (tp s₀)) H.D = bytesAt u₁.mem (State.addr (tp s₀)) H.D := by
    rw [← mb₁]; exact bytes_keep ff₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (tm_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₄ : bytesAt c₂.mem (State.addr (tp s₀)) H.D = bytesAt f₁.mem (State.addr (tp s₀)) H.D :=
    bytes_keep fc₂ (by simp only [List.mem_singleton]; rintro r rfl; exact dT _ (st_sub hp)) hDn
  have T₅ : bytesAt u₂.mem (State.addr (tp s₀)) H.D = bytesAt c₂.mem (State.addr (tp s₀)) H.D := by
    rw [← ma₂]; exact bytes_keep fu₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₆ : bytesAt f₂.mem (State.addr (tp s₀)) H.D = bytesAt u₂.mem (State.addr (tp s₀)) H.D := by
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
  have hx : (Spec.Pbkdf2.xorBytes (bytesAt f₂.mem (State.addr (tp s₀)) H.D)
      (bytesAt f₂.mem (UA (H := H) s₀) H.D)).length = H.D := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), bytesAt_length]
  have Ux : bytesAt t.mem (UA (H := H) s₀) H.D = bytesAt f₂.mem (UA (H := H) s₀) H.D := by
    rw [mt, mx]
    exact bytes_keep (Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := tR (H := H) s₀) (by
      rw [hx]; exact Region.contains_self _ _)) (by
        simp only [List.mem_singleton]; rintro r rfl; exact (dT _ ua).symm) hDn
  have Tx : bytesAt t.mem (State.addr (tp s₀)) H.D = Spec.Pbkdf2.xorBytes
      (bytesAt f₂.mem (State.addr (tp s₀)) H.D) (bytesAt f₂.mem (UA (H := H) s₀) H.D) := by
    rw [mt, mx]; exact bytesAt_writeBytes_self' hx (by omega)
  rw [h.it k0 ⟨hl0, hrI, hrO⟩, show m = (m - 1) + 1 by omega, Ux, Tx, dig₂, T₆, T₅, T₄, T₃, T₂, T₁,
    Nat.add_sub_cancel]
  rfl

/-! ## The prologue and the loop -/

omit hp in
theorem nn_lt : nn s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt

theorem pro_ok : WP isa (.block (prologue H)) s₀ fun t => KR (H := H) sc s₀ (nn s₀) t ∧ t.gpr .r1 = up s₀ ∧
      Frame [saveR H (scr s₀)] s₀.mem t.mem := by
  have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf
  obtain ⟨sR, _⟩ := mem_wr hp
  simp only [prologue, List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    (by rw [hp.rd]; exact ⟨argR s₀, by simp, Region.contains_self _ _⟩) fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega) (by omega)
    fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have hm : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have fs : Frame [saveR H (scr s₀)] s₀.mem s₆.mem := by rw [hm, ← u₁.mem]; exact f₂
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e₂ _ (by decide)],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide),
      BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]; rfl,
    hm ▸ sv₂.of_eq H fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    fs.sub (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨scR sc s₀, by simp, save_sub hp⟩)⟩,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)], fs⟩

/-- `U` into `scratch`. -/
theorem copyU_ok {s : State} (hk : KR (H := H) sc s₀ (nn s₀) s) (hr1 : s.gpr .r1 = up s₀)
    (hf : Frame [saveR H (scr s₀)] s₀.mem s.mem) :
    WP isa (copy .r1 0 .r11 (uO H) H.D) s (Inv hH sc s₀ (nn s₀)) := by
  obtain ⟨hb, hf', hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = H.buf + H.S + H.F := rfl
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have nu := hp.nu
  have uR' : uR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have usub : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega)
  refine WP.mono (copy_ok (so := 0) (d := uO H) (n := H.D) (by decide) (by decide) (by decide)
    (off_lt hp (Nat.le_refl _)) hD0 (by omega) (by rw [hr1]; omega) (by rw [hk.r11]; omega)
    (fun k hk' => by rw [hr1, add_zero']; exact inRegions_of_sub uR' (fun _ h => h) (by omega) hk')
    (fun k hk' => by rw [hk.r11, hk.wr]; exact inRegions_of_sub sR usub (by omega) hk')
    (by rw [hr1, hk.r11, add_zero']; exact hp.u_s.sub_right usub)) fun t c => ?_
  rw [hr1, hk.r11, add_zero'] at c
  have fc : Frame [⟨UA (H := H) s₀, H.D⟩] s.mem t.mem :=
    c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨hk.keep c.rd c.wr c.sp (fun r hr => c.other r (not_cclob (kregs_clob r hr)))
    fc (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact save_off hp (by omega) (by omega))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, usub⟩), fun k0 _ => ?_⟩
  congr 1
  · rw [c.mem, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    exact (bytes_keep hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.u_s.sub_right (save_sub hp)) (by omega)).symm
  · exact ((bytes_keep fc (by simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right usub)
      (by omega)).trans (bytes_keep hf (by
        simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right (save_sub hp)) (by omega))).symm

omit hp in
/-- `cmp r6, #0`: the flags of whether there are steps. -/
theorem cmp_ok {s : State} (h : Inv hH sc s₀ (nn s₀) s) :
    WP isa (.block [.cmp .r6 (.imm 0)]) s fun t => Inv hH sc s₀ (nn s₀) t ∧ t.z = decide (nn s₀ = 0) := by
  refine wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ⟨⟨h.kr.keep f₁.rd f₁.wr f₁.sp
    (fun r _ => by rw [f₁.gpr]) (rs := []) (by rw [f₁.mem]; exact Frame.refl _ _) (by simp) (by simp),
    fun k0 hk => by rw [h.it k0 hk, f₁.mem]⟩, ?_⟩
  rw [z₁, h.kr.r6, show ∀ x : BitVec 32, x - 0 = x from fun x => BitVec.sub_zero x, ofNat_beq_zero nn_lt]

theorem loop_ok {s : State} (h : Inv hH sc s₀ (nn s₀) s) (hz : s.z = decide (nn s₀ = 0)) :
    WP isa (.ite .eq (.block []) (.loop (body H) .ne)) s (Inv hH sc s₀ 0) := by
  have hlt := nn_lt (s₀ := s₀)
  refine WP.ite (decide (nn s₀ = 0)) (by show eval .eq s = _; rw [eval_eq, hz]) (fun h0 => WP.block_nil ?_)
    fun h0 => ?_
  · have e : nn s₀ = 0 := by simpa using h0
    exact e ▸ h
  · have hpos : 1 ≤ nn s₀ := by have := of_decide_eq_false h0; omega
    refine WP.loop (M := isa) (fun k t => ∃ m, k = m ∧ 1 ≤ m ∧ m ≤ nn s₀ ∧ Inv hH sc s₀ m t) ?_ (nn s₀) s
      ⟨nn s₀, rfl, hpos, (Nat.le_refl _), h⟩
    rintro k t ⟨m, hkm, h1, h2, ht⟩
    refine WP.mono (body_ok hH hp h1 (by omega) ht) fun t' ⟨ht', hz'⟩ => ?_
    have he : isa.eval .ne t' = some (!decide (m - 1 = 0)) := by
      show eval .ne t' = _; rw [eval_ne, hz']
    by_cases hl : m - 1 = 0
    · exact .inl ⟨by rw [he]; simp [hl], hl ▸ ht'⟩
    · exact .inr ⟨by rw [he]; simp [hl], m - 1, by omega, m - 1, rfl, by omega, by omega, ht'⟩

theorem correct : WP isa (iterate H) s₀ fun s' => abiPreserved s₀ s' ∧ (iterG hH.SH sc).post s₀ s' := by
  obtain ⟨hb, hf', hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  refine WP.seq (WP.mono (pro_ok hp) fun s₂ ⟨k₂, x₂, f₂⟩ => ?_)
  refine WP.seq (WP.mono (copyU_ok hH hp k₂ x₂ f₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (cmp_ok hH h₃) fun s₄ ⟨h₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hH hp h₄ z₄) fun s₅ h₅ => ?_)
  have k₅ := h₅.kr
  have hL : 8 * H.W + 36 ≤ 8 * sc := by omega
  refine WP.mono (restore_ok H k₅.r11 hW k₅.saved (by rw [k₅.wr]; exact (mem_wr hp).1) hL hnw)
    fun s' ⟨hm, _, _, hsp, hg, _⟩ => ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, k₅.sp]⟩, ?_⟩
  intro k0 hl hrI hrO
  have hS' := hH.hS; have hD' := hH.hD; have hB' := hH.hB
  rw [hB'] at hl
  rw [hS'] at hrO
  show bytesAt s'.mem (State.addr (tp s₀)) hH.SH.digestBytes = _
  rw [hD', hm, h₅.it k0 ⟨hl, hrI, hrO⟩]
  rfl

end

end VG.Proof.Pbkdf2.Generic.Arm

/-!
# PBKDF2-HMAC over any streaming hash function on 32-bit ARM: `iterate`, constant time

As on x86 (`Proof/Pbkdf2/Generic/X86/IterateCT.lean`); the prologue loads
`scratch` from the stack, so its taint check starts with the stack argument
public (`argTaint`).
-/

namespace VG.Proof.Pbkdf2.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy scrAt)
open VG.Impl.Pbkdf2.Generic.Arm (stO tmpO uO xorLoop count2 atSt body prologue iterate)
open VG.Proof.MdStream.Arm (eval_eq eval_ne)
open VG.Proof.Hmac.Generic.Arm

/-- The argument registers. -/
abbrev args : List Reg := [.r0, .r1, .r2, .r3]

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.r4, .r5, .r6, .r11]

/-- The block that sets up a call of `update` on the state, with `D` bytes at `scratch + o`. -/
abbrev updBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ scrAt .r1 o ++ [.movw .r7 (BitVec.ofNat 16 H.D), .mov .r10 (.reg .r11),
    .movw .r2 (BitVec.ofNat 16 H.B), .mov .r3 (.imm 0)]

/-- The block that sets up a call of `finalize` on the state, into `scratch + o`. -/
abbrev finBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ count2 H ++ scrAt .r1 o ++ [.mov .r12 (.reg .r11)]

theorem skip_check : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) (.block []) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block [.cmp .r6 (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem dec_check :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block [.subs .r6 .r6 (.imm 1)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The taint checks of the pieces of `iterate` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (VG.Taint.check taint (argTaint args 4) (.block (prologue H)) hc).isSome = true
  copyU : ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs (.r1 :: pubRegs)) (copy .r1 0 .r11 (uO H) H.D) hc).isSome = true
  copyK : ∀ o ∈ [0, H.S], ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs pubRegs) (copy .r4 o .r11 (stO H) H.S) hc).isSome = true
  upd : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (updBlock H o)) hc).isSome = true
  fin : ∀ o ∈ [uO H, tmpO H], ∃ hc,
    (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block (finBlock H o)) hc).isSome = true
  xor : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (xorLoop H) hc).isSome = true
  restore : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) (.block H.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

variable {H : Hash} (hH : HashOK H) {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem PubEq.nn (hq : PubEq s₀ s₀') : Generic.Arm.nn s₀ = Generic.Arm.nn s₀' := by
  show (s₀.gpr .r2).toNat = (s₀'.gpr .r2).toNat; rw [hq.r2]

theorem kr_agree (hq : PubEq s₀ s₀') {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s)
    (h' : KR (H := H) sc s₀' m s') : ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, key, key, hq.r0]
  · rw [h.r5, h'.r5, tp, tp, hq.r3]
  · rw [h.r6, h'.r6]
  · rw [h.r11, h'.r11, scr, scr, hq.a0]

theorem eqs (hq : PubEq s₀ s₀') : scr s₀' = scr s₀ ∧ ∀ o : Nat, sO s₀' o = sO s₀ o :=
  ⟨hq.a0.symm, fun o => by rw [sO, sO, scr, scr, hq.a0]⟩

/-- The stack argument lies outside the writable regions. -/
theorem args_wf {t : State} (h : Pre (H := H) sc t) :
    t.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4⟩ r := by
  have e : (⟨State.addr t.sp, 4⟩ : Region) = argR t := by simp [stackArgAddr]
  refine ⟨h.spf, ?_⟩
  simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact h.a_t
  · exact h.a_s

omit hp hp' hq in
theorem UpdArgs.congr {t : State} {st st' d d' c c' : BitVec 32} {len : Nat} (h₁ : st = st') (h₂ : d = d')
    (h₃ : c = c') (a : UpdArgs hH t st d c len) : UpdArgs hH t st' d' c' len := by
  subst h₁ h₂ h₃; exact a

omit hp hp' hq in
theorem FinArgs.congr {t : State} {st st' d d' c c' : BitVec 32} (h₁ : st = st') (h₂ : d = d')
    (h₃ : c = c') (a : FinArgs hH t st d c) : FinArgs hH t st' d' c' := by
  subst h₁ h₂ h₃; exact a

include hH hp hp' hq

omit hH in
/-- A piece of code between calls that keeps `KR`. -/
theorem kr_rel {m : Nat} {c : Prog isa}
    (hck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs pubRegs) c hc).isSome = true)
    (hw : ∀ {t₀ : State}, Pre (H := H) sc t₀ → ∀ s, KR (H := H) sc t₀ m s → WP isa c s (KR (H := H) sc t₀ m)) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') c
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
  rel_taint pubRegs (fun _ _ h h' => kr_agree hq h h') hck (hw hp) (hw hp')

theorem upd_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callUpd (atSt H) H.B o H.D)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      UpdArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) H.D ∧ count t = BitVec.ofNat 64 H.B)
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      UpdArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) H.D ∧ count t = BitVec.ofNat 64 H.B)
    pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.upd o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (updArgs_ok hH hp h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (updArgs_ok hH hp' h ho) fun _ ⟨k, a, x1, _⟩ =>
      ⟨k, UpdArgs.congr hH (e3 _) (e3 o) e2 a, x1⟩)
  exact ha.seq (rel_wp (upd_rel hH (sp := s₀.sp) (st := sO s₀ (stO H)) (d := sO s₀ o) (sc := scr s₀)
    (len := H.D) fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], k.sp, by rw [k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => updCall_ok hH hp' k ho (UpdArgs.congr hH (e3 _).symm (e3 o).symm e2.symm a)
      fun _ k' _ _ => k'))

theorem fin_rel' {m : Nat} {o : Nat} (ho : o = uO H ∨ o = tmpO H) (hc : Checks H) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (H.callFin (atSt H) (count2 H) o)
      fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' := by
  obtain ⟨e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) sc s₀ m t ∧
      FinArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) ∧ count t = BitVec.ofNat 64 (H.B + H.D))
    (G' := fun t => KR (H := H) sc s₀' m t ∧
      FinArgs hH t (sO s₀ (stO H)) (sO s₀ o) (scr s₀) ∧ count t = BitVec.ofNat 64 (H.B + H.D))
    pubRegs (fun _ _ h h' => kr_agree hq h h') (hc.fin o (by rcases ho with rfl | rfl <;> simp))
    (fun s h => WP.mono (finArgs_ok hH hp h ho) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (finArgs_ok hH hp' h ho) fun _ ⟨k, a, x1, _⟩ =>
      ⟨k, FinArgs.congr hH (e3 _) (e3 o) e2 a, x1⟩)
  exact ha.seq (rel_wp (fin_rel hH (sp := s₀.sp) (st := sO s₀ (stO H)) (o := sO s₀ o) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], k.sp, by rw [k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k ho a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k ho (FinArgs.congr hH (e3 _).symm (e3 o).symm e2.symm a)
      fun _ k' _ _ => k'))

theorem body_rel (hc : Checks H) {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) :
    RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s') (body H)
      fun s s' => KR (H := H) sc s₀ (m - 1) s ∧ KR (H := H) sc s₀' (m - 1) s' := by
  have ck : ∀ {o : Nat}, (o = 0 ∨ o = H.S) → RelCT isa (fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s')
      (copy .r4 o .r11 (stO H) H.S) fun s s' => KR (H := H) sc s₀ m s ∧ KR (H := H) sc s₀' m s' :=
    fun ho => kr_rel hp hp' hq (m := m) (hc.copyK _ (by rcases ho with rfl | rfl <;> simp))
      fun hp s k => WP.mono (copyKey_ok hH hp k ho) fun _ h => h.1
  have x := kr_rel hp hp' hq (m := m) hc.xor fun hp s k => WP.mono (xor'_ok hp k) fun _ h => h.1
  have d := rel_taint (G := KR (H := H) sc s₀ (m - 1)) (G' := KR (H := H) sc s₀' (m - 1)) pubRegs
    (fun _ _ h h' => kr_agree hq h h') dec_check
    (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1) (fun s k => WP.mono (dec_ok hm hn k) fun _ h => h.1)
  exact (ck (.inl rfl)).seq ((upd_rel' hH hp hp' hq (.inl rfl) hc).seq ((fin_rel' hH hp hp' hq (.inr rfl) hc).seq
    ((ck (.inr rfl)).seq ((upd_rel' hH hp hp' hq (.inr rfl) hc).seq ((fin_rel' hH hp hp' hq (.inl rfl) hc).seq
    (x.seq d))))))

/-- The loop's invariant in two runs, with `n` steps left. -/
abbrev LoopInv (n : Nat) (s s' : State) : Prop :=
  1 ≤ n ∧ n ≤ nn s₀ ∧ Inv hH sc s₀ n s ∧ Inv hH sc s₀' n s'

theorem step_rel (hc : Checks H) (n : Nat) :
    RelCT isa (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n) (body H) fun s s' =>
      isa.eval .ne s = isa.eval .ne s' ∧
      (isa.eval .ne s = some false → Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') ∧
      (isa.eval .ne s = some true → ∃ m < n, LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') m s s') := by
  have hlt := nn_lt (s₀ := s₀)
  by_cases hn : 1 ≤ n ∧ n ≤ nn s₀
  · have b := (body_rel hH hp hp' hq hc hn.1 (by omega)).mono (P' := LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n)
      (fun _ _ (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) => ⟨h.2.2.1.kr, h.2.2.2.kr⟩)
      fun _ _ h => h
    refine (b.wp (F₁ := fun (t : State) => Inv hH sc s₀ (n - 1) t ∧ t.z = decide (n - 1 = 0))
      (F₂ := fun (t : State) => Inv hH sc s₀' (n - 1) t ∧ t.z = decide (n - 1 = 0))
      fun s s' (h : LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀') n _ _) =>
        ⟨body_ok hH hp hn.1 (by omega) h.2.2.1, body_ok hH hp' hn.1 (by omega) h.2.2.2⟩).mono
      (fun _ _ h => h) fun t t' h => ?_
    obtain ⟨_, ⟨i, z⟩, ⟨i', z'⟩⟩ := h
    have e : isa.eval .ne t = some (!decide (n - 1 = 0)) := by show eval .ne t = _; rw [eval_ne, z]
    have e' : isa.eval .ne t' = some (!decide (n - 1 = 0)) := by show eval .ne t' = _; rw [eval_ne, z']
    rw [e, e']
    refine ⟨rfl, fun hf => ?_, fun ht => ?_⟩
    · have hl : n - 1 = 0 := by simpa using hf
      exact ⟨hl ▸ i, hl ▸ i'⟩
    · have hl : n - 1 ≠ 0 := by simpa using ht
      exact ⟨n - 1, by omega, by omega, by omega, i, i'⟩
  · intro _ _ _ _ _ _ h
    exact absurd ⟨h.1, h.2.1⟩ hn

theorem loop_rel (hc : Checks H) :
    RelCT isa (fun s s' => (Inv hH sc s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0)) ∧
        (Inv hH sc s₀' (nn s₀') s' ∧ s'.z = decide (nn s₀' = 0)))
      (.ite .eq (.block []) (.loop (body H) .ne))
      fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s' := by
  have hN := hq.nn
  have ev : ∀ {t : State} {k : Nat}, t.z = decide (k = 0) → isa.eval .eq t = some (decide (k = 0)) :=
    fun h => by show eval .eq _ = _; rw [eval_eq, h]
  refine RelCT.ite (fun s s' h => by rw [ev h.1.2, ev h.2.2, hN]) ?_ ?_
  · by_cases e : nn s₀ = 0
    · have e' : nn s₀' = 0 := hN ▸ e
      exact (rel_taint (c := .block []) (F := fun s => Inv hH sc s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0))
        (F' := fun s => Inv hH sc s₀' (nn s₀') s ∧ s.z = decide (nn s₀' = 0))
        (G := Inv hH sc s₀ 0) (G' := Inv hH sc s₀' 0) []
        (fun s s' h h' => by simp) skip_check
        (fun s h => WP.block_nil (e ▸ h.1)) (fun s h => WP.block_nil (e' ▸ h.1))).mono (fun _ _ h => h.1)
        fun _ _ h => h
    · intro _ _ _ _ _ _ h
      have z := h.2
      rw [ev h.1.1.2] at z
      exact absurd (by simpa using z) e
  · refine (RelCT.loop (M := isa) (LoopInv hH (sc := sc) (s₀ := s₀) (s₀' := s₀')) (step_rel hH hp hp' hq hc)
      (nn s₀)).mono (fun s s' h => ?_) fun _ _ h => h
    have z := h.2
    rw [ev h.1.1.2] at z
    have e : nn s₀ ≠ 0 := by simpa using z
    exact ⟨by omega, (Nat.le_refl _), h.1.1.1, hN ▸ h.1.2.1⟩

theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (iterate H) fun _ _ => True := by
  have hN := hq.nn
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .r1 = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (G' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .r1 = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (argTaint args 4) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (args_wf hp) (args_wf hp')
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega]; exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
    (fun _ e => by rw [e]; exact pro_ok hp) (fun _ e => by rw [e]; exact pro_ok hp')
  have cu := rel_taint
    (F := fun s => KR (H := H) sc s₀ (nn s₀) s ∧ s.gpr .r1 = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem)
    (F' := fun s => KR (H := H) sc s₀' (nn s₀') s ∧ s.gpr .r1 = up s₀' ∧ Frame [saveR H (scr s₀')] s₀'.mem s.mem)
    (G := Inv hH sc s₀ (nn s₀)) (G' := Inv hH sc s₀' (nn s₀')) (.r1 :: pubRegs)
    (fun s s' h h' r hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [h.2.1, h'.2.1, up, up, hq.r1]
      · exact kr_agree hq h.1 (hN ▸ h'.1) r hm) hc.copyU
    (fun s h => copyU_ok hH hp h.1 h.2.1 h.2.2) (fun s h => copyU_ok hH hp' h.1 h.2.1 h.2.2)
  have cm := rel_taint (F := Inv hH sc s₀ (nn s₀)) (F' := Inv hH sc s₀' (nn s₀'))
    (G := fun s => Inv hH sc s₀ (nn s₀) s ∧ s.z = decide (nn s₀ = 0))
    (G' := fun s => Inv hH sc s₀' (nn s₀') s ∧ s.z = decide (nn s₀' = 0)) pubRegs
    (fun s s' h h' => kr_agree hq h.kr (hN ▸ h'.kr)) cmp_check
    (fun s h => cmp_ok hH h) (fun s h => cmp_ok hH h)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Inv hH sc s₀ 0 s ∧ Inv hH sc s₀' 0 s') (.block H.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs pubRegs) (fun _ _ h =>
      Taint.agree_ofRegs (kr_agree hq h.1.kr h.2.kr)) hr
  exact pro.seq (cu.seq (cm.seq ((loop_rel hH hp hp' hq hc).seq restore)))

end VG.Proof.Pbkdf2.Generic.Arm

namespace VG.Proof.Pbkdf2.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)
open VG.Proof.Hmac.Generic.Arm

/-- `iterate` is verified against `iterG`, given the taint checks, which the
kernel evaluates for each hash function. -/
theorem verified {H : Hash} (hH : HashOK H) {sc : Nat} (hc : Checks H)
    (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) (hsat : ∃ s, (iterG hH.SH sc).pre s) :
    Verified Arm.target (VG.Impl.Pbkdf2.Generic.Arm.iterate H) (iterG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH sc hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
  exact (ct hH (pre_of hH sc h₁ hfit) (pre_of hH sc h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hc
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Generic.Arm

/-!
# PBKDF2-HMAC over the streaming hash functions on 32-bit ARM: the instances

As on x86 (`Proof/Pbkdf2/Generic/X86/Instances.lean`): the generic proof (above)
at each hash function of `Proof/Hmac/Generic/Arm/Hashes.lean`, moved to the
shared contract of `Spec/Pbkdf2/Generic.lean` (`sig_implies`), which the
artifacts are emitted with.
-/

namespace VG.Proof.Pbkdf2.Generic.Arm.Instances

open VG.Arm
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Pbkdf2.Generic.Arm

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 sc` bytes of scratch space; `scratch`, at
`0x4000`, is the stack argument. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x1000, 2 * S⟩, ⟨0x2000, D⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x3000, D⟩, ⟨0x4000, 8 * sc⟩]

/-- `iterG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem iterImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Pbkdf2.iterateContract S W Arm.abi 16).pre s) :
    (iterG S W).Implies (Spec.Pbkdf2.iterateContract S W Arm.abi 16) := by
  generic_implies [
    Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, iterG, below, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using h

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
  restore := ⟨_, by taint_decide⟩

theorem sha1_imp : (iterG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha1S 56 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 84 20 56)

theorem sha1 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha1H)
    (Spec.Hmac.sha1I.iterateContract Arm.abi 16) :=
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
  restore := ⟨_, by taint_decide⟩

theorem md5_imp : (iterG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.md5S 48 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 80 16 48)

theorem md5 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate md5H)
    (Spec.Hmac.md5I.iterateContract Arm.abi 16) :=
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
  restore := ⟨_, by taint_decide⟩

theorem sha384_imp : (iterG Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha384S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 192 48 234)

theorem sha384 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha384H)
    (Spec.Hmac.sha384I.iterateContract Arm.abi 16) :=
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
  restore := ⟨_, by taint_decide⟩

theorem sha512_imp : (iterG Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha512S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 192 64 234)

theorem sha512 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha512H')
    (Spec.Hmac.sha512I.iterateContract Arm.abi 16) :=
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
  restore := ⟨_, by taint_decide⟩

theorem sha512_224_imp : (iterG Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha512_224S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 192 28 234)

theorem sha512_224 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha512_224H)
    (Spec.Hmac.sha512_224I.iterateContract Arm.abi 16) :=
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
  restore := ⟨_, by taint_decide⟩

theorem sha512_256_imp : (iterG Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha512_256S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterG, below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 192 32 234)

theorem sha512_256 : Verified Arm.target (Impl.Pbkdf2.Generic.Arm.iterate sha512_256H)
    (Spec.Hmac.sha512_256I.iterateContract Arm.abi 16) :=
  (verified sha512_256OK sha512_256_checks (by decide) sha512_256_imp.sat_left).of_implies sha512_256_imp

end VG.Proof.Pbkdf2.Generic.Arm.Instances
