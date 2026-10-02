import VerifiedGarbage.Impl.Pbkdf2.Generic.X86
import VerifiedGarbage.Proof.Hmac.Generic.X86.Finalize

/-!
# PBKDF2-HMAC over any streaming hash function on x86 (32-bit): `iterate`, correct

As on 32-bit ARM (`Proof/Pbkdf2/Generic/Arm/Instances.lean`). The arguments
are on the stack: `scratch`, `n` and `u` are loaded first (after our caller's
registers are saved in `scratch`), and `key` and `t` again in each step, when
needed. The loop counts the steps left in `edi` down with `sub`, and branches
on its result.
-/

namespace VG.Proof.Pbkdf2.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash copy at_)
open VG.Impl.Pbkdf2.Generic.X86 (stO tmpO uO xorLoop atSt ldKey ldT body prologue iterate)
open VG.Proof.Hmac.Generic.X86
open VG.Proof.Hmac.Generic.X86.Finalize (add_zero')
open VG.Proof.Hmac.Generic.X86.Init (argW)
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub xorBytes_length' sub_of_off sub_of_self bytes_keep
  bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_mov wp_movi wp_movm wp_add wp_addi wp_subi wp_test sub_offset
  ofNat_beq_zero sub_ofNat eval_e eval_ne)
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev key : BitVec 32 := arg s₀ 0
abbrev up : BitVec 32 := arg s₀ 1
abbrev tp : BitVec 32 := arg s₀ 3
abbrev scr : BitVec 32 := arg s₀ 4
/-- The number of steps. -/
abbrev nn : Nat := (arg s₀ 2).toNat
abbrev keyR : Region := ⟨(key s₀).setWidth 64, 2 * H.S⟩
abbrev uR : Region := ⟨(up s₀).setWidth 64, H.D⟩
abbrev tR : Region := ⟨(tp s₀).setWidth 64, H.D⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (E s₀) 4, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- Byte `o` of `scratch`, and its address as a register holds it. -/
abbrev SA (o : Nat) : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 o
abbrev sO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
/-- The state being hashed, the inner digest and `U`, in `scratch`. -/
abbrev ST : Addr := SA s₀ (stO H)
abbrev TM : Addr := SA s₀ (tmpO H)
abbrev UA : Addr := SA s₀ (uO H)
abbrev calR : Region := ⟨(scr s₀).setWidth 64, hH.Wb⟩

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
  r_t : (retR s₀).Disjoint (tR (H := H) s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_k : (stkR s₀).Disjoint (keyR (H := H) s₀)
  b_u : (stkR s₀).Disjoint (uR (H := H) s₀)
  b_t : (stkR s₀).Disjoint (tR (H := H) s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  nk : (key s₀).toNat + 2 * H.S ≤ 2 ^ 32
  nu : (up s₀).toNat + H.D ≤ 2 ^ 32
  nt : (tp s₀).toNat + H.D ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.buf + H.S + 2 * H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (iterG hH.SH sc).pre s₀) (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h19]; rfl
  simp only [hS, hD, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, hfit,
    ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem bounds : H.buf = 8 * H.W + 16 ∧ H.buf + H.S + 2 * H.F ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.W ≤ 64 ∧ 0 < H.S ∧ H.S ≤ 256 ∧ 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64 ∧ 0 < H.B ∧ H.B ≤ 128 :=
  ⟨rfl, hp.fits, hp.nw, hp.hW, hp.hS.1, hp.hS.2, hp.hD.1, hp.hD.2.1, hp.hD.2.2, hp.hB.1, hp.hB.2⟩

theorem off_sub {o n : Nat} (h : o + n ≤ 8 * sc) :
    Region.Sub ⟨SA s₀ o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega)

theorem addr_sO {o : Nat} (h : o < 8 * sc) : (sO s₀ o).setWidth 64 = SA s₀ o :=
  setWidth_add (by have := hp.nw; omega)

theorem toNat_sO {o : Nat} (h : o < 8 * sc) : (sO s₀ o).toNat = (scr s₀).toNat + o :=
  toNat_add_ofNat (by have := hp.nw; omega)

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

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have := hp.spf; omega)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have := hp.spf; omega)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: `T`, `scratch` and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [tR (H := H) s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on, with `m` steps left. -/
structure KR (s₀ : State) (m : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  edi : s.gpr .edi = BitVec.ofNat 32 m
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame (wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .edi]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide
theorem kregs_clob : ∀ r ∈ kregs, r ∉ clob := by decide

section
variable {sc : Nat}

theorem KR.keep {s₀ : State} {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') :
    KR (H := H) sc s₀ m s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.edi, h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ : State} {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) {d : Reg} (hd : d ∉ kregs)
    {v : BitVec 32} (u : Upd s s' d v) : KR (H := H) sc s₀ m s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := []) (by rw [u.mem]; exact Frame.refl _ _)
    (by simp) (by simp)

theorem stk_eq {s₀ : State} {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) : stk s = stkR s₀ := by
  rw [stk, hk.esp]

end

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem mem_wr : scR sc s₀ ∈ s₀.wr ∧ tR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem argR_in : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, argR_in hp, arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

theorem KR.argEq {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {i : Nat} (hi : i < 5) :
    VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have := hp.spf; omega) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_t
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega)

theorem KR.readArg {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

theorem KR.ret {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.r_t
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

theorem KR.call {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ ws, Region.Sub r (scR sc s₀)) :
    KR (H := H) sc s₀ m s' := by
  have f := ha.frame
  rw [stk_eq h] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.b_s.symm.sub_left (save_sub hp)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨scR sc s₀, by simp, hsub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem save_off {o n : Nat} (ho : 8 * H.W + 16 ≤ o) (h : o + n ≤ 8 * sc) :
    (saveR H (scr s₀)).Disjoint ⟨SA s₀ o, n⟩ :=
  part_disj hp (a := 8 * H.W) (m := 16) (by omega) (by have := hp.fits; simp only [Hash.buf] at this; omega) h

/-! ## The loads of `key` and `t` -/

theorem ld_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {i : Nat} (hi : i = 0 ∨ i = 3) :
    WP isa (.block [.mov .esi (.mem (at_ .esp (4 + 4 * i)))]) s fun t =>
      KR (H := H) sc s₀ m t ∧ t.gpr .esi = arg s₀ i ∧ t.mem = s.mem := by
  have hi' : i < 5 := by omega
  refine wp_movm (a := argAddr s₀ i) (by rw [ea_at, hk.esp]; rfl) (argIn hp hk.rd hk.wr hi') fun t u => ?_
  exact WP.block_nil ⟨hk.upd (by decide) u, by rw [u.gpr, hk.readArg hp hi'], u.mem⟩

/-! ## The copies of the key's states -/

theorem copyKey_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) (hsi : s.gpr .esi = key s₀) {o : Nat}
    (ho : o = 0 ∨ o = H.S) :
    WP isa (copy .esi o .ebp (stO H) H.S) s fun t => KR (H := H) sc s₀ m t ∧
      Frame [⟨ST (H := H) s₀, H.S⟩] s.mem t.mem ∧
      ∀ msg, hH.SH.Repr s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 o) msg →
        hH.SH.Repr t.mem (ST (H := H) s₀) msg := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, -⟩ := bounds hp
  have hkn := hp.nk
  have ksub : Region.Sub ⟨(key s₀).setWidth 64 + BitVec.ofNat 64 o, H.S⟩ (keyR (H := H) s₀) :=
    sub_offset (by rcases ho with rfl | rfl <;> omega) (by rcases ho with rfl | rfl <;> omega)
  have kR : keyR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have sR : scR sc s₀ ∈ s.wr := by rw [hk.wr]; exact (mem_wr hp).1
  have stsub := st_sub hp
  refine WP.mono (copy_ok (so := o) (d := stO H) (n := H.S) (by decide) (by decide) hS0 (by omega)
    (by rw [hsi]; rcases ho with rfl | rfl <;> omega) (by rw [hk.ebp]; simp only [stO]; omega)
    (fun k hk' => by rw [hsi]; exact inRegions_of_sub kR ksub (by omega) hk')
    (fun k hk' => by rw [hk.ebp]; exact inRegions_of_sub sR stsub (by omega) hk')
    (by rw [hsi, hk.ebp]; exact (hp.k_s.sub_left ksub).sub_right stsub)) fun t c => ?_
  rw [hsi, hk.ebp] at c
  have fr : Frame [⟨ST (H := H) s₀, H.S⟩] s.mem t.mem :=
    c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have sd : (saveR H (scr s₀)).Disjoint ⟨ST (H := H) s₀, H.S⟩ :=
    save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega)
  refine ⟨hk.keep c.rd c.wr (fun r hr => c.other r (not_cclob (kregs_clob r hr)))
    fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sd)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, stsub⟩),
    fr, fun msg hr => ?_⟩
  refine hH.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [c.mem, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi]
  -- The key's bytes are those of the initial memory.
  refine hk.frame.bytes (R := ⟨(key s₀).setWidth 64 + BitVec.ofNat 64 o, H.S⟩) ?_ (by show H.S ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.k_t.sub_left ksub
  · exact hp.k_s.sub_left ksub
  · exact hp.b_k.symm.sub_left ksub

/-! ## The calls -/

/-- The block before `update`'s frame, from the state, with `D` bytes at `scratch + o`. -/
abbrev updBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ [.mov .eax (.imm 0), .mov .esi (.imm (BitVec.ofNat 32 H.B)), .mov .ecx (.imm (BitVec.ofNat 32 H.D))] ++
    Impl.Hmac.Generic.X86.scr .edx o

/-- The block before `finalize`'s frame, from the state, into `scratch + o`. -/
abbrev finBlock (H : Hash) (o : Nat) : List Instr :=
  atSt H ++ H.count2 ++ Impl.Hmac.Generic.X86.scr .edx o

theorem updArgs_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = uO H ∨ o = tmpO H) :
    WP isa (.block (updBlock H o)) s fun t =>
        KR (H := H) sc s₀ m t ∧
        UpdArgs hH t .esi .ebx (sO s₀ (stO H)) (sO s₀ o) (scr s₀) (BitVec.ofNat 32 H.B) H.D ∧ t.mem = s.mem := by
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
  simp only [updBlock, atSt, Impl.Hmac.Generic.X86.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_movi fun s₄ u₄ =>
    wp_movi fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => WP.block_nil ?_
  have k₇ : KR (H := H) sc s₀ m s₇ :=
    ((((((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  refine ⟨k₇, ?_, by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { hst := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, hk.ebp]
      hlo := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
      eax := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr]
      ecx := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
      edx := by rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.other _ (by decide), hk.ebp]
      ebp := k₇.ebp
      hr := by decide
      hl := by decide
      hlen := by omega
      sp48 := by rw [k₇.esp]; exact hp.sp48
      cd := by
        rw [k₇.rd, k₇.wr, eO]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (List.mem_append_right _ sR) (by omega)
      cw := by
        rw [k₇.wr, eS]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_off sR (by omega)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_sc := by rw [eS]; exact (cal_disj hH hp (by omega) (by omega)).symm
      d_st := by rw [eO, eS]; exact part_disj hp (by omega) (by omega) (by omega)
      d_sc := by rw [eO]; exact (cal_disj hH hp (by omega) (by omega)).symm
      b_st := by rw [stk_eq k₇, eS]; exact hp.b_s.sub_right (st_sub hp)
      b_d := by rw [stk_eq k₇, eO]; exact hp.b_s.sub_right dsub
      b_sc := by rw [stk_eq k₇]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := by rw [toNat_sO hp (by omega)]; omega
      nd := by rw [toNat_sO hp (by omega)]; omega
      nsc := by omega }

theorem updCall_ok {m : Nat} {t : State} (hk : KR (H := H) sc s₀ m t) {o : Nat} (ho : o = uO H ∨ o = tmpO H)
    (ha : UpdArgs hH t .esi .ebx (sO s₀ (stO H)) (sO s₀ o) (scr s₀) (BitVec.ofNat 32 H.B) H.D) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ m s' → Frame [⟨ST (H := H) s₀, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ msg, hH.SH.Repr t.mem (ST (H := H) s₀) msg → BitVec.ofNat 64 H.B = BitVec.ofNat 64 msg.length →
        hH.SH.Repr s'.mem (ST (H := H) s₀) (msg ++ bytesAt t.mem (SA s₀ o) H.D)) → Q s') :
    WP isa (.frame (.push (upd6 .esi .ebx)) (.call H.updN H.updC) (.pop .eax (upd6 .esi .ebx).length)) t Q := by
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
  rw [stk_eq hk, eS] at f
  rw [eS, eO] at hpost
  refine hQ s' (hk.call hp ha' ?_ ?_) f fun msg hr hc => hpost msg hr (by
    rw [zero_append_ofNat (by omega)]; exact hc)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [eS]
    rintro r (rfl | rfl)
    · exact save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega)
    · exact ((cal_disj hH hp (b := 8 * H.W) (n := 16) (Nat.le_refl _) (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [eS]
    rintro r (rfl | rfl)
    · exact st_sub hp
    · exact cal_sub hH hp

theorem finArgs_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = uO H ∨ o = tmpO H) :
    WP isa (.block (finBlock H o)) s fun t =>
        KR (H := H) sc s₀ m t ∧
        FinArgs hH t .ebx (sO s₀ (stO H)) (sO s₀ o) (scr s₀) (BitVec.ofNat 32 (H.B + H.D)) 0 ∧ t.mem = s.mem := by
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
  simp only [finBlock, atSt, Hash.count2, Impl.Hmac.Generic.X86.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_movi fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => WP.block_nil ?_
  have k₆ : KR (H := H) sc s₀ m s₆ :=
    (((((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅).upd (by decide) u₆
  refine ⟨k₆, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { hst := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.gpr, u₁.gpr, hk.ebp]
      eax := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
      ecx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
      edx := by rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), hk.ebp]
      ebp := k₆.ebp
      hr := by decide
      sp48 := by rw [k₆.esp]; exact hp.sp48
      cw := by
        rw [k₆.wr, eS, eO]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_off sR (by omega)
          · exact sub_of_off sR (by omega)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_o := by rw [eS, eO]; exact part_disj hp (by omega) (by omega) (by omega)
      st_sc := by rw [eS]; exact (cal_disj hH hp (by omega) (by omega)).symm
      o_sc := by rw [eO]; exact (cal_disj hH hp (by omega) (by omega)).symm
      b_st := by rw [stk_eq k₆, eS]; exact hp.b_s.sub_right (st_sub hp)
      b_o := by rw [stk_eq k₆, eO]; exact hp.b_s.sub_right osub
      b_sc := by rw [stk_eq k₆]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := by rw [toNat_sO hp (by omega)]; omega
      no := by rw [toNat_sO hp (by omega)]; omega
      nsc := by omega }

theorem finCall_ok {m : Nat} {t : State} (hk : KR (H := H) sc s₀ m t) {o : Nat} (ho : o = uO H ∨ o = tmpO H)
    (ha : FinArgs hH t .ebx (sO s₀ (stO H)) (sO s₀ o) (scr s₀) (BitVec.ofNat 32 (H.B + H.D)) 0)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ m s' →
      Frame [⟨ST (H := H) s₀, H.S⟩, ⟨SA s₀ o, H.F⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ msg, hH.SH.Repr t.mem (ST (H := H) s₀) msg → msg.length < 2 ^ 64 →
        BitVec.ofNat 64 (H.B + H.D) = BitVec.ofNat 64 msg.length →
        (bytesAt s'.mem (SA s₀ o) H.F).take H.D = hH.SH.H.hash msg) → Q s') :
    WP isa (.frame (.push (fin5 .ebx)) (.call H.finN H.finC) (.pop .eax (fin5 .ebx).length)) t Q := by
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
  rw [stk_eq hk, eS, eO] at f
  rw [eS, eO] at hpost
  refine hQ s' (hk.call hp ha' ?_ ?_) f fun msg hr hl hc => hpost msg hr hl (by
    rw [zero_append_ofNat (by omega)]; exact hc)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [eS, eO]
    rintro r (rfl | rfl | rfl)
    · exact save_off hp (by omega) (by omega)
    · exact save_off hp (by omega) (by omega)
    · exact ((cal_disj hH hp (b := 8 * H.W) (n := 16) (Nat.le_refl _) (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [eS, eO]
    rintro r (rfl | rfl | rfl)
    · exact st_sub hp
    · exact off_sub hp (by omega)
    · exact cal_sub hH hp

/-! ## `T ← T ⊕ U` and the count -/

theorem xor'_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) (hsi : s.gpr .esi = tp s₀) :
    WP isa (xorLoop H) s fun t => KR (H := H) sc s₀ m t ∧
      t.mem = writeBytes s.mem ((tp s₀).setWidth 64) (Spec.Pbkdf2.xorBytes
        (bytesAt s.mem ((tp s₀).setWidth 64) H.D) (bytesAt s.mem (UA (H := H) s₀) H.D)) := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = H.buf + H.S + H.F := rfl
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have nt := hp.nt
  have usub : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega)
  refine WP.mono (xor_ok (uo := uO H) (n := H.D) hD0 (by omega)
    (by rw [hk.ebp]; omega) (by rw [hsi]; omega)
    (fun k hk' => by
      rw [hk.ebp, hk.rd, hk.wr]; exact inRegions_of_sub (List.mem_append_right _ sR) usub (by omega) hk')
    (fun k hk' => by rw [hsi, hk.wr]; exact inRegions_of_sub tR' (fun _ h => h) (by omega) hk')
    (by rw [hk.ebp, hsi]; exact hp.t_s.symm.sub_left usub)) fun t x => ?_
  rw [hk.ebp, hsi] at x
  refine ⟨hk.keep x.rd x.wr (fun r hr => x.other r (kregs_clob r hr))
    (x.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := tR (H := H) s₀) (by
      rw [xorBytes_length' _ _ (by simp [bytesAt_length]), bytesAt_length]; exact Region.contains_self _ _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.symm.sub_left (save_sub hp))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩), x.mem⟩

omit hp in
theorem dec_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (hk : KR (H := H) sc s₀ m s) :
    WP isa (.block [.alu .sub .edi (.imm 1)]) s fun t => KR (H := H) sc s₀ (m - 1) t ∧ t.mem = s.mem ∧
      t.zf = some (decide (m - 1 = 0)) :=
  wp_subi fun t u z => WP.block_nil ⟨⟨by rw [u.rd, hk.rd], by rw [u.wr, hk.wr],
    by rw [u.other _ (by decide), hk.esp], by rw [u.other _ (by decide), hk.ebp],
    by rw [u.gpr, hk.edi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hm],
    u.mem ▸ hk.saved, u.mem ▸ hk.frame⟩,
    u.mem, by rw [z, hk.edi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hm,
      ofNat_beq_zero (by omega)]⟩

end

/-! ## One step -/

/-- The key's states represent `K₀ ⊕ ipad` and `K₀ ⊕ opad`. -/
def KeyOK (s₀ : State) (k0 : List Byte) : Prop :=
  k0.length = H.B ∧ hH.SH.Repr s₀.mem ((key s₀).setWidth 64) (xorPad k0 ipad) ∧
    hH.SH.Repr s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 H.S) (xorPad k0 opad)

/-- With `m` steps left, what is left to compute is the rest of the whole. -/
structure Inv (s₀ : State) (m : Nat) (s : State) : Prop where
  kr : KR (H := H) sc s₀ m s
  it : ∀ k0, KeyOK hH s₀ k0 →
    Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (nn s₀) (bytesAt s₀.mem ((up s₀).setWidth 64) H.D)
        (bytesAt s₀.mem ((tp s₀).setWidth 64) H.D) =
      Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) m (bytesAt s.mem (UA (H := H) s₀) H.D)
        (bytesAt s.mem ((tp s₀).setWidth 64) H.D)

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem body_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (h : Inv hH sc s₀ m s) :
    WP isa (body H) s fun t => Inv hH sc s₀ (m - 1) t ∧ t.zf = some (decide (m - 1 = 0)) := by
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
  refine WP.seq (WP.mono (ld_ok hp h.kr (.inl rfl)) fun l₁ ⟨kl₁, sl₁, ml₁⟩ => ?_)
  refine WP.seq (WP.mono (copyKey_ok hH hp kl₁ sl₁ (.inl rfl)) fun c₁ ⟨kc₁, fc₁, rc₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp kc₁ (.inl rfl)) fun a₁ ⟨ka₁, aa₁, ma₁⟩ =>
    updCall_ok hH hp ka₁ (.inl rfl) aa₁ fun u₁ ku₁ fu₁ ru₁ => ?_))
  refine WP.seq (WP.seq (WP.mono (finArgs_ok hH hp ku₁ (.inr rfl)) fun b₁ ⟨kb₁, ab₁, mb₁⟩ =>
    finCall_ok hH hp kb₁ (.inr rfl) ab₁ fun f₁ kf₁ ff₁ rf₁ => ?_))
  refine WP.seq (WP.mono (ld_ok hp kf₁ (.inl rfl)) fun l₂ ⟨kl₂, sl₂, ml₂⟩ => ?_)
  refine WP.seq (WP.mono (copyKey_ok hH hp kl₂ sl₂ (.inr rfl)) fun c₂ ⟨kc₂, fc₂, rc₂⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp kc₂ (.inr rfl)) fun a₂ ⟨ka₂, aa₂, ma₂⟩ =>
    updCall_ok hH hp ka₂ (.inr rfl) aa₂ fun u₂ ku₂ fu₂ ru₂ => ?_))
  refine WP.seq (WP.seq (WP.mono (finArgs_ok hH hp ku₂ (.inl rfl)) fun b₂ ⟨kb₂, ab₂, mb₂⟩ =>
    finCall_ok hH hp kb₂ (.inl rfl) ab₂ fun f₂ kf₂ ff₂ rf₂ => ?_))
  refine WP.seq (WP.mono (ld_ok hp kf₂ (.inr rfl)) fun l₃ ⟨kl₃, sl₃, ml₃⟩ => ?_)
  refine WP.seq (WP.mono (xor'_ok hp kl₃ sl₃) fun x ⟨kx, mx⟩ => ?_)
  refine WP.mono (dec_ok hm hn kx) fun t ⟨kt, mt, zt⟩ => ⟨⟨kt, fun k0 hk => ?_⟩, zt⟩
  -- The bytes of `U` and `T` at each point.
  obtain ⟨hl0, hrI, hrO⟩ := hk
  have U₁ : bytesAt c₁.mem (UA (H := H) s₀) H.D = bytesAt s.mem (UA (H := H) s₀) H.D := by
    rw [← ml₁]; exact bytes_keep fc₁ (by simp only [List.mem_singleton]; rintro r rfl; exact dU₁) hDn
  have T₁ : bytesAt c₁.mem ((tp s₀).setWidth 64) H.D = bytesAt s.mem ((tp s₀).setWidth 64) H.D := by
    rw [← ml₁]; exact bytes_keep fc₁ (by simp only [List.mem_singleton]; rintro r rfl; exact dT _ (st_sub hp)) hDn
  have T₂ : bytesAt u₁.mem ((tp s₀).setWidth 64) H.D = bytesAt c₁.mem ((tp s₀).setWidth 64) H.D := by
    rw [← ma₁]; exact bytes_keep fu₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₃ : bytesAt f₁.mem ((tp s₀).setWidth 64) H.D = bytesAt u₁.mem ((tp s₀).setWidth 64) H.D := by
    rw [← mb₁]; exact bytes_keep ff₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (tm_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₄ : bytesAt c₂.mem ((tp s₀).setWidth 64) H.D = bytesAt f₁.mem ((tp s₀).setWidth 64) H.D := by
    rw [← ml₂]; exact bytes_keep fc₂ (by simp only [List.mem_singleton]; rintro r rfl; exact dT _ (st_sub hp)) hDn
  have T₅ : bytesAt u₂.mem ((tp s₀).setWidth 64) H.D = bytesAt c₂.mem ((tp s₀).setWidth 64) H.D := by
    rw [← ma₂]; exact bytes_keep fu₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₆ : bytesAt f₂.mem ((tp s₀).setWidth 64) H.D = bytesAt u₂.mem ((tp s₀).setWidth 64) H.D := by
    rw [← mb₂]; exact bytes_keep ff₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (ua_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have M₄ : bytesAt c₂.mem (TM (H := H) s₀) H.D = bytesAt f₁.mem (TM (H := H) s₀) H.D := by
    rw [← ml₂]; exact bytes_keep fc₂ (by simp only [List.mem_singleton]; rintro r rfl; exact dM₁) hDn
  -- The inner hash.
  have rI₁ := rc₁ _ (by rw [add_zero']; exact hrI)
  have rU₁ := ru₁ _ (ma₁ ▸ rI₁) (by rw [xorPad_length, hl0])
  rw [ma₁, U₁] at rU₁
  have hl₁ : (xorPad k0 ipad ++ bytesAt s.mem (UA (H := H) s₀) H.D).length = H.B + H.D := by
    rw [List.length_append, xorPad_length, hl0, bytesAt_length]
  have dig₁ := rf₁ _ (mb₁ ▸ rU₁) (by rw [hl₁]; omega) (by rw [hl₁])
  -- The outer hash.
  have rO₂ := rc₂ _ hrO
  have rU₂ := ru₂ _ (ma₂ ▸ rO₂) (by rw [xorPad_length, hl0])
  rw [ma₂, M₄, bytesAt_take _ _ hDF, dig₁] at rU₂
  have hl₂ : (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ bytesAt s.mem (UA (H := H) s₀) H.D)).length =
      H.B + H.D := by
    rw [List.length_append, xorPad_length, hl0, ← dig₁, List.length_take, bytesAt_length, Nat.min_eq_left hDF]
  have dig₂ := rf₂ _ (mb₂ ▸ rU₂) (by rw [hl₂]; omega) (by rw [hl₂])
  rw [← bytesAt_take _ _ hDF] at dig₂
  -- `T ← T ⊕ U`.
  have hx : (Spec.Pbkdf2.xorBytes (bytesAt l₃.mem ((tp s₀).setWidth 64) H.D)
      (bytesAt l₃.mem (UA (H := H) s₀) H.D)).length = H.D := by
    rw [xorBytes_length' _ _ (by simp [bytesAt_length]), bytesAt_length]
  have Ux : bytesAt t.mem (UA (H := H) s₀) H.D = bytesAt f₂.mem (UA (H := H) s₀) H.D := by
    rw [mt, mx, ← ml₃]
    exact bytes_keep (Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := tR (H := H) s₀) (by
      rw [hx]; exact Region.contains_self _ _)) (by
        simp only [List.mem_singleton]; rintro r rfl; exact (dT _ ua).symm) hDn
  have Tx : bytesAt t.mem ((tp s₀).setWidth 64) H.D = Spec.Pbkdf2.xorBytes
      (bytesAt f₂.mem ((tp s₀).setWidth 64) H.D) (bytesAt f₂.mem (UA (H := H) s₀) H.D) := by
    rw [mt, mx, bytesAt_writeBytes_self' hx (by omega), ml₃]
  rw [h.it k0 ⟨hl0, hrI, hrO⟩, show m = (m - 1) + 1 by omega, Ux, Tx, dig₂, T₆, T₅, T₄, T₃, T₂, T₁,
    Nat.add_sub_cancel]
  rfl

/-! ## The prologue and the loop -/

omit hp in
theorem nn_lt : nn s₀ < 2 ^ 32 := (arg s₀ 2).isLt

theorem pro_ok : WP isa (.block (prologue H)) s₀ fun t => KR (H := H) sc s₀ (nn s₀) t ∧ t.gpr .esi = up s₀ ∧
      Frame [saveR H (scr s₀)] s₀.mem t.mem := by
  have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf
  obtain ⟨sR, _⟩ := mem_wr hp
  have dA : ∀ r ∈ [saveR H (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hp)
  simp only [prologue, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 4) (argW rfl 4) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega) (by omega)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (arg_sub rfl (by omega) (by have := hp.spf; omega))) (by decide)
  have i₂ : ∀ i < 5, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl hi
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 2 (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl,
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 2 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
    hm ▸ sv₂.of_eq H fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    (hm ▸ f₂').sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hp⟩⟩,
    by rw [u₅.gpr, u₄.mem, u₃.mem, rA 1 (by decide)], hm ▸ f₂'⟩

/-- `U` into `scratch`. -/
theorem copyU_ok {s : State} (hk : KR (H := H) sc s₀ (nn s₀) s) (hsi : s.gpr .esi = up s₀)
    (hf : Frame [saveR H (scr s₀)] s₀.mem s.mem) :
    WP isa (copy .esi 0 .ebp (uO H) H.D) s (Inv hH sc s₀ (nn s₀)) := by
  obtain ⟨hb, hf', hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = H.buf + H.S + H.F := rfl
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have nu := hp.nu
  have uR' : uR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have usub : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega)
  refine WP.mono (copy_ok (so := 0) (d := uO H) (n := H.D) (by decide) (by decide)
    hD0 (by omega) (by rw [hsi]; omega) (by rw [hk.ebp]; omega)
    (fun k hk' => by rw [hsi, add_zero']; exact inRegions_of_sub uR' (fun _ h => h) (by omega) hk')
    (fun k hk' => by rw [hk.ebp, hk.wr]; exact inRegions_of_sub sR usub (by omega) hk')
    (by rw [hsi, hk.ebp, add_zero']; exact hp.u_s.sub_right usub)) fun t c => ?_
  rw [hsi, hk.ebp, add_zero'] at c
  have fc : Frame [⟨UA (H := H) s₀, H.D⟩] s.mem t.mem :=
    c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨hk.keep c.rd c.wr (fun r hr => c.other r (not_cclob (kregs_clob r hr)))
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
/-- `test edi, edi`: the flags of whether there are steps. -/
theorem test_ok {s : State} (h : Inv hH sc s₀ (nn s₀) s) :
    WP isa (.block [.alu .test .edi (.reg .edi)]) s fun t => Inv hH sc s₀ (nn s₀) t ∧
      t.zf = some (decide (nn s₀ = 0)) := by
  refine wp_test fun s₁ f₁ z₁ => WP.block_nil ⟨⟨h.kr.keep f₁.rd f₁.wr
    (fun r _ => by rw [f₁.gpr]) (rs := []) (by rw [f₁.mem]; exact Frame.refl _ _) (by simp) (by simp),
    fun k0 hk => by rw [h.it k0 hk, f₁.mem]⟩, ?_⟩
  rw [z₁, h.kr.edi, test_z, Proof.Sha256.X86.Stream.toNat_ofNat_lt nn_lt]

theorem loop_ok {s : State} (h : Inv hH sc s₀ (nn s₀) s) (hz : s.zf = some (decide (nn s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body H) .ne)) s (Inv hH sc s₀ 0) := by
  have hlt := nn_lt (s₀ := s₀)
  refine WP.ite (decide (nn s₀ = 0)) (by show eval .e s = _; rw [eval_e, hz]) (fun h0 => WP.block_nil ?_)
    fun h0 => ?_
  · have e : nn s₀ = 0 := by simpa using h0
    exact e ▸ h
  · have hpos : 1 ≤ nn s₀ := by have := of_decide_eq_false h0; omega
    refine WP.loop (M := isa) (fun k t => ∃ m, k = m ∧ 1 ≤ m ∧ m ≤ nn s₀ ∧ Inv hH sc s₀ m t) ?_ (nn s₀) s
      ⟨nn s₀, rfl, hpos, (Nat.le_refl _), h⟩
    rintro k t ⟨m, hkm, h1, h2, ht⟩
    refine WP.mono (body_ok hH hp h1 (by omega) ht) fun t' ⟨ht', hz'⟩ => ?_
    have he : isa.eval .ne t' = some (!decide (m - 1 = 0)) := by
      show eval .ne t' = _; rw [eval_ne, hz']; rfl
    by_cases hl : m - 1 = 0
    · exact .inl ⟨by rw [he]; simp [hl], hl ▸ ht'⟩
    · exact .inr ⟨by rw [he]; simp [hl], m - 1, by omega, m - 1, rfl, by omega, by omega, ht'⟩

theorem correct : WP isa (iterate H) s₀ fun s' => abiPreserved s₀ s' ∧ (iterG hH.SH sc).post s₀ s' := by
  obtain ⟨hb, hf', hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  refine WP.seq (WP.mono (pro_ok hp) fun s₂ ⟨k₂, x₂, f₂⟩ => ?_)
  refine WP.seq (WP.mono (copyU_ok hH hp k₂ x₂ f₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (test_ok hH h₃) fun s₄ ⟨h₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hH hp h₄ z₄) fun s₅ h₅ => ?_)
  have k₅ := h₅.kr
  have hL : 8 * H.W + 16 ≤ 8 * sc := by omega
  refine WP.mono (restore_ok H k₅.ebp k₅.saved (by rw [k₅.wr]; exact (mem_wr hp).1) hL hnw)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact k₅.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₅.esp]
    · exact hg r (callee_saved r hr he)
  intro k0 hl hrI hrO
  have hS' := hH.hS; have hD' := hH.hD; have hB' := hH.hB
  rw [hB'] at hl
  rw [hS'] at hrO
  show bytesAt s'.mem ((tp s₀).setWidth 64) hH.SH.digestBytes = _
  rw [hD', hm, h₅.it k0 ⟨hl, hrI, hrO⟩]
  rfl

end

end VG.Proof.Pbkdf2.Generic.X86
