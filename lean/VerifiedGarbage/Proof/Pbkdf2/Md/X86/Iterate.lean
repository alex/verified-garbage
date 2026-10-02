import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on x86 (32-bit): correct

The iteration (`Impl/Pbkdf2/Md/X86.lean`) is correct for any hash function
whose code the proofs know (`MdOk`): `Md.hmac_step` says that its two
compressions per step compute HMAC. The arguments are on the stack: `scratch`,
`key`, `n` and `u` are loaded first (after our caller's registers are saved in
`scratch`), and `t` in each step. The loop counts the steps left in `edi` down
with `sub`, and branches on its result.
-/

namespace VG.Proof.Pbkdf2.Md.X86.Iterate

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash copyW)
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK iterG SavedRegs saveR savedRegs save_ok restore_ok callee_saved ea_at stk
  After setWidth_add toNat_add_ofNat stk_ret stk_args arg_contains arg_keep argAddr_eq saved_mem test_z)
open VG.Proof.Hmac.Generic.Common (InRegions.right' bytesAt_writeBytes_self' bytesAt_take covers_one)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_test
  sub_offset ofNat_beq_zero sub_ofNat eval_e eval_ne)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep writeBytes_at bytesAt_getD')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

section
variable (H : Hash) (sc : Nat) (s₀ : State)

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
/-- Byte `o` of `scratch`. -/
abbrev SA (o : Nat) : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 o
/-- The hash value being compressed, as `ebx` holds it, and its address;
the block is right after it. -/
abbrev hv : BitVec 32 := scr s₀ + BitVec.ofNat 32 H.st.buf
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨(scr s₀).setWidth 64, H.so⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR H s₀, uR H s₀, argR s₀]
  wr : s₀.wr = [tR H s₀, scR sc s₀]
  k_t : (keyR H s₀).Disjoint (tR H s₀)
  k_s : (keyR H s₀).Disjoint (scR sc s₀)
  u_t : (uR H s₀).Disjoint (tR H s₀)
  u_s : (uR H s₀).Disjoint (scR sc s₀)
  t_s : (tR H s₀).Disjoint (scR sc s₀)
  a_t : (argR s₀).Disjoint (tR H s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  r_t : (retR s₀).Disjoint (tR H s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_k : (stkR s₀).Disjoint (keyR H s₀)
  b_u : (stkR s₀).Disjoint (uR H s₀)
  b_t : (stkR s₀).Disjoint (tR H s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  nk : (key s₀).toNat + 2 * H.S ≤ 2 ^ 32
  nu : (up s₀).toNat + H.D ≤ 2 ^ 32
  nt : (tp s₀).toNat + H.D ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.st.buf + H.N + H.B ≤ 8 * sc
  hz : Sizes H

theorem pre_of {H : Hash} (hH : HashOK H.st) {sc : Nat} {s₀ : State} (h : (iterG hH.SH sc).pre s₀) (hz : Sizes H)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) : Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h19]; rfl
  simp only [hS, hD, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, hfit, hz⟩

/-! ## The parts of `scratch` -/

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ H.st.buf + H.N + H.B ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ 0 < H.D ∧ H.D ≤ H.N ∧ H.B ≤ 128 ∧ 64 ≤ H.B ∧
    H.S = H.N + H.B :=
  ⟨rfl, hp.fits, hp.nw, hp.hz.so, hp.hz.W, hp.hz.N.1, hp.hz.N.2.1, hp.hz.D.1, hp.hz.D.2.1, hp.hz.B4.2.2,
    hp.hz.B4.2.1, hp.hz.S⟩

theorem off_sub {o n : Nat} (h : o + n ≤ 8 * sc) : Region.Sub ⟨SA s₀ o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega)

theorem hv_eq : (hv H s₀).setWidth 64 = SA s₀ H.st.buf :=
  setWidth_add (by have := bounds hp; omega)

theorem hv_toNat : (hv H s₀).toNat = (scr s₀).toNat + H.st.buf :=
  toNat_add_ofNat (by have := bounds hp; omega)

/-- The hash value and the block. -/
theorem hvR_sub : Region.Sub ⟨(hv H s₀).setWidth 64, H.N + H.B⟩ (scR sc s₀) := by
  rw [hv_eq hp]; obtain ⟨-, hf, -⟩ := bounds hp; exact off_sub hp (by omega)

theorem cmp_sub : Region.Sub (cmpR H s₀) (scR sc s₀) := by
  obtain ⟨hb, hf, -, hso, -⟩ := bounds hp; exact Region.sub_prefix (by omega)

theorem save_sub : Region.Sub (saveR H.st (scr s₀)) (scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := bounds hp; exact off_sub hp (by omega)

/-- The parts of `scratch` do not overlap. -/
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 8 * sc) (hb : b + n ≤ 8 * sc) :
    Region.Disjoint ⟨SA s₀ a, m⟩ ⟨SA s₀ b, n⟩ :=
  VG.Proof.Hmac.Generic.Common.off_disj _ h (by have := hp.nw; omega) (by have := hp.nw; omega)

theorem hv_cmp : Region.Disjoint ⟨(hv H s₀).setWidth 64, H.N + H.B⟩ (cmpR H s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := bounds hp
  rw [hv_eq hp]; exact Offset.disjoint_base _ (by omega) (by omega)

theorem save_hv {n : Nat} (h : n ≤ H.N + H.B) : (saveR H.st (scr s₀)).Disjoint ⟨(hv H s₀).setWidth 64, n⟩ := by
  obtain ⟨hb, hf, -⟩ := bounds hp
  rw [hv_eq hp]; exact part_disj hp (by omega) (by omega) (by omega)

theorem save_cmp : (saveR H.st (scr s₀)).Disjoint (cmpR H s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := bounds hp
  exact Offset.disjoint_base _ (by omega) (by omega)

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have := hp.spf; omega)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have := hp.spf; omega)

theorem t_hv {n : Nat} (h : n ≤ H.N + H.B) : Region.Disjoint (tR H s₀) ⟨(hv H s₀).setWidth 64, n⟩ :=
  hp.t_s.sub_right fun a ha => hvR_sub hp a (Region.sub_prefix h a ha)

theorem t_blk : Region.Disjoint (tR H s₀) ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ := by
  obtain ⟨hb, hf, hw, -⟩ := bounds hp
  refine hp.t_s.sub_right fun a ha => hvR_sub hp a (Offset.sub_base _ (by omega) a ha)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: `T`, `scratch` and the stack below `esp`. -/
abbrev wrs (H : Hash) (sc : Nat) (s₀ : State) : List Region := [tR H s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on, with `m` steps left. -/
structure KR (H : Hash) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  ebx : s.gpr .ebx = hv H s₀
  esi : s.gpr .esi = key s₀
  edi : s.gpr .edi = BitVec.ofNat 32 m
  saved : SavedRegs H.st (scr s₀) s₀ s.mem
  frame : Frame (wrs H sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .ebx, .esi, .edi]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

section
variable {H : Hash} {sc : Nat} {s₀ : State}

theorem KR.keep {m : Nat} {s s' : State} (h : KR H sc s₀ m s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs H sc s₀, Region.Sub r r') : KR H sc s₀ m s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.ebx, (hg _ (by simp)).trans h.esi, (hg _ (by simp)).trans h.edi,
    h.saved.frame H.st hf hs, h.frame.trans (hf.sub hsub)⟩

/-- `KR` after code that writes only `eax`, `ecx` and `edx` and a part of
`scratch` other than where our caller's registers are. -/
theorem KR.write {m : Nat} {s s' : State} (h : KR H sc s₀ m s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) {R : Region} (hf : Frame [R] s.mem s'.mem)
    (hs : (saveR H.st (scr s₀)).Disjoint R) (hsub : ∃ r' ∈ wrs H sc s₀, Region.Sub R r') : KR H sc s₀ m s' :=
  h.keep hrd hwr (fun r hr => hg r (by revert hr; decide +revert) (by revert hr; decide +revert)
    (by revert hr; decide +revert)) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hs)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsub)

theorem stk_eq {m : Nat} {s : State} (hk : KR H sc s₀ m s) : stk s = stkR s₀ := by rw [stk, hk.esp]

end

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

theorem mem_wr : scR sc s₀ ∈ s₀.wr ∧ tR H s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem argR_in : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, argR_in hp, arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

theorem KR.argEq {m : Nat} {s : State} (hk : KR H sc s₀ m s) {i : Nat} (hi : i < 5) :
    VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have := hp.spf; omega) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_t
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega)

theorem KR.readArg {m : Nat} {s : State} (hk : KR H sc s₀ m s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

theorem KR.ret {m : Nat} {s : State} (hk : KR H sc s₀ m s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.r_t
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

/-- `KR` after a call that writes parts of `scratch`. -/
theorem KR.call {m : Nat} {s s' : State} (h : KR H sc s₀ m s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws, (saveR H.st (scr s₀)).Disjoint r) (hsub : ∀ r ∈ ws, Region.Sub r (scR sc s₀)) :
    KR H sc s₀ m s' := by
  have f := ha.frame
  rw [stk_eq h] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.b_s.symm.sub_left (save_sub hp)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨scR sc s₀, by simp, hsub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- The hash value and block are writable. -/
theorem cov_hv {s : State} (hwr : s.wr = s₀.wr) : Covers [⟨(hv H s₀).setWidth 64, H.N + H.B⟩] s.wr := by
  obtain ⟨hb, hf, -⟩ := bounds hp
  rw [hv_eq hp, hwr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scR sc s₀, (mem_wr hp).1, H.st.buf, rfl, by simp only; omega⟩

/-- The arguments of the compression of the block. -/
theorem cmpArgs {m : Nat} {s : State} (hk : KR H sc s₀ m s) (hax : s.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N) :
    CmpArgs H.N H.B H.so s (hv H s₀) (scr s₀) := by
  obtain ⟨hb, hf, hw, hso, -⟩ := bounds hp
  have := hv_toNat hp
  exact
    { ebx := hk.ebx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := cov_hv hp hk.wr
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨scR sc s₀, (mem_wr hp).1, 0, by simp, by simp only; omega⟩
      st_sc := hv_cmp hp
      b_st := by rw [stk_eq hk]; exact hp.b_s.sub_right (hvR_sub hp)
      b_sc := by rw [stk_eq hk]; exact hp.b_s.sub_right (cmp_sub hp)
      nst := by omega
      nsc := by omega }

/-- The key's bytes are as on entry. -/
theorem key_bytes {m : Nat} {s : State} (hk : KR H sc s₀ m s) {i : Nat} (hi : i < 2 * H.S) :
    s.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 i) = s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 i) :=
  hk.frame.bytes (R := keyR H s₀) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.k_t
    · exact hp.k_s
    · exact hp.b_k.symm) (by show 2 * H.S ≤ 2 ^ 64; have := hp.nk; omega) hi

end

/-! ## The loop invariant -/

section
variable {H : Hash} (hO : MdOk H) (s₀ : State)

/-- A step, as the code computes it, from the key's inner and outer hash values. -/
abbrev stepM : List Byte → List Byte :=
  hO.md.step H.D (hO.md.stateAt s₀.mem ((key s₀).setWidth 64))
    (hO.md.stateAt s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 H.S))

end

/-- The loop invariant, with `m` steps left. -/
structure Inv {H : Hash} (hO : MdOk H) (sc : Nat) (s₀ : State) (m : Nat) (s : State) : Prop
    extends KR H sc s₀ m s where
  pad : bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB
  le : m ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM hO s₀) (nn s₀) (bytesAt s₀.mem ((up s₀).setWidth 64) H.D)
      (bytesAt s₀.mem ((tp s₀).setWidth 64) H.D) =
    Spec.Pbkdf2.iterate (stepM hO s₀) m (bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)
      (bytesAt s.mem ((tp s₀).setWidth 64) H.D)

/-! ## Loading a hash value of the key and compressing the block into it -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

/-- The block, after the hash value, is outside what the load and the
compression write. -/
theorem blk_disj {a n : Nat} (h₁ : H.N ≤ a) (h₂ : a + n ≤ H.N + H.B) :
    ∀ r ∈ [(⟨(hv H s₀).setWidth 64, H.N⟩ : Region), cmpR H s₀, stkR s₀],
      Region.Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
  obtain ⟨hb, hf, hw, -⟩ := bounds hp
  have := hv_toNat hp
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ h₁ (by omega)
  · exact (hv_cmp hp).sub_left (Offset.sub_base _ (by omega))
  · exact (hp.b_s.sub_right fun a' ha' => hvR_sub hp a' (Offset.sub_base _ (by omega) a' ha')).symm

/-- Loading the key's hash value at `key + o` into the hash value being
compressed, and `eax` at the block. -/
theorem load_ok {o : Nat} (ho : o + H.N ≤ 2 * H.S) {m : Nat} {s : State} (h : KR H sc s₀ m s)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', KR H sc s₀ m s' → s'.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N →
      Frame [⟨(hv H s₀).setWidth 64, H.N⟩] s.mem s'.mem →
      hO.md.stateAt s'.mem ((hv H s₀).setWidth 64) = hO.md.stateAt s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.loadKey o ++ H.atBlk ++ rest)) s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  have hN4 := hp.hz.N.2.2
  have hn4 : 4 * (H.N / 4) = H.N := by omega
  have hvt := hv_toNat hp
  have nk := hp.nk
  have kc : Covers [keyR H s₀] (s.rd ++ s.wr) := covers_one (by rw [h.rd, hp.rd]; simp)
  rw [List.append_assoc]
  refine copyW_ok (by decide) (by decide) (H.N / 4) _ s _ h.esi h.ebx (by omega) (by omega)
    (fun j hj => by rw [addr_eq (by omega)]; exact inReg kc (by omega) (by omega))
    (fun j hj => by rw [addr_eq (by omega)]; exact inReg (cov_hv hp h.wr) (by omega) (by omega)) ?_
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · rw [hn4]
    exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega))
      (by rw [BitVec.add_zero, hv_eq hp]; exact Offset.contains_base _ (by omega) (by omega))
  rw [hn4, BitVec.add_zero] at m₁
  have f₁ : Frame [⟨(hv H s₀).setWidth 64, H.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine atBlk_ok fun s₂ e₂ g₂ m₂ rd₂ wr₂ => ?_
  have k₂ : KR H sc s₀ m s₂ := h.write (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    (fun r h1 h2 _ => by rw [g₂ r h1, g₁ r h2]) (m₂ ▸ f₁) (save_hv hp (by omega))
    ⟨scR sc s₀, by simp, fun a ha => hvR_sub hp a (Region.sub_prefix (by omega) a ha)⟩
  refine k s₂ k₂ (by rw [e₂, g₁ _ (by decide), h.ebx]) (m₂ ▸ f₁) ?_
  refine hO.reloc _ _ _ _ fun i hi => ?_
  rw [m₂, m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi, Memory.add_ofNat]
  exact key_bytes hp h (by omega)

/-- The compression of the block into the hash value. -/
theorem cmpS_ok {m : Nat} {s : State} (h : KR H sc s₀ m s) (hax : s.gpr .eax = hv H s₀ + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (k : ∀ s', KR H sc s₀ m s' → Frame [⟨(hv H s₀).setWidth 64, H.N⟩, cmpR H s₀, stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((hv H s₀).setWidth 64) = hO.md.compress (hO.md.stateAt s.mem ((hv H s₀).setWidth 64))
        (hO.md.blockAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  refine cmp_ok hO.comp (by omega) (cmpArgs hp h hax) fun s₃ ha e₃ => ?_
  have k₃ : KR H sc s₀ m s₃ := h.call hp ha (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact save_hv hp (by omega)
      · exact save_cmp hp) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact fun a ha => hvR_sub hp a (Region.sub_prefix (by omega) a ha)
      · exact cmp_sub hp)
  have f := ha.frame
  rw [stk_eq h] at f
  exact k s₃ k₃ (f.mono (by simp)) e₃

theorem lc_ok {o : Nat} (ho : o + H.N ≤ 2 * H.S) {m : Nat} {s : State} (h : KR H sc s₀ m s)
    (hpad : bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB) {c : Prog isa}
    {Q : State → Prop}
    (k : ∀ s', KR H sc s₀ m s' → Frame [⟨(hv H s₀).setWidth 64, H.N⟩, cmpR H s₀, stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((hv H s₀).setWidth 64) = hO.md.compress
        (hO.md.stateAt s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 o))
        (hO.md.tailBlock H.D (bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)) →
      bytesAt s'.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB →
      bytesAt s'.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D → WP isa c s' Q) :
    WP isa (.block (H.loadKey o ++ H.atBlk)) s fun s' => WP isa (.seq H.cmp c) s' Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  rw [← List.append_nil (H.loadKey o ++ H.atBlk)]
  refine load_ok hO hp ho h fun s₂ k₂ ax₂ f₁ st₂ => WP.block_nil (WP.seq (cmpS_ok hO hp k₂ ax₂ fun s₃ k₃ f₂ e₃ => ?_))
  have dB : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
      ∀ r ∈ [(⟨(hv H s₀).setWidth 64, H.N⟩ : Region)], Region.Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r :=
    fun h₁ h₂ r hr => blk_disj hp h₁ h₂ r (by simp only [List.mem_singleton] at hr; simp [hr])
  have pad₂ : bytesAt s₂.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 H.D) (H.B - H.D) =
      hO.md.tailPad H.D := by
    rw [Memory.add_ofNat, Memory.frame_bytesAt f₁ (dB (by omega) (by omega)) (by omega), hpad, hO.tail]
  have u₂ : bytesAt s₂.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
      bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D :=
    Memory.frame_bytesAt f₁ (dB (by omega) (by omega)) (by omega)
  have f₃ : Frame [⟨(hv H s₀).setWidth 64, H.N⟩, cmpR H s₀, stkR s₀] s.mem s₃.mem :=
    (f₁.mono (by simp)).trans f₂
  refine k s₃ k₃ f₃ ?_ ?_ ?_
  · rw [e₃, st₂, Md.blockAt_tailPad (by omega) pad₂, u₂]
  · rw [Memory.frame_bytesAt f₃ (blk_disj hp (by omega) (by omega)) (by omega), hpad]
  · exact Memory.frame_bytesAt f₃ (blk_disj hp (by omega) (by omega)) (by omega)

/-! ## The end of a step: the digest, `T ← T ⊕ U` and the count -/

omit hp in
theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    VG.WriteBytes.write_eq_writeBytes]
  refine congrArg (writeBytes m d) ?_
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

omit hp in
theorem wp_xorm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine VG.Proof.Sha256.X86.Stream.WP.cons
    (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 32) false false).setReg d (s.gpr d ^^^ s.mem.readW a 32))
    ?_ (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load32, ha, hin]

omit hp in
/-- `T ← T ⊕ U` for the first `n` words of `T` at `t` (in `edx`) and `U` at
`x + N` (`x` in `ebx`). -/
theorem xor_ok {x t : BitVec 32} (hd : Region.Disjoint ⟨t.setWidth 64, H.D⟩ ⟨x.setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩)
    (fx : x.toNat + H.N + H.D ≤ 2 ^ 32) (ft : t.toNat + H.D ≤ 2 ^ 32) :
    ∀ n, 4 * n ≤ H.D → ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .ebx = x → s.gpr .edx = t →
    (∀ k < n, InRegions (s.rd ++ s.wr) (addr x (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (addr t (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (t.setWidth 64)
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem (t.setWidth 64) (4 * n))
          (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbx hdx hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hbx hdx (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [Hash.xorW, List.cons_append, List.nil_append]
    have eU : addr x (H.N + 4 * n) = x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n) := by
      rw [addr_eq (by omega), Memory.add_ofNat]
    have eT : addr t (4 * n) = t.setWidth 64 + BitVec.ofNat 64 (4 * n) := addr_eq (by omega)
    refine wp_movm (a := addr x (H.N + 4 * n)) (by rw [ea_at, g₁ _ (by decide), hbx])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    have hw := hout n (by omega)
    refine wp_xorm (a := addr t (4 * n)) (by rw [ea_at, u₂.other _ (by decide), g₁ _ (by decide), hdx])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact InRegions.right' hw) fun s₃ u₃ => ?_
    refine wp_store (a := addr t (4 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hdx])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hw) fun s₄ u₄ => k s₄ (fun r hr => by
        rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr]) (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁])
        (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem (t.setWidth 64) (4 * n))
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N) (4 * n))).length = 4 * n := by
      rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, writeW_xor32, m₁, eU, eT,
      bytesAt_writeBytes_sep (p := t.setWidth 64 + BitVec.ofNat 64 (4 * n)),
      bytesAt_writeBytes_sep (p := x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n))]
    · have e := writeBytes_append s.mem (t.setWidth 64) _ (Spec.Pbkdf2.xorBytes
        (bytesAt s.mem (t.setWidth 64 + BitVec.ofNat 64 (4 * n)) 4)
        (bytesAt s.mem (x.setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n)) 4))
        (by rw [hl, Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro y h₁ h₂
      rw [hl] at h₂
      exact hd y (by simp only [Region.Contains]; omega) (Memory.off_contains h₁ (by omega) (by omega))
    · omega
    · intro y h₁ h₂
      rw [hl] at h₂
      exact Memory.sep_after h₁ h₂ (by omega)
    · omega

theorem tail_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 32) {s : State} (h : KR H sc s₀ m s)
    (hpad : bytesAt s.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB)
    {Q : State → Prop}
    (k : ∀ s', KR H sc s₀ (m - 1) s' → s'.zf = some (decide (m - 1 = 0)) →
      Frame [⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩, tR H s₀] s.mem s'.mem →
      bytesAt s'.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB →
      bytesAt s'.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        (hO.md.digest (hO.md.stateAt s.mem ((hv H s₀).setWidth 64))).take H.D →
      bytesAt s'.mem ((tp s₀).setWidth 64) H.D = Spec.Pbkdf2.xorBytes (bytesAt s.mem ((tp s₀).setWidth 64) H.D)
        ((hO.md.digest (hO.md.stateAt s.mem ((hv H s₀).setWidth 64))).take H.D) → Q s') :
    WP isa (.block (H.digest ++ H.tStep)) s Q := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  have hD4 := hp.hz.D.2.2
  have hvt := hv_toNat hp
  have nt := hp.nt
  have hD4' : 4 * (H.D / 4) = H.D := by omega
  have sbB : Region.Sub ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (scR sc s₀) :=
    fun a ha => hvR_sub hp a (Offset.sub_base _ (by omega) a ha)
  refine digest_ok hp.hz hO.out h.ebx (by omega) (cov_hv hp h.wr) hpad fun s₁ g₁ rd₁ wr₁ f₁ b₁ p₁ => ?_
  have k₁ : KR H sc s₀ m s₁ := h.write rd₁ wr₁ g₁ f₁
    ((save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega))) ⟨scR sc s₀, by simp, sbB⟩
  simp only [Hash.tStep, List.cons_append, List.nil_append]
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, k₁.esp]; rfl) (argIn hp k₁.rd k₁.wr (by decide))
    fun s₂ u₂ => ?_
  have dx₂ : s₂.gpr .edx = tp s₀ := by rw [u₂.gpr, k₁.readArg hp (by decide)]
  have k₂ : KR H sc s₀ m s₂ := k₁.write u₂.rd u₂.wr (fun r _ _ h3 => u₂.other r h3) (R := ⟨0, 0⟩)
    (by rw [u₂.mem]; exact Frame.refl _ _) (fun _ _ h => by simp [Region.Contains] at h)
    ⟨scR sc s₀, by simp, fun _ h => by simp [Region.Contains] at h⟩
  have hd : Region.Disjoint ⟨(tp s₀).setWidth 64, H.D⟩ ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩ :=
    (t_blk hp).sub_right (Region.sub_prefix (by omega))
  refine xor_ok hd (by omega) nt (H.D / 4) (by omega) _ s₂ _ k₂.ebx dx₂
    (fun j hj => by
      rw [addr_eq (by omega)]
      exact InRegions.right' (inReg (cov_hv hp k₂.wr) (by omega) (by omega)))
    (fun j hj => by
      rw [addr_eq (by omega), k₂.wr]
      exact ⟨tR H s₀, (mem_wr hp).2, Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  rw [hD4'] at m₃
  have hxl : (Spec.Pbkdf2.xorBytes (bytesAt s₂.mem ((tp s₀).setWidth 64) H.D)
      (bytesAt s₂.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D)).length = H.D := by
    rw [Memory.xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have f₃ : Frame [tR H s₀] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  have k₃ : KR H sc s₀ m s₃ := k₂.write rd₃ wr₃ (fun r _ h2 _ => g₃ r h2) f₃
    (hp.t_s.sub_right (save_sub hp)).symm ⟨tR H s₀, by simp, fun _ h => h⟩
  refine wp_subi fun s₄ u₄ z₄ => WP.block_nil ?_
  have e₄ : s₃.gpr .edi - 1 = BitVec.ofNat 32 (m - 1) := by
    rw [k₃.edi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hm]
  have k₄ : KR H sc s₀ (m - 1) s₄ :=
    ⟨by rw [u₄.rd, k₃.rd], by rw [u₄.wr, k₃.wr], by rw [u₄.other _ (by decide), k₃.esp],
      by rw [u₄.other _ (by decide), k₃.ebp], by rw [u₄.other _ (by decide), k₃.ebx],
      by rw [u₄.other _ (by decide), k₃.esi], by rw [u₄.gpr, e₄], u₄.mem ▸ k₃.saved, u₄.mem ▸ k₃.frame⟩
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  have tB : ∀ r ∈ [tR H s₀], Region.Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ r := by
    simp only [List.mem_singleton]; rintro r rfl; exact (t_blk hp).symm
  have tB' : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
      ∀ r ∈ [tR H s₀], Region.Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h₁ h₂ r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact ((t_blk hp).sub_right (Offset.sub _ (by omega) (by omega))).symm
  refine k s₄ k₄ (by rw [z₄, e₄, ofNat_beq_zero (by omega)]) ?_ ?_ ?_ ?_
  · rw [u₄.mem]; exact (f₁.mono (by simp)).trans (m₂ ▸ f₃.mono (by simp))
  · rw [u₄.mem, Memory.frame_bytesAt f₃ (tB' (by omega) (by omega)) (by omega), m₂, p₁]
  · rw [u₄.mem, Memory.frame_bytesAt f₃ (tB' (Nat.le_refl _) (by omega)) (by omega), m₂, b₁]
  · have hT₁ : bytesAt s₁.mem ((tp s₀).setWidth 64) H.D = bytesAt s.mem ((tp s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact t_blk hp) (by omega)
    rw [u₄.mem, m₃, bytesAt_writeBytes_self' hxl (by omega), m₂, hT₁, b₁]

end

/-! ## A step -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

omit hp in
theorem iterate_succ (f : List Byte → List Byte) (n : Nat) (u t : List Byte) :
    Spec.Pbkdf2.iterate f (n + 1) u t = Spec.Pbkdf2.iterate f n (f u) (Spec.Pbkdf2.xorBytes t (f u)) := rfl

theorem body_ok {r : Nat} {s : State} (h : Inv hO sc s₀ (r + 1) s) :
    WP isa H.body s fun s' => eval .ne s' = some (r != 0) ∧ Inv hO sc s₀ r s' := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  have hvt := hv_toNat hp
  have hlt : r + 1 < 2 ^ 32 := by have := h.le; have := (arg s₀ 2).isLt; simp only [nn] at *; omega
  have sbB : Region.Sub ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (scR sc s₀) :=
    fun a ha => hvR_sub hp a (Offset.sub_base _ (by omega) a ha)
  unfold Hash.body
  refine WP.seq (lc_ok hO hp (o := 0) (by omega) h.toKR h.pad fun s₂ k₂ f₂ e₂ p₂ u₂ => ?_)
  refine WP.seq ?_
  rw [List.append_assoc]
  refine digest_ok hp.hz hO.out k₂.ebx (by omega) (cov_hv hp k₂.wr) p₂ fun s₃ g₃ rd₃ wr₃ f₃ b₃ p₃ => ?_
  have k₃ : KR H sc s₀ (r + 1) s₃ := k₂.write rd₃ wr₃ g₃ f₃
    ((save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega))) ⟨scR sc s₀, by simp, sbB⟩
  refine lc_ok hO hp (o := H.S) (by omega) k₃ p₃ fun s₅ k₅ f₅ e₅ p₅ u₅ => ?_
  refine tail_ok hO hp (m := r + 1) (by omega) hlt k₅ p₅ fun s₈ k₈ z₈ f₈ p₈ b₈ t₈ => ?_
  rw [Nat.add_sub_cancel] at k₈ z₈
  -- `T` is untouched until the end.
  have dT : ∀ {rs : List Region}, (∀ q ∈ rs, Region.Sub q (scR sc s₀) ∨ q = stkR s₀) →
      ∀ q ∈ rs, Region.Disjoint ⟨(tp s₀).setWidth 64, H.D⟩ q := by
    intro rs hrs q hq
    rcases hrs q hq with hq | rfl
    · exact hp.t_s.sub_right hq
    · exact hp.b_t.symm
  have sub₁ : ∀ q ∈ [(⟨(hv H s₀).setWidth 64, H.N⟩ : Region), cmpR H s₀, stkR s₀],
      Region.Sub q (scR sc s₀) ∨ q = stkR s₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl)
    · exact .inl fun a ha => hvR_sub hp a (Region.sub_prefix (by omega) a ha)
    · exact .inl (cmp_sub hp)
    · exact .inr rfl
  have hT₅ : bytesAt s₅.mem ((tp s₀).setWidth 64) H.D = bytesAt s.mem ((tp s₀).setWidth 64) H.D := by
    rw [Memory.frame_bytesAt f₅ (dT sub₁) (by omega),
      Memory.frame_bytesAt f₃ (dT (by simp only [List.mem_singleton]; rintro q rfl; exact .inl sbB)) (by omega),
      Memory.frame_bytesAt f₂ (dT sub₁) (by omega)]
  rw [hT₅, e₅, b₃, e₂, show (key s₀).setWidth 64 + BitVec.ofNat 64 0 = (key s₀).setWidth 64 by simp] at t₈
  rw [e₅, b₃, e₂, show (key s₀).setWidth 64 + BitVec.ofNat 64 0 = (key s₀).setWidth 64 by simp] at b₈
  refine ⟨?_, { k₈ with pad := p₈, le := by have := h.le; omega, val := ?_ }⟩
  · rw [eval_ne, z₈, Option.map_some]
    cases r <;> rfl
  · rw [h.val, iterate_succ, b₈, t₈]; rfl

theorem loop_ok {n : Nat} {s : State} (h : Inv hO sc s₀ n s) (hz' : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop H.body .ne)) s (Inv hO sc s₀ 0) := by
  refine WP.ite (decide (n = 0)) (by show s.zf = _; exact hz') (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv hO sc s₀ (m + 1) s)
      (fun m s hs' => WP.mono (body_ok hO hp hs') fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

end

/-! ## The prologue and the epilogue -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

theorem pro_ok : WP isa (.block H.prologue) s₀ fun s => Inv hO sc s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)) := by
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS⟩ := bounds hp
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have hvt := hv_toNat hp
  have hD4 := hp.hz.D.2.2
  have hD4' : 4 * (H.D / 4) = H.D := by omega
  have tl := hp.hz.tail_length
  have nu := hp.nu; have nt := hp.nt
  have dA : ∀ r ∈ [saveR H.st (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hp)
  simp only [Hash.prologue, List.append_assoc, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at]; rfl) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H.st (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega) (by omega)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H.st (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (VG.Proof.Pbkdf2.Stream.X86.arg_sub rfl (by omega) (by have := hp.spf; omega))) (by decide)
  have i₂ : ∀ i < 5, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl hi
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 0) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 2) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 2 (by decide)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by
      rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide))
    fun s₈ u₈ => ?_
  have m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have bp₈ : s₈.gpr .ebp = scr s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl
  have bx₈ : s₈.gpr .ebx = hv H s₀ := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]
    rfl
  have si₈ : s₈.gpr .esi = key s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.mem, rA 0 (by decide)]
  have di₈ : s₈.gpr .edi = arg s₀ 2 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem,
      rA 2 (by decide)]
  have dx₈ : s₈.gpr .edx = up s₀ := by
    rw [u₈.gpr, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, rA 1 (by decide)]
  have sp₈ : s₈.gpr .esp = E s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
  have ucov : Covers [uR H s₀] (s₈.rd ++ s₈.wr) := covers_one (by rw [rd₈, hp.rd]; simp)
  -- `U` into the block.
  refine copyW_ok (by decide) (by decide) (H.D / 4) _ s₈ _ dx₈ bx₈ (by omega) (by omega)
    (fun j hj => by
      rw [addr_eq (by omega)]; have := inReg (o := 4 * j) (n := 4) ucov (by omega) (by omega)
      rwa [show 0 + 4 * j = 4 * j by omega])
    (fun j hj => by rw [addr_eq (by omega)]; exact inReg (cov_hv hp wr₈) (by omega) (by omega)) ?_
    fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  · rw [hD4', BitVec.add_zero]
    exact hp.u_s.sep (Region.contains_self _ _)
      (by rw [hv_eq hp, Memory.add_ofNat]; exact Offset.contains_base _ (by omega) (by omega))
  rw [hD4', BitVec.add_zero] at m₉
  -- The padding.
  refine pad_ok hp.hz (s := s₉) (x := hv H s₀) (by rw [g₉ _ (by decide), bx₈]) (by omega) (cov_hv hp (wr₉.trans wr₈))
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ m₁₀ => ?_
  refine wp_test fun s₁₁ u₁₁ z₁₁ => WP.block_nil ?_
  have m₁₁ : s₁₁.mem = writeBytes (writeBytes s₂.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N)
      (bytesAt s₂.mem ((up s₀).setWidth 64) H.D)) ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) H.tailB := by
    rw [u₁₁.mem, m₁₀, m₉, m₈]
  have gr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁₁.gpr r = s₈.gpr r := fun r _ h2 _ => by
    rw [u₁₁.gpr, g₁₀ r h2, g₉ r h2]
  have fB : Frame [⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩] s₂.mem s₁₁.mem := by
    rw [m₁₁]
    refine (writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]
      have := Offset.contains_base ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) (d := 0) (n := H.D) (k := H.B)
        (by omega) (by omega)
      rwa [BitVec.add_zero] at this
    · rw [tl, ← Memory.add_ofNat]; exact Offset.contains_base _ (by omega) (by omega)
  have sbB : Region.Sub ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ (scR sc s₀) :=
    fun a ha => hvR_sub hp a (Offset.sub_base _ (by omega) a ha)
  have dsB : (saveR H.st (scr s₀)).Disjoint ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩ :=
    (save_hv hp (Nat.le_refl _)).sub_right (Offset.sub_base _ (by omega))
  have sv : SavedRegs H.st (scr s₀) s₀ s₁₁.mem :=
    (sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)).frame H.st fB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dsB)
  have fr : Frame (wrs H sc s₀) s₀.mem s₁₁.mem :=
    (f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hp⟩).trans
    (fB.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, sbB⟩)
  have edi : s₁₁.gpr .edi = BitVec.ofNat 32 (nn s₀) := by
    rw [gr _ (by decide) (by decide) (by decide), di₈, nn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have dU : Mem.Sep ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D
      ((hv H s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) H.tailB.length := by
    rw [tl, ← Memory.add_ofNat]
    have := Offset.sep ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) (d := 0) (n := H.D) (e := H.D)
      (k := H.B - H.D) (.inl (by omega)) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  refine ⟨⟨⟨by rw [u₁₁.rd, rd₁₀, rd₉, rd₈], by rw [u₁₁.wr, wr₁₀, wr₉, wr₈],
    by rw [gr _ (by decide) (by decide) (by decide), sp₈], by rw [gr _ (by decide) (by decide) (by decide), bp₈],
    by rw [gr _ (by decide) (by decide) (by decide), bx₈], by rw [gr _ (by decide) (by decide) (by decide), si₈],
    edi, sv, fr⟩, ?_, Nat.le_refl _, ?_⟩, ?_⟩
  · rw [m₁₁, ← tl, bytesAt_writeBytes_self' rfl (by omega)]
  · -- `U` and `T`.
    have hU₂ : bytesAt s₂.mem ((up s₀).setWidth 64) H.D = bytesAt s₀.mem ((up s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt f₂' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.u_s.sub_right (save_sub hp)) (by omega)
    have hU : bytesAt s₁₁.mem ((hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D =
        bytesAt s₀.mem ((up s₀).setWidth 64) H.D := by
      rw [m₁₁, bytesAt_writeBytes_sep _ _ dU (by omega), bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega),
        hU₂]
    have hT : bytesAt s₁₁.mem ((tp s₀).setWidth 64) H.D = bytesAt s₀.mem ((tp s₀).setWidth 64) H.D :=
      Memory.frame_bytesAt ((f₂'.mono (rs' := [saveR H.st (scr s₀), ⟨(hv H s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.B⟩])
        (by simp)).trans (fB.mono (by simp))) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.t_s.sub_right (save_sub hp)
        · exact t_blk hp) (by omega)
    rw [hU, hT]
  · rw [z₁₁, g₁₀ _ (by decide), g₉ _ (by decide), di₈, test_z]

omit hp in
/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {m : Mem}
    (hT : bytesAt m ((tp s₀).setWidth 64) H.D = Spec.Pbkdf2.iterate (stepM hO s₀) (nn s₀)
      (bytesAt s₀.mem ((up s₀).setWidth 64) H.D) (bytesAt s₀.mem ((tp s₀).setWidth 64) H.D))
    {k0 : List Byte} (hk : k0.length = hO.hH.SH.H.blockSize)
    (hi : hO.hH.SH.Repr s₀.mem ((key s₀).setWidth 64) (xorPad k0 ipad))
    (ho : hO.hH.SH.Repr s₀.mem ((key s₀).setWidth 64 + BitVec.ofNat 64 hO.hH.SH.stateBytes) (xorPad k0 opad)) :
    bytesAt m ((tp s₀).setWidth 64) hO.hH.SH.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey hO.hH.SH.H k0) (nn s₀) (bytesAt s₀.mem ((up s₀).setWidth 64) hO.hH.SH.digestBytes)
        (bytesAt s₀.mem ((tp s₀).setWidth 64) hO.hH.SH.digestBytes) := by
  have hl := hO.link
  have hB : 0 < H.B := by have := hl.DL; omega
  rw [hl.hB] at hk
  rw [hl.hS, ← hO.sizes.S] at ho
  have li : (xorPad k0 ipad).length = H.B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = H.B := by simp [xorPad, hk]
  have ei := Md.stateAt_of_repr hB li (hl.repr _ _ _ hi)
  have eo := Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)
  rw [hl.hD]
  refine hT.trans (Md.iterate_congr (fun u hu => ?_) (fun u => Md.step_length _ hl.DN _ _ u) _ _ _
    (bytesAt_length _ _ _)).symm
  rw [Md.hmac_step hl hk hu, ei, eo]

theorem epilogue_ok {s : State} (h : Inv hO sc s₀ 0 s) :
    WP isa (.block H.st.restore) s fun s' => abiPreserved s₀ s' ∧ (iterG hO.hH.SH sc).post s₀ s' := by
  obtain ⟨hb, hf, hw, -⟩ := bounds hp
  refine WP.mono (restore_ok H.st h.ebp h.saved (by rw [h.wr]; exact (mem_wr hp).1) (by omega) hp.nw)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm]; exact h.toKR.ret hp⟩, fun k0 hk hi ho' => ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), h.esp]
    · exact hg r (callee_saved r hr he)
  · rw [hm]; exact post_eq hO h.val.symm hk hi ho'

theorem correct : WP isa H.iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterG hO.hH.SH sc).post s₀ s' := by
  unfold Hash.iterate
  refine WP.seq (WP.mono (pro_ok hO hp) fun s₁ ⟨h, hz'⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hO hp h hz') fun s₂ h₂ => epilogue_ok hO hp h₂)

end

end VG.Proof.Pbkdf2.Md.X86.Iterate
