import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `iterate`, correct

Untrusted: everything here is checked by Lean. Each step is two calls of
the compression function on the block in `scratch`, which holds `U` and the
padding of a message of `B + D` bytes: HMAC's inner hash of `U` is the
compression of the key's inner hash value (the hash of `K₀ ⊕ ipad`) with
that block (`HashOK.hmac_step`), and the outer hash likewise.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_ save restore saved compressAt)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64 (iterG)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_writeBytes_sep bytesAt_length bytesAt_getD'
  bytesAt_writeBytes_self xorPad_length writeBytes_at)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take bytesAt_writeBytes_self' sub_of_off sub_of_self
  InRegions.right')
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

/-! ## A step of HMAC, as two compressions -/

namespace HashOK

variable {H : Hash} (hH : HashOK H)

/-- The padding of a message of `B + D` bytes, after its last `D` bytes. -/
def padD : List Byte :=
  [0x80] ++ List.replicate (H.P.B - H.P.L - 1 - H.D) 0 ++ hH.md.lenBytes (H.P.B + H.D)

theorem padD_length : hH.padD.length = H.P.B - H.D := by
  have := hH.hDL
  simp only [padD, List.length_append, List.length_singleton, List.length_replicate, hH.md.lenBytes_length]
  omega

/-- The block made of `D` bytes `x` and the padding. -/
def blk (x : List Byte) : hH.md.Blk := hH.md.parse fun t => (x ++ hH.padD).getD t 0

/-- The digest of `h` compressed with the block of `x`. -/
def half (h : hH.md.HV) (x : List Byte) : List Byte := (hH.md.digest (hH.md.compress h (hH.blk x))).take H.D

theorem half_length (h : hH.md.HV) (x : List Byte) : (hH.half h x).length = H.D := by
  simp only [half, List.length_take, hH.md.digest_length]; have := hH.hDN; omega

/-- The hash of a block followed by `D` bytes: one more compression. -/
theorem hash_step {p x : List Byte} (hp : p.length = H.P.B) (hx : x.length = H.D) :
    hH.md.hash hH.iv (p ++ x) = hH.md.digest (hH.md.compress (hH.md.compressList hH.iv p 1) (hH.blk x)) := by
  have hB := hH.B_pos; have hDL := hH.hDL
  have hl : (p ++ x).length = H.P.B + H.D := by rw [List.length_append, hp, hx]
  have hmod : (p ++ x).length % H.P.B = H.D := by
    rw [hl, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (p ++ x).length / H.P.B = 1 := by
    rw [hl, Nat.add_div_left _ hB, Nat.div_eq_of_lt (by omega)]
  rw [hH.md.hash_one hB (by rw [hmod]; omega), hdiv, hH.md.compressList_append (by rw [hp, Nat.mul_one]),
    hmod, hl]
  have hr : Md.rest H.P.B (p ++ x) = x := by
    show (p ++ x).drop (H.P.B * ((p ++ x).length / H.P.B)) = x
    rw [hdiv, Nat.mul_one, ← hp, List.drop_left]
  rw [hr]
  refine congrArg hH.md.digest (congrArg (hH.md.compress _) (hH.md.parse_congr fun k _ => ?_))
  simp only [padD, List.append_assoc]

/-- The hash value a state representing a block holds. -/
theorem state_of_repr {mem : Mem} {q : Addr} {p : List Byte} (hp : p.length = H.P.B)
    (h : hH.SH.Repr mem q p) : hH.md.stateAt mem q = hH.md.compressList hH.iv p 1 := by
  have := ((hH.repr _ _ _).1 h).1
  rwa [hp, Nat.div_self hH.B_pos] at this

/-- A step of PBKDF2: HMAC with the key `K₀`, as two compressions of the
hash values of `K₀ ⊕ ipad` and `K₀ ⊕ opad`. -/
theorem hmac_step {k0 u : List Byte} (hk : k0.length = H.P.B) (hu : u.length = H.D) :
    hmacBlockKey hH.SH.H k0 u = hH.half (hH.md.compressList hH.iv (xorPad k0 opad) 1)
      (hH.half (hH.md.compressList hH.iv (xorPad k0 ipad) 1) u) := by
  simp only [hmacBlockKey, hH.hash]
  rw [hash_step hH (by rw [xorPad_length, hk]) hu, hash_step hH (by rw [xorPad_length, hk]) (by
    rw [List.length_take, hH.md.digest_length]; have := hH.hDN; omega)]
  rfl

end HashOK

/-! ## The precondition and the parts of `scratch` -/

variable {H : Hash} (hH : HashOK H)

section
variable (s₀ : State)

abbrev key : Addr := s₀.gpr .rdi
abbrev up : Addr := s₀.gpr .rsi
abbrev tp : Addr := s₀.gpr .rcx
abbrev scr : Addr := s₀.gpr .r8
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .rdx).setWidth 32).toNat
abbrev keyR : Region := ⟨key s₀, 2 * H.S⟩
abbrev uR : Region := ⟨up s₀, H.D⟩
abbrev tR : Region := ⟨tp s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, 8 * H.W⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- A part of `scratch`. -/
abbrev sR (o n : Nat) : Region := ⟨scr s₀ + BitVec.ofNat 64 o, n⟩
/-- The hash value being compressed, and the block. -/
abbrev ST : Addr := scr s₀ + BitVec.ofNat 64 H.stO
abbrev BL : Addr := scr s₀ + BitVec.ofNat 64 H.blkO
/-- Where our caller's registers are saved. -/
abbrev saveR : Region := sR s₀ H.P.so 48

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR (H := H) s₀, uR (H := H) s₀]
  wr : s₀.wr = [tR (H := H) s₀, scR (H := H) s₀]
  k_t : (keyR (H := H) s₀).Disjoint (tR (H := H) s₀)
  k_s : (keyR (H := H) s₀).Disjoint (scR (H := H) s₀)
  u_t : (uR (H := H) s₀).Disjoint (tR (H := H) s₀)
  u_s : (uR (H := H) s₀).Disjoint (scR (H := H) s₀)
  t_s : (tR (H := H) s₀).Disjoint (scR (H := H) s₀)
  ret_k : (retR s₀).Disjoint (keyR (H := H) s₀)
  ret_u : (retR s₀).Disjoint (uR (H := H) s₀)
  ret_t : (retR s₀).Disjoint (tR (H := H) s₀)
  ret_s : (retR s₀).Disjoint (scR (H := H) s₀)
  stk_k : (stkR s₀).Disjoint (keyR (H := H) s₀)
  stk_u : (stkR s₀).Disjoint (uR (H := H) s₀)
  stk_t : (stkR s₀).Disjoint (tR (H := H) s₀)
  stk_s : (stkR s₀).Disjoint (scR (H := H) s₀)
  knw : (key s₀).toNat + 2 * H.S ≤ 2 ^ 64
  nw : (scr s₀).toNat + 8 * H.W ≤ 2 ^ 64

theorem pre_of {s₀ : State} (h : (iterG hH.SH H.W).pre s₀) : Pre (H := H) s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- The sizes, as facts about natural numbers. -/
structure Sizes (H : Hash) : Prop where
  B : H.P.B = 64 ∨ H.P.B = 128
  N : 0 < H.P.N ∧ H.P.N ≤ 64
  L : 0 < H.P.L ∧ H.P.L ≤ 16
  D : 0 < H.D ∧ H.D ≤ H.P.N ∧ H.D % 4 = 0 ∧ H.D + H.P.L + 4 ≤ H.P.B
  N4 : H.P.N % 4 = 0
  L4 : H.P.L % 4 = 0
  NL : H.P.N + H.P.L ≤ H.P.B
  so : H.P.so % 8 = 0 ∧ H.P.so ≤ 1024
  fits : H.P.so + 48 + H.P.N + H.P.B ≤ 8 * H.W
  W : H.W ≤ 256

theorem HashOK.sizes (hH : HashOK H) : Sizes H :=
  ⟨hH.dims.B, hH.dims.N, hH.dims.L, ⟨hH.hD0, hH.hDN, hH.hD4, hH.hDL⟩, hH.hN4, hH.hL4, hH.hNL,
    ⟨hH.hso.1, hH.dims.so⟩, hH.fits, hH.hW⟩

section
variable {s₀ : State}

theorem off_sub {o n : Nat} (h : o + n ≤ 8 * H.W) : Region.Sub (sR s₀ o n) (scR (H := H) s₀) :=
  Offset.sub_base _ h

theorem part_disj (hz : Sizes H) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 8 * H.W)
    (hb : b + n ≤ 8 * H.W) : Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := hz.W; exact Offset.disjoint _ h (by omega) (by omega)

theorem low_disj (hz : Sizes H) {b n : Nat} (hb : H.P.so ≤ b) (hbn : b + n ≤ 8 * H.W) :
    Region.Disjoint (sR s₀ b n) ⟨scr s₀, H.P.so⟩ := by
  have := hz.W; exact Offset.disjoint_base _ hb (by omega)

theorem in_sc (hp : Pre (H := H) s₀) (hz : Sizes H) {s : State} (hwr : s.wr = s₀.wr) {o n : Nat}
    (h : o + n ≤ 8 * H.W) : InRegions s.wr (scr s₀ + BitVec.ofNat 64 o) n := by
  have := hz.W
  exact ⟨scR (H := H) s₀, by rw [hwr, hp.wr]; simp, Offset.contains_base _ h (by omega)⟩

end

/-! ## The block's memory -/

theorem contains_pre {b : Addr} {n k : Nat} (h : n ≤ k) : (⟨b, k⟩ : Region).Contains b n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- What the code writes over the block's padding after writing the digest
(`N` bytes) there: the padding's first `N - D` bytes. -/
def fx (H : Hash) : List Byte := if H.D < H.P.N then (0x80 : Byte) :: List.replicate (H.P.N - H.D - 1) 0 else []

theorem fx_length : (fx H).length = H.P.N - H.D := by
  unfold fx; split <;> simp <;> omega

theorem Sizes.dims (hz : Sizes H) : Dims H.P := ⟨hz.B, hz.N, hz.L, hz.so.2⟩

theorem Sizes.B_le (hz : Sizes H) : H.P.B ≤ 128 := by rcases hz.B with h | h <;> omega

/-- The block, from its bytes. -/
theorem blockAt_eq {m : Mem} {p : Addr} (hpad : bytesAt m (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.padD) :
    hH.md.blockAt m p = hH.blk (bytesAt m p H.D) := by
  have hz := hH.sizes
  refine hH.md.parse_congr fun k hk => ?_
  rw [← hpad, ← bytesAt_add, show H.D + (H.P.B - H.D) = H.P.B by have := hz.D; omega, bytesAt_getD' _ _ hk]

/-- The digest and the fix over the block leave the digest's first `D` bytes
and the padding. -/
theorem outFix_mem {m : Mem} {p : Addr} {dig : List Byte} (hdig : dig.length = H.P.N)
    (hpad : bytesAt m (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.padD) :
    bytesAt (writeBytes (writeBytes m p dig) (p + BitVec.ofNat 64 H.D) (fx H)) p H.D = dig.take H.D ∧
    bytesAt (writeBytes (writeBytes m p dig) (p + BitVec.ofNat 64 H.D) (fx H)) (p + BitVec.ofNat 64 H.D)
      (H.P.B - H.D) = hH.padD := by
  have hz := hH.sizes
  have := hz.D; have := hz.NL; have := hz.B_le; have := hz.N
  have hfl := fx_length (H := H)
  refine ⟨?_, ?_⟩
  · rw [bytesAt_writeBytes_sep _ _ (by rw [hfl]; exact Offset.sep_base p (Nat.le_refl _) (by omega)) (by omega),
      bytesAt_take _ _ (show H.D ≤ H.P.N by omega), bytesAt_writeBytes_self' hdig (by omega)]
  · by_cases hlt : H.D < H.P.N
    · have e₁ : bytesAt m (p + BitVec.ofNat 64 H.D) (H.P.B - H.D) =
          bytesAt m (p + BitVec.ofNat 64 H.D) (H.P.N - H.D) ++ bytesAt m (p + BitVec.ofNat 64 H.P.N) (H.P.B - H.P.N) := by
        rw [show H.P.B - H.D = (H.P.N - H.D) + (H.P.B - H.P.N) by omega, bytesAt_add, add_ofNat,
          show H.D + (H.P.N - H.D) = H.P.N by omega]
      have hdrop : bytesAt m (p + BitVec.ofNat 64 H.P.N) (H.P.B - H.P.N) = hH.padD.drop (H.P.N - H.D) := by
        rw [← hpad, e₁, List.drop_left' (bytesAt_length _ _ _)]
      have htake : hH.padD.take (H.P.N - H.D) = fx H := by
        have e : hH.padD = 0x80 :: (List.replicate (H.P.B - H.P.L - 1 - H.D) 0 ++ hH.md.lenBytes (H.P.B + H.D)) := by
          simp [HashOK.padD]
        rw [e, show H.P.N - H.D = (H.P.N - H.D - 1) + 1 by omega, List.take_succ_cons,
          List.take_append_of_le_length (by simp; omega), List.take_replicate, Nat.min_eq_left (by omega)]
        simp [fx, hlt]
      rw [show H.P.B - H.D = H.P.N - H.D + (H.P.B - H.P.N) by omega, bytesAt_add,
        bytesAt_writeBytes_self' hfl (by omega), add_ofNat, show H.D + (H.P.N - H.D) = H.P.N by omega,
        bytesAt_writeBytes_sep _ _ (by rw [hfl]; exact Offset.sep p (Or.inr (by omega)) (by omega) (by omega))
          (by omega),
        bytesAt_writeBytes_sep _ _ (by
          rw [hdig]; exact fun x h₁ h₂ => Offset.sep_base p (Nat.le_refl _) (by omega) x h₂ h₁) (by omega),
        hdrop, ← htake, List.take_append_drop]
    · have e : H.D = H.P.N := by omega
      rw [show fx H = [] by simp [fx, hlt], writeBytes_nil,
        bytesAt_writeBytes_sep _ _ (by
          rw [hdig]; exact fun x h₁ h₂ => Offset.sep_base p (Nat.le_of_eq e.symm) (by omega) x h₂ h₁) (by omega),
        hpad]

/-! ## What the pieces keep -/

/-- The registers and memory kept from the prologue on, with `m` steps left:
everything written is in `T`, `scratch` or the stack. -/
structure KR (s₀ : State) (m : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = ST (H := H) s₀
  rbp : s.gpr .rbp = BL (H := H) s₀
  r12 : s.gpr .r12 = key s₀
  r13 : s.gpr .r13 = BitVec.ofNat 64 m
  r14 : s.gpr .r14 = tp s₀
  r15 : s.gpr .r15 = scr s₀
  saved : Saved H.P s₀ .r8 s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64
  frame : Frame [tR (H := H) s₀, scR (H := H) s₀, stkR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]

theorem kregs_saved {r : Reg} (h : r ∈ kregs) : r ∈ calleeSaved := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]

theorem kregs_ne {r : Reg} (h : r ∈ kregs) : r ≠ .rax := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem saved_frame (hz : Sizes H) {s₀ : State} {m m' : Mem} (h : Saved H.P s₀ .r8 m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (saveR (H := H) s₀).Disjoint r) : Saved H.P s₀ .r8 m' := by
  intro q hq
  have ho := saved_offset hz.dims hq
  rw [← h q hq, ofInt_natCast]
  exact hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 q.2, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub _ ho.1 ho.2)) (by decide)

theorem stk_ret {s₀ : State} : (stkR s₀).Disjoint (retR s₀) :=
  fun x h₁ h₂ => Offset.base_disjoint_below (s₀.gpr .rsp) (n := 16) (k := 8) (by omega) x h₂ h₁

section
variable {s₀ : State} (hp : Pre (H := H) s₀) (hz : Sizes H)

include hp hz

theorem KR.keep {m : Nat} {s s' : State} (h : KR (H := H) s₀ m s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR (H := H) s₀).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [tR (H := H) s₀, scR (H := H) s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) s₀ m s' := by
  have hr : ∀ r ∈ rs, (retR s₀).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hs'⟩ := hsub r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hp.ret_t.sub_right hs'
    · exact hp.ret_s.sub_right hs'
    · exact (stk_ret (s₀ := s₀)).symm.sub_right hs'
  exact ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.rbp, (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13,
    (hg _ (by simp)).trans h.r14, (hg _ (by simp)).trans h.r15, saved_frame hz h.saved hf hs,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret,
    h.frame.trans (hf.sub hsub)⟩

/-- A write into a part of `scratch` after the saved registers keeps `KR`. -/
theorem KR.write {m : Nat} {s s' : State} (h : KR (H := H) s₀ m s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {o n : Nat} (ho : H.P.so + 48 ≤ o) (hon : o + n ≤ 8 * H.W)
    (hf : Frame [sR s₀ o n] s.mem s'.mem) : KR (H := H) s₀ m s' :=
  h.keep hp hz hrd hwr hg hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl ho) (by have := hz.fits; omega) hon)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR (H := H) s₀, by simp, off_sub hon⟩)

omit hp hz in
theorem KR.withM {m m' : Nat} {s : State} (h : KR (H := H) s₀ m s) (hr : s.gpr .r13 = BitVec.ofNat 64 m') :
    KR (H := H) s₀ m' s := { h with r13 := hr }

/-! ## The pieces of a step -/

theorem load_ok {m : Nat} {s : State} (hk : KR (H := H) s₀ m s) {o : Nat} (ho : o + H.P.N ≤ 2 * H.S)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', KR (H := H) s₀ m s' → s'.gpr .rsi = BL (H := H) s₀ →
      Frame [sR s₀ H.stO H.P.N] s.mem s'.mem →
      hH.md.stateAt s'.mem (ST (H := H) s₀) = hH.md.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (H.load o ++ rest)) s Q := by
  have := hz.N; have := hz.N4; have := hz.fits; have := hz.W; have hkn := hp.knw
  have hS : H.S = H.P.N + H.P.B := rfl
  have hso : H.stO = H.P.so + 48 := rfl
  have e4 : 4 * (H.P.N / 4) = H.P.N := by omega
  have est : ∀ j, ST (H := H) s₀ + BitVec.ofNat 64 0 + BitVec.ofNat 64 j =
      scr s₀ + BitVec.ofNat 64 (H.stO + j) := fun j => by simp only [add_ofNat, Nat.add_zero]
  unfold Hash.load
  rw [List.append_assoc]
  refine copy32_ok (src := .r12) (dst := .rbx) (by decide) (by decide) o 0 (H.P.N / 4) _ s Q
    (fun j hj => by
      rw [hk.r12, hk.rd, hp.rd, add_ofNat]
      exact ⟨keyR (H := H) s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by
      rw [hk.rbx, est]; exact in_sc hp hz hk.wr (by omega))
    (by
      rw [hk.r12, hk.rbx, e4, add_ofNat, Nat.add_zero]
      exact hp.k_s.sep (Offset.contains_base _ (by omega) (by omega))
        (Offset.contains_base _ (by omega) (by omega)))
    (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  rw [hk.r12, hk.rbx, e4, add_ofNat, Nat.add_zero] at m₁
  refine wp_mov fun s₂ u₂ _ _ => ?_
  have fr : Frame [sR s₀ H.stO H.P.N] s.mem s₂.mem := by
    rw [u₂.mem, m₁]
    exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine k s₂ (hk.write hp hz (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁])
      (fun r hr => by rw [u₂.other r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g₁ r (kregs_ne hr)])
      (Nat.le_refl _) (by omega) fr)
    (by rw [u₂.gpr, g₁ _ (by decide), hk.rbp]) fr ?_
  refine hH.reloc _ _ _ _ fun i hi => ?_
  rw [u₂.mem, m₁, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi]
  have ksub : Region.Sub ⟨key s₀ + BitVec.ofNat 64 o, H.P.N⟩ (keyR (H := H) s₀) := Offset.sub_base _ ho
  refine hk.frame.bytes (R := ⟨key s₀ + BitVec.ofNat 64 o, H.P.N⟩) ?_ (by show H.P.N ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.k_t.sub_left ksub
  · exact hp.k_s.sub_left ksub
  · exact hp.stk_k.symm.sub_left ksub

/-- The compression function's arguments, with the block in `rsi`. -/
theorem kr_call {m : Nat} {s : State} (hk : KR (H := H) s₀ m s) (hsi : s.gpr .rsi = BL (H := H) s₀) :
    CallOk H.P s (ST (H := H) s₀) (scr s₀) (BL (H := H) s₀) := by
  have := hz.N; have := hz.fits; have := hz.W; have := hz.B_le; have := hz.so
  have hso : H.stO = H.P.so + 48 := rfl
  have hbl : H.blkO = H.P.so + 48 + H.P.N := rfl
  have sR' : scR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hk.wr, hp.wr]; simp
  have sW : scR (H := H) s₀ ∈ s.wr := by rw [hk.wr, hp.wr]; simp
  have b8 : Region.Sub (below (s₀.gpr .rsp) 8) (stkR s₀) := below_sub (by omega) (by omega)
  exact ⟨hk.rbx, hk.r15, hsi, low_disj hz (by omega) (by omega),
      part_disj hz (Or.inr (by omega)) (by omega) (by omega), low_disj hz (by omega) (by omega),
      by rw [hk.rsp]; exact (hp.stk_s.sub_left b8).sub_right (off_sub (by omega)),
      by rw [hk.rsp]; exact (hp.stk_s.sub_left b8).sub_right (Region.sub_prefix (by omega)),
      by rw [hk.rsp]; exact (hp.stk_s.sub_left b8).sub_right (off_sub (by omega)),
      Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_of_off sR' (by omega)
        · exact sub_of_off sR' (by omega)
        · exact sub_of_self sR' (by show H.P.so ≤ 8 * H.W; omega),
      Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact sub_of_off sW (by omega)
        · exact sub_of_self sW (by show H.P.so ≤ 8 * H.W; omega)⟩

theorem cmp_ok {m : Nat} {s : State} (hk : KR (H := H) s₀ m s) (hsi : s.gpr .rsi = BL (H := H) s₀) :
    WP isa (compressAt H.compN H.compC) s fun s' => KR (H := H) s₀ m s' ∧
      Frame [sR s₀ H.stO H.P.N, ⟨scr s₀, H.P.so⟩, below (s₀.gpr .rsp) 8] s.mem s'.mem ∧
      hH.md.stateAt s'.mem (ST (H := H) s₀) =
        hH.md.compress (hH.md.stateAt s.mem (ST (H := H) s₀)) (hH.md.blockAt s.mem (BL (H := H) s₀)) := by
  have := hz.N; have := hz.fits; have := hz.W; have := hz.B_le; have := hz.so
  have hso : H.stO = H.P.so + 48 := rfl
  have hbl : H.blkO = H.P.so + 48 + H.P.N := rfl
  have b8 : Region.Sub (below (s₀.gpr .rsp) 8) (stkR s₀) := below_sub (by omega) (by omega)
  refine compressAt_ok hH.md hH.comp (st := ST (H := H) s₀) (scr := scr s₀) (src := BL (H := H) s₀)
    (kr_call hp hz hk hsi)
    (by omega) (by omega) fun s' hrd hwr hcs hf hst _ _ => ?_
  rw [hk.rsp] at hf
  refine ⟨hk.keep hp hz hrd hwr (fun r hr => hcs r (kregs_saved hr)) hf (fun r hr => ?_) (fun r hr => ?_), hf, hst⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
    · exact low_disj hz (Nat.le_refl _) (by omega)
    · exact ((hp.stk_s.sub_left b8).sub_right (off_sub (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR (H := H) s₀, by simp, off_sub (by omega)⟩
    · exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, b8⟩

theorem outFix_ok {m : Nat} {s : State} (hk : KR (H := H) s₀ m s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', KR (H := H) s₀ m s' → Frame [sR s₀ H.blkO H.P.B] s.mem s'.mem →
      s'.mem = writeBytes (writeBytes s.mem (BL (H := H) s₀) (hH.md.digest (hH.md.stateAt s.mem (ST (H := H) s₀))))
        (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (fx H) → WP isa (.block rest) s' Q) :
    WP isa (.block (H.P.out ++ H.fix ++ rest)) s Q := by
  have := hz.N; have := hz.fits; have := hz.W; have := hz.B_le; have := hz.so; have := hz.D; have := hz.NL
  have := hz.N4
  have hso : H.stO = H.P.so + 48 := rfl
  have hbl : H.blkO = H.P.so + 48 + H.P.N := rfl
  have hdl := hH.md.digest_length (hH.md.stateAt s.mem (ST (H := H) s₀))
  have hfl := fx_length (H := H)
  have bw : ∀ {t : State}, t.wr = s₀.wr → ∀ j n, j + n ≤ H.P.B →
      InRegions t.wr (BL (H := H) s₀ + BitVec.ofNat 64 j) n := fun hw j n hj => by
    rw [add_ofNat]; exact in_sc hp hz hw (by omega)
  have fr : ∀ m₀ : Mem, Frame [sR s₀ H.blkO H.P.B] m₀ (writeBytes (writeBytes m₀ (BL (H := H) s₀)
      (hH.md.digest (hH.md.stateAt s.mem (ST (H := H) s₀)))) (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (fx H)) :=
    fun m₀ => (writeBytes_frame _ _ _ (by rw [hdl]; exact contains_pre (by omega))).trans
      (writeBytes_frame _ _ _ (by rw [hfl]; exact Offset.contains_base _ (by omega) (by omega)))
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (hH.shape.out s ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  · rw [hk.rbx]; exact InRegions.right' (in_sc hp hz hk.wr (by simp only [hso]; omega))
  · rw [hk.rbp]; simpa using bw hk.wr 0 H.P.N (by omega)
  · rw [hk.rbx, hk.rbp]; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  rw [hk.rbp, hk.rbx] at m₁
  have kr₁ : ∀ {t : State}, (∀ r, r ≠ .rax → t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr →
      t.mem = writeBytes (writeBytes s.mem (BL (H := H) s₀) (hH.md.digest (hH.md.stateAt s.mem (ST (H := H) s₀))))
        (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (fx H) → KR (H := H) s₀ m t := fun g rd wr mt =>
    hk.write hp hz rd wr (fun r hr => g r (kregs_ne hr)) (o := H.blkO) (n := H.P.B) (by omega) (by omega)
      (by rw [mt]; exact fr _)
  unfold Hash.fix
  by_cases hlt : H.D < H.P.N
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hlt)]
    refine padTo_ok H (e := H.P.N) (by omega) (by omega) (by omega)
      (fun j hj₁ hj₂ => by rw [g₁ _ (by decide), hk.rbp, wr₁]; exact bw hk.wr j 4 (by omega))
      fun s₂ g₂ rd₂ wr₂ m₂ => ?_
    have mt : s₂.mem = writeBytes (writeBytes s.mem (BL (H := H) s₀)
        (hH.md.digest (hH.md.stateAt s.mem (ST (H := H) s₀)))) (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (fx H) := by
      rw [m₂, m₁, g₁ _ (by decide), hk.rbp, fx, ite_eq_left_of_eq_true _ _ (eq_true hlt)]
    exact k s₂ (kr₁ (fun r hr => by rw [g₂ r hr, g₁ r hr]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) mt)
      (by rw [mt]; exact fr _) mt
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt), List.nil_append]
    have mt : s₁.mem = writeBytes (writeBytes s.mem (BL (H := H) s₀)
        (hH.md.digest (hH.md.stateAt s.mem (ST (H := H) s₀)))) (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (fx H) := by
      rw [m₁, fx, ite_eq_right_of_eq_false _ _ (eq_false hlt), writeBytes_nil]
    exact k s₁ (kr₁ g₁ rd₁ wr₁ mt) (by rw [mt]; exact fr _) mt

theorem xorDec_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) {s : State} (hk : KR (H := H) s₀ m s) :
    WP isa (.block (H.xor32 ++ [.alu .sub .r13 (.imm 1)])) s fun t => KR (H := H) s₀ (m - 1) t ∧
      t.zf = some (decide (m - 1 = 0)) ∧
      t.mem = writeBytes s.mem (tp s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp s₀) H.D)
        (bytesAt s.mem (BL (H := H) s₀) H.D)) := by
  have := hz.N; have := hz.fits; have := hz.W; have := hz.B_le; have := hz.D
  have hbl : H.blkO = H.P.so + 48 + H.P.N := rfl
  have e4 : 4 * (H.D / 4) = H.D := by omega
  have tW : tR (H := H) s₀ ∈ s.wr := by rw [hk.wr, hp.wr]; simp
  unfold Hash.xor32
  refine xor32_ok (tp := tp s₀) (up := BL (H := H) s₀) (n₀ := H.D / 4) (by
      rw [e4]; exact hp.t_s.sub_right (off_sub (by omega))) (by omega) (H.D / 4) (Nat.le_refl _) _ s _
    hk.r14 hk.rbp
    (fun j hj => by rw [add_ofNat]; exact InRegions.right' (in_sc hp hz hk.wr (by omega)))
    (fun j hj => ⟨_, tW, Offset.contains_base _ (by omega) (by omega)⟩) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  rw [e4] at m₁
  refine wp_subi fun t u z => WP.block_nil ⟨?_, ?_, by rw [u.mem, m₁]⟩
  · have hx : (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp s₀) H.D) (bytesAt s.mem (BL (H := H) s₀) H.D)).length =
        H.D := by rw [xorBytes_len _ _ (by simp [bytesAt_length]), bytesAt_length]
    have k₁ : KR (H := H) s₀ m s₁ := hk.keep hp hz rd₁ wr₁ (fun r hr => g₁ r (kregs_ne hr))
      (rs := [tR (H := H) s₀])
      (by rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hx]; exact Region.contains_self (tp s₀) H.D))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.t_s.sub_right (off_sub (by omega))).symm)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨tR (H := H) s₀, by simp, fun _ h => h⟩)
    exact ⟨by rw [u.rd, k₁.rd], by rw [u.wr, k₁.wr], by rw [u.other _ (by decide), k₁.rsp],
      by rw [u.other _ (by decide), k₁.rbx], by rw [u.other _ (by decide), k₁.rbp],
      by rw [u.other _ (by decide), k₁.r12], by rw [u.gpr, k₁.r13, sx1, ofNat_pred hm],
      by rw [u.other _ (by decide), k₁.r14], by rw [u.other _ (by decide), k₁.r15], u.mem ▸ k₁.saved,
      by rw [u.mem, k₁.ret], u.mem ▸ k₁.frame⟩
  · rw [z, g₁ _ (by decide), hk.r13, sx1, ofNat_pred hm, ofNat_beq_zero (by omega)]

/-! ## One step -/

omit hp hz in
theorem keepB {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR s₀ o n) r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' (scr s₀ + BitVec.ofNat 64 o) n = bytesAt m (scr s₀ + BitVec.ofNat 64 o) n :=
  bytes_keep hf hd hn

/-- The parts of `scratch` after the hash value being compressed are outside what a
load of it and a compression write. -/
theorem dis_cmp {o n : Nat} (ho : H.stO + H.P.N ≤ o) (hon : o + n ≤ 8 * H.W) :
    ∀ r ∈ [sR s₀ H.stO H.P.N, ⟨scr s₀, H.P.so⟩, below (s₀.gpr .rsp) 8], Region.Disjoint (sR s₀ o n) r := by
  have := hz.W; have := hz.N
  have hso : H.stO = H.P.so + 48 := rfl
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact part_disj hz (Or.inr ho) hon (by omega)
  · exact low_disj hz (by omega) hon
  · exact ((hp.stk_s.sub_left (below_sub (by omega) (by omega))).sub_right (off_sub hon)).symm

/-- `T` is outside what everything but `T ← T ⊕ U` writes. -/
theorem dis_t : ∀ r ∈ [sR s₀ H.stO H.P.N, ⟨scr s₀, H.P.so⟩, below (s₀.gpr .rsp) 8, sR s₀ H.blkO H.P.B],
    Region.Disjoint (tR (H := H) s₀) r := by
  have := hz.W; have := hz.N; have := hz.fits
  have hso : H.stO = H.P.so + 48 := rfl
  have hbl : H.blkO = H.P.so + 48 + H.P.N := rfl
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.t_s.sub_right (off_sub (by omega))
  · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
  · exact (hp.stk_t.sub_left (below_sub (by omega) (by omega))).symm
  · exact hp.t_s.sub_right (off_sub (by omega))

/-- The key's states represent `K₀ ⊕ ipad` and `K₀ ⊕ opad`. -/
def KeyOK (s₀ : State) (k0 : List Byte) : Prop :=
  k0.length = H.P.B ∧ hH.SH.Repr s₀.mem (key s₀) (xorPad k0 ipad) ∧
    hH.SH.Repr s₀.mem (key s₀ + BitVec.ofNat 64 H.S) (xorPad k0 opad)

/-- With `m` steps left, what is left to compute is the rest of the whole;
the block holds `U` and the padding. -/
structure Inv (s₀ : State) (m : Nat) (s : State) : Prop where
  kr : KR (H := H) s₀ m s
  pad : bytesAt s.mem (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.padD
  it : ∀ k0, KeyOK hH s₀ k0 →
    Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (nn s₀) (bytesAt s₀.mem (up s₀) H.D)
        (bytesAt s₀.mem (tp s₀) H.D) =
      Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) m (bytesAt s.mem (BL (H := H) s₀) H.D)
        (bytesAt s.mem (tp s₀) H.D)

theorem body_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) {s : State} (h : Inv hH s₀ m s) :
    WP isa H.body s fun t => Inv hH s₀ (m - 1) t ∧ t.zf = some (decide (m - 1 = 0)) := by
  have := hz.W; have := hz.N; have := hz.fits; have := hz.D; have := hz.B_le
  have hso : H.stO = H.P.so + 48 := rfl
  have hbl : H.blkO = H.P.so + 48 + H.P.N := rfl
  have hS : H.S = H.P.N + H.P.B := rfl
  have eB : ∀ o : Nat, BL (H := H) s₀ + BitVec.ofNat 64 o = scr s₀ + BitVec.ofNat 64 (H.blkO + o) :=
    fun o => add_ofNat _ _ _
  have dP := dis_cmp hp hz (o := H.blkO + H.D) (n := H.P.B - H.D) (by omega) (by omega)
  have dU := dis_cmp hp hz (o := H.blkO) (n := H.D) (by omega) (by omega)
  have dT := dis_t hp hz
  have hBn : H.P.B - H.D ≤ 2 ^ 64 := by omega
  have hDn : H.D ≤ 2 ^ 64 := by omega
  -- The pieces.
  unfold Hash.body
  refine WP.seq ?_
  rw [← List.append_nil (H.load 0)]
  refine load_ok hH hp hz h.kr (o := 0) (by omega) fun s₁ k₁ si₁ f₁ st₁ => WP.block_nil ?_
  refine WP.seq (WP.mono (cmp_ok hH hp hz k₁ si₁) fun c₁ ⟨kc₁, fc₁, sc₁⟩ => ?_)
  refine WP.seq ?_
  refine outFix_ok hH hp hz kc₁ fun o₁ ko₁ fo₁ mo₁ => ?_
  rw [← List.append_nil (H.load H.S)]
  refine load_ok hH hp hz ko₁ (o := H.S) (by omega) fun l₂ kl₂ si₂ fl₂ stl₂ => WP.block_nil ?_
  refine WP.seq (WP.mono (cmp_ok hH hp hz kl₂ si₂) fun c₂ ⟨kc₂, fc₂, sc₂⟩ => ?_)
  rw [List.append_assoc (H.P.out ++ H.fix)]
  refine outFix_ok hH hp hz kc₂ fun o₂ ko₂ fo₂ mo₂ => ?_
  refine WP.mono (xorDec_ok hp hz hm hn ko₂) fun t ⟨kt, zt, mt⟩ => ?_
  -- The block at each point.
  have p₁ : bytesAt s₁.mem (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.padD := by
    rw [eB, keepB f₁ (fun r hr => dP r (by simp at hr; simp [hr])) hBn, ← eB]; exact h.pad
  have u₁ : bytesAt s₁.mem (BL (H := H) s₀) H.D = bytesAt s.mem (BL (H := H) s₀) H.D :=
    keepB f₁ (fun r hr => dU r (by simp at hr; simp [hr])) hDn
  have pc₁ : bytesAt c₁.mem (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.padD := by
    rw [eB, keepB fc₁ dP hBn, ← eB]; exact p₁
  obtain ⟨uo₁, po₁⟩ := outFix_mem hH (hH.md.digest_length _) pc₁
  rw [← mo₁] at uo₁ po₁
  have pl₂ : bytesAt l₂.mem (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.padD := by
    rw [eB, keepB fl₂ (fun r hr => dP r (by simp at hr; simp [hr])) hBn, ← eB]; exact po₁
  have ul₂ : bytesAt l₂.mem (BL (H := H) s₀) H.D = bytesAt o₁.mem (BL (H := H) s₀) H.D :=
    keepB fl₂ (fun r hr => dU r (by simp at hr; simp [hr])) hDn
  have pc₂ : bytesAt c₂.mem (BL (H := H) s₀ + BitVec.ofNat 64 H.D) (H.P.B - H.D) = hH.padD := by
    rw [eB, keepB fc₂ dP hBn, ← eB]; exact pl₂
  obtain ⟨uo₂, po₂⟩ := outFix_mem hH (hH.md.digest_length _) pc₂
  rw [← mo₂] at uo₂ po₂
  -- The hash values.
  have e₀ : key s₀ + BitVec.ofNat 64 0 = key s₀ := BitVec.add_zero _
  rw [e₀] at st₁
  have d₁ : bytesAt o₁.mem (BL (H := H) s₀) H.D =
      hH.half (hH.md.stateAt s₀.mem (key s₀)) (bytesAt s.mem (BL (H := H) s₀) H.D) := by
    rw [uo₁, sc₁, st₁, blockAt_eq hH p₁, u₁]; rfl
  have d₂ : bytesAt o₂.mem (BL (H := H) s₀) H.D =
      hH.half (hH.md.stateAt s₀.mem (key s₀ + BitVec.ofNat 64 H.S)) (bytesAt o₁.mem (BL (H := H) s₀) H.D) := by
    rw [uo₂, sc₂, stl₂, blockAt_eq hH pl₂, ul₂]; rfl
  -- `T ← T ⊕ U`.
  have hx : (Spec.Pbkdf2.xorBytes (bytesAt o₂.mem (tp s₀) H.D) (bytesAt o₂.mem (BL (H := H) s₀) H.D)).length =
      H.D := by rw [xorBytes_len _ _ (by simp [bytesAt_length]), bytesAt_length]
  have ft : Frame [tR (H := H) s₀] o₂.mem t.mem := by
    rw [mt]; exact writeBytes_frame _ _ _ (by rw [hx]; exact Region.contains_self (tp s₀) H.D)
  have dtB : ∀ o n, H.blkO ≤ o → o + n ≤ 8 * H.W → ∀ r ∈ [tR (H := H) s₀], Region.Disjoint (sR s₀ o n) r :=
    fun o n h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.t_s.sub_right (off_sub h₂)).symm
  refine ⟨⟨kt, ?_, fun k0 hk => ?_⟩, zt⟩
  · rw [eB, keepB ft (dtB _ _ (by omega) (by omega)) hBn, ← eB]; exact po₂
  · obtain ⟨hl0, hrI, hrO⟩ := hk
    have T : bytesAt o₂.mem (tp s₀) H.D = bytesAt s.mem (tp s₀) H.D := by
      have t₁ := bytes_keep f₁ (fun r hr => dT r (by simp at hr; simp [hr])) hDn
      have t₂ := bytes_keep fc₁ (fun r hr => dT r (by simp at hr; rcases hr with h | h | h <;> simp [h])) hDn
      have t₃ := bytes_keep fo₁ (fun r hr => dT r (by simp at hr; simp [hr])) hDn
      have t₄ := bytes_keep fl₂ (fun r hr => dT r (by simp at hr; simp [hr])) hDn
      have t₅ := bytes_keep fc₂ (fun r hr => dT r (by simp at hr; rcases hr with h | h | h <;> simp [h])) hDn
      have t₆ := bytes_keep fo₂ (fun r hr => dT r (by simp at hr; simp [hr])) hDn
      rw [t₆, t₅, t₄, t₃, t₂, t₁]
    have Ut : bytesAt t.mem (BL (H := H) s₀) H.D = bytesAt o₂.mem (BL (H := H) s₀) H.D :=
      keepB ft (dtB _ _ (by omega) (by omega)) hDn
    have Tt : bytesAt t.mem (tp s₀) H.D = Spec.Pbkdf2.xorBytes (bytesAt o₂.mem (tp s₀) H.D)
        (bytesAt o₂.mem (BL (H := H) s₀) H.D) := by
      rw [mt]; exact bytesAt_writeBytes_self' hx (by omega)
    have step : hmacBlockKey hH.SH.H k0 (bytesAt s.mem (BL (H := H) s₀) H.D) = bytesAt o₂.mem (BL (H := H) s₀) H.D := by
      rw [hH.hmac_step hl0 (bytesAt_length _ _ _), d₂, d₁, hH.state_of_repr (by rw [xorPad_length, hl0]) hrI,
        hH.state_of_repr (by rw [xorPad_length, hl0]) hrO]
    rw [h.it k0 ⟨hl0, hrI, hrO⟩, show m = (m - 1) + 1 by omega, Ut, Tt, T, ← step]
    rfl

/-! ## The prologue, the loop and the epilogue -/

omit hp hz in
theorem wp_mov32r {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

omit hp hz in
theorem zx32 (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

omit hz in
omit hp in
theorem nn_lt : nn s₀ < 2 ^ 32 := ((s₀.gpr .rdx).setWidth 32).isLt

/-- Saving our caller's registers in `scratch`. -/
theorem save_ok {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s₀.gpr → s'.rd = s₀.rd → s'.wr = s₀.wr → s'.mem = saveMem H.P s₀ .r8 →
      WP isa (.block rest) s' Q) :
    WP isa (.block (save H.P .r8 ++ rest)) s₀ Q := by
  have := hz.so; have := hz.fits; have := hz.W
  have o : ∀ d : Nat, d + 8 ≤ H.P.so + 48 → InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR (H := H) s₀, by simp [hp.wr], contains_offset' (by omega) (by omega)⟩
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((H.P.so : Nat) : Int)) rfl (o _ (by omega))
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((H.P.so + 8 : Nat) : Int)) (by simp only [State.ea, at_, g₁])
    (by rw [wr₁]; exact o _ (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((H.P.so + 16 : Nat) : Int))
    (by simp only [State.ea, at_, g₂, g₁]) (by rw [wr₂, wr₁]; exact o _ (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((H.P.so + 24 : Nat) : Int))
    (by simp only [State.ea, at_, g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁]; exact o _ (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((H.P.so + 32 : Nat) : Int))
    (by simp only [State.ea, at_, g₄, g₃, g₂, g₁])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((H.P.so + 40 : Nat) : Int))
    (by simp only [State.ea, at_, g₅, g₄, g₃, g₂, g₁])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  exact k s₆ (by rw [g₆, g₅, g₄, g₃, g₂, g₁]) (by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁])
    (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁])
    (by rw [m₆, m₅, m₄, m₃, m₂, m₁]; simp only [saveMem, g₅, g₄, g₃, g₂, g₁])

set_option simprocs false in
/-- Loading them back, with `scratch` in `r15` (loaded last). -/
theorem restore_ok {s : State} (h15 : s.gpr .r15 = scr s₀) (hs : Saved H.P s₀ .r8 s.mem)
    (hwr : s.wr = s₀.wr) :
    WP isa (.block (restore H.P)) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have := hz.so; have := hz.fits; have := hz.W
  have i : ∀ d : Nat, d + 8 ≤ H.P.so + 48 →
      InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 := fun d hd => by
    rw [hwr]
    exact InRegions.right' ⟨scR (H := H) s₀, by simp [hp.wr], contains_offset' (by omega) (by omega)⟩
  have i0 := i H.P.so (by omega); have i1 := i (H.P.so + 8) (by omega); have i2 := i (H.P.so + 16) (by omega)
  have i3 := i (H.P.so + 24) (by omega); have i4 := i (H.P.so + 32) (by omega)
  have i5 := i (H.P.so + 40) (by omega)
  have g0 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((H.P.so : Nat) : Int)) 64 = s₀.gpr .rbx :=
    hs (.rbx, H.P.so) (by simp [saved])
  have g1 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((H.P.so + 8 : Nat) : Int)) 64 = s₀.gpr .rbp :=
    hs (.rbp, H.P.so + 8) (by simp [saved])
  have g2 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((H.P.so + 16 : Nat) : Int)) 64 = s₀.gpr .r12 :=
    hs (.r12, H.P.so + 16) (by simp [saved])
  have g3 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((H.P.so + 24 : Nat) : Int)) 64 = s₀.gpr .r13 :=
    hs (.r13, H.P.so + 24) (by simp [saved])
  have g4 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((H.P.so + 32 : Nat) : Int)) 64 = s₀.gpr .r14 :=
    hs (.r14, H.P.so + 32) (by simp [saved])
  have g5 : s.mem.readW (scr s₀ + BitVec.ofInt 64 ((H.P.so + 40 : Nat) : Int)) 64 = s₀.gpr .r15 :=
    hs (.r15, H.P.so + 40) (by simp [saved])
  clear i
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, h15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, fun r hr => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true})
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    simp [h1, h2, h3, h4, h5, h6]

/-- The prologue: the registers saved and set up, `U` and the padding in the
block, and the flags for the loop's first test. -/
theorem pro_ok : WP isa (.block H.iterPrologue) s₀ fun s =>
    Inv hH s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)) := by
  have := hz.W; have := hz.N; have := hz.fits; have := hz.D; have := hz.B_le; have := hz.L; have := hz.L4
  have := hz.so; have := hz.NL; have hn32 := nn_lt (s₀ := s₀)
  have hso : H.stO = H.P.so + 48 := rfl
  have hbl : H.blkO = H.P.so + 48 + H.P.N := rfl
  have hB4 : H.P.B % 4 = 0 := by rcases hz.B with h | h <;> omega
  have z0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  have bw : ∀ {t : State}, t.wr = s₀.wr → ∀ j n, j + n ≤ H.P.B →
      InRegions t.wr (BL (H := H) s₀ + BitVec.ofNat 64 j) n := fun hw j n hj => by
    rw [add_ofNat]; exact in_sc hp hz hw (by omega)
  have bc : ∀ j n, j + n ≤ H.P.B → (sR s₀ H.blkO H.P.B).Contains (BL (H := H) s₀ + BitVec.ofNat 64 j) n :=
    fun j n hj => Offset.contains_base _ hj (by omega)
  have lbl := hH.md.lenBytes_length (H.P.B + H.D)
  have hlen : hH.md.lenOf (BitVec.ofNat 64 (H.P.B + H.D)) = hH.md.lenBytes (H.P.B + H.D) :=
    hH.md.lenOf_eq _ (hH.lenOk _ (by omega))
  unfold Hash.iterPrologue
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine save_ok hp hz fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ => wp_mov fun s₅ u₅ _ _ =>
    wp_addi fun s₆ u₆ => wp_mov32r fun s₇ u₇ => wp_mov fun s₈ u₈ _ _ => ?_
  have oth₈ : ∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r13 → r ≠ .r14 → s₈.gpr r = s₀.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₈.other r h5, u₇.other r h4, u₆.other r h3, u₅.other r h3, u₄.other r h2, u₃.other r h2,
        u₂.other r h1, g₁]
  have r15₈ : s₈.gpr .r15 = scr s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  have rbx₈ : s₈.gpr .rbx = ST (H := H) s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.gpr, u₂.other _ (by decide), g₁, sx_ofNat (by omega)]
  have rbp₈ : s₈.gpr .rbp = BL (H := H) s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁, sx_ofNat (by omega)]
  have r13₈ : s₈.gpr .r13 = BitVec.ofNat 64 (nn s₀) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁, zx32]
  have r14₈ : s₈.gpr .r14 = tp s₀ := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have m₈ : s₈.mem = saveMem H.P s₀ .r8 := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have rsi₈ : s₈.gpr .rsi = up s₀ := oth₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have e4 : 4 * (H.D / 4) = H.D := by omega
  -- `U` into the block.
  refine copy32_ok (src := .rsi) (dst := .rbp) (by decide) (by decide) 0 0 (H.D / 4) _ s₈ _
    (fun j hj => by
      rw [rsi₈, rd₈, hp.rd, z0]
      exact ⟨uR (H := H) s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => by rw [rbp₈, z0]; exact bw wr₈ _ _ (by omega))
    (by
      rw [rsi₈, rbp₈, z0, z0, e4]
      exact hp.u_s.sep (contains_pre (Nat.le_refl _)) (Offset.contains_base _ (by omega) (by omega)))
    (by omega) fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  rw [rsi₈, rbp₈, z0, z0, e4] at m₉
  -- The padding.
  refine padTo_ok H (e := H.P.B - H.P.L) (by omega) (by omega) (by omega)
    (fun j hj₁ hj₂ => by rw [g₉ _ (by decide), rbp₈, wr₉]; exact bw wr₈ j 4 (by omega))
    fun s₁₀ g₁₀ rd₁₀ wr₁₀ m₁₀ => ?_
  rw [g₉ _ (by decide), rbp₈] at m₁₀
  refine wp_mov32i fun s₁₁ u₁₁ _ _ => ?_
  have g₁₁ : ∀ r, r ≠ .rax → r ≠ .r12 → s₁₁.gpr r = s₈.gpr r := fun r h1 h2 => by
    rw [u₁₁.other r h2, g₁₀ r h1, g₉ r h1]
  have eL : ST (H := H) s₀ + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L) =
      BL (H := H) s₀ + BitVec.ofNat 64 (H.P.B - H.P.L) := by
    rw [add_ofNat, add_ofNat, show H.stO + (H.P.N + H.P.B - H.P.L) = H.blkO + (H.P.B - H.P.L) by omega]
  -- The length.
  rw [WP.block_append_iff]
  refine WP.mono (hH.shape.len s₁₁ (by
      rw [g₁₁ _ (by decide) (by decide), rbx₈, eL, u₁₁.wr, wr₁₀, wr₉]; exact bw wr₈ _ _ (by omega)))
    fun s₁₂ ⟨g₁₂, rd₁₂, wr₁₂, m₁₂⟩ => ?_
  rw [g₁₁ _ (by decide) (by decide), rbx₈, eL, u₁₁.gpr, zx_ofNat (by omega), hlen, u₁₁.mem] at m₁₂
  refine wp_mov fun s₁₃ u₁₃ _ _ => wp_test fun s₁₄ g₁₄ m₁₄ rd₁₄ wr₁₄ z₁₄ => WP.block_nil ?_
  have gr : ∀ r, r ≠ .rax → r ≠ .r12 → s₁₄.gpr r = s₈.gpr r := fun r h1 h2 => by
    rw [g₁₄, u₁₃.other r h2, g₁₂ r h1, g₁₁ r h1 h2]
  have mm : s₁₄.mem = writeBytes (writeBytes (writeBytes (saveMem H.P s₀ .r8) (BL (H := H) s₀)
      (bytesAt (saveMem H.P s₀ .r8) (up s₀) H.D)) (BL (H := H) s₀ + BitVec.ofNat 64 H.D)
      ((0x80 : Byte) :: List.replicate (H.P.B - H.P.L - H.D - 1) 0))
      (BL (H := H) s₀ + BitVec.ofNat 64 (H.P.B - H.P.L)) (hH.md.lenBytes (H.P.B + H.D)) := by
    rw [m₁₄, u₁₃.mem, m₁₂, m₁₀, m₉, m₈]
  have hU : (bytesAt (saveMem H.P s₀ .r8) (up s₀) H.D).length = H.D := bytesAt_length _ _ _
  have hpz : ((0x80 : Byte) :: List.replicate (H.P.B - H.P.L - H.D - 1) 0).length = H.P.B - H.P.L - H.D := by
    simp only [List.length_cons, List.length_replicate]; omega
  have FB : Frame [sR s₀ H.blkO H.P.B] (saveMem H.P s₀ .r8) s₁₄.mem := by
    rw [mm]
    refine ((writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)).trans (writeBytes_frame _ _ _ ?_)
    · rw [hU]; simpa [z0] using bc 0 H.D (by omega)
    · rw [hpz]; exact bc _ _ (by omega)
    · rw [lbl]; exact bc _ _ (by omega)
  have FS : Frame [⟨scr s₀, H.P.so + 48⟩] s₀.mem (saveMem H.P s₀ .r8) := saveMem_frame hz.dims
  have dS : ∀ r ∈ [sR s₀ H.blkO H.P.B], (saveR (H := H) s₀).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact part_disj hz (Or.inl (by omega)) (by omega) (by omega)
  have Ffull : Frame [tR (H := H) s₀, scR (H := H) s₀, stkR s₀] s₀.mem s₁₄.mem :=
    (FS.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scR (H := H) s₀, by simp, Region.sub_prefix (by omega)⟩).trans
      (FB.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR (H := H) s₀, by simp, off_sub (by omega)⟩)
  refine ⟨⟨⟨by rw [rd₁₄, u₁₃.rd, rd₁₂, u₁₁.rd, rd₁₀, rd₉, rd₈], by rw [wr₁₄, u₁₃.wr, wr₁₂, u₁₁.wr, wr₁₀, wr₉, wr₈],
    by rw [gr _ (by decide) (by decide)]; exact oth₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [gr _ (by decide) (by decide), rbx₈], by rw [gr _ (by decide) (by decide), rbp₈],
    by rw [g₁₄, u₁₃.gpr, g₁₂ _ (by decide), g₁₁ _ (by decide) (by decide)]
       exact oth₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [gr _ (by decide) (by decide), r13₈], by rw [gr _ (by decide) (by decide), r14₈],
    by rw [gr _ (by decide) (by decide), r15₈],
    saved_frame hz (saveMem_saved hz.dims) FB dS,
    Ffull.readW (r := retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hp.ret_t
      · exact hp.ret_s
      · exact stk_ret.symm) (by decide),
    Ffull⟩, ?_, fun k0 _ => ?_⟩, ?_⟩
  · -- The padding.
    rw [mm, show H.P.B - H.D = (H.P.B - H.P.L - H.D) + H.P.L by omega, bytesAt_add,
      add_ofNat (BL (H := H) s₀) H.D, show H.D + (H.P.B - H.P.L - H.D) = H.P.B - H.P.L by omega,
      bytesAt_writeBytes_self' lbl (by omega)]
    have b₁ := bytesAt_writeBytes_sep (writeBytes (writeBytes (saveMem H.P s₀ .r8) (BL (H := H) s₀)
      (bytesAt (saveMem H.P s₀ .r8) (up s₀) H.D)) (BL (H := H) s₀ + BitVec.ofNat 64 H.D)
      ((0x80 : Byte) :: List.replicate (H.P.B - H.P.L - H.D - 1) 0))
      (p := BL (H := H) s₀ + BitVec.ofNat 64 H.D) (q := BL (H := H) s₀ + BitVec.ofNat 64 (H.P.B - H.P.L))
      (n := H.P.B - H.P.L - H.D) (hH.md.lenBytes (H.P.B + H.D))
      (by rw [lbl]; exact Offset.sep _ (Or.inl (by omega)) (by omega) (by omega)) (by omega)
    rw [b₁, bytesAt_writeBytes_self' hpz (by omega)]
    simp only [HashOK.padD, List.cons_append, List.nil_append,
      show H.P.B - H.P.L - 1 - H.D = H.P.B - H.P.L - H.D - 1 by omega]
  · -- The iteration so far: none.
    have hU' : bytesAt s₁₄.mem (BL (H := H) s₀) H.D = bytesAt s₀.mem (up s₀) H.D := by
      rw [mm]
      have b₁ := bytesAt_writeBytes_sep (writeBytes (writeBytes (saveMem H.P s₀ .r8) (BL (H := H) s₀)
        (bytesAt (saveMem H.P s₀ .r8) (up s₀) H.D)) (BL (H := H) s₀ + BitVec.ofNat 64 H.D)
        ((0x80 : Byte) :: List.replicate (H.P.B - H.P.L - H.D - 1) 0))
        (p := BL (H := H) s₀) (q := BL (H := H) s₀ + BitVec.ofNat 64 (H.P.B - H.P.L)) (n := H.D)
        (hH.md.lenBytes (H.P.B + H.D))
        (by rw [lbl]; exact Offset.sep_base _ (by omega) (by omega)) (by omega)
      have b₂ := bytesAt_writeBytes_sep (writeBytes (saveMem H.P s₀ .r8) (BL (H := H) s₀)
        (bytesAt (saveMem H.P s₀ .r8) (up s₀) H.D)) (p := BL (H := H) s₀) (n := H.D)
        ((0x80 : Byte) :: List.replicate (H.P.B - H.P.L - H.D - 1) 0)
        (by rw [hpz]; exact Offset.sep_base _ (Nat.le_refl _) (by omega)) (by omega)
      rw [b₁, b₂, bytesAt_writeBytes_self' hU (by omega)]
      exact bytes_keep FS (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.u_s.sub_right (Region.sub_prefix (by omega))) (by omega)
    have hT : bytesAt s₁₄.mem (tp s₀) H.D = bytesAt s₀.mem (tp s₀) H.D :=
      (bytes_keep FB (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.sub_right (off_sub (by omega))) (by omega)).trans
      (bytes_keep FS (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.t_s.sub_right (Region.sub_prefix (by omega))) (by omega))
    rw [hU', hT]
  · rw [z₁₄, u₁₃.other _ (by decide), g₁₂ _ (by decide), g₁₁ _ (by decide) (by decide), r13₈, BitVec.and_self, ofNat_beq_zero (by omega)]

/-- The loop: `n` steps, none when `n = 0`. -/
theorem loop_ok {s : State} (h : Inv hH s₀ (nn s₀) s) (hz0 : s.zf = some (decide (nn s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop H.body .ne)) s (Inv hH s₀ 0) := by
  have hlt := nn_lt (s₀ := s₀)
  refine WP.ite (decide (nn s₀ = 0)) (by simp [eval, hz0]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have e : nn s₀ = 0 := by simpa using h0
    exact e ▸ h
  · have hpos : 1 ≤ nn s₀ := by have := of_decide_eq_false h0; omega
    refine WP.loop (M := isa) (fun k t => ∃ m, k = m ∧ 1 ≤ m ∧ m ≤ nn s₀ ∧ Inv hH s₀ m t) ?_ (nn s₀) s
      ⟨nn s₀, rfl, hpos, (Nat.le_refl _), h⟩
    rintro k t ⟨m, hkm, h1, h2, ht⟩
    refine WP.mono (body_ok hH hp hz h1 (by omega) ht) fun t' ⟨ht', hz'⟩ => ?_
    by_cases hl : m - 1 = 0
    · exact .inl ⟨by simp [eval, hz', hl], hl ▸ ht'⟩
    · exact .inr ⟨by simp [eval, hz', hl], m - 1, by omega, m - 1, rfl, by omega, by omega, ht'⟩

theorem correct : WP isa H.iterate s₀ fun s' => gprPreserved s₀ s' ∧ (iterG hH.SH H.W).post s₀ s' := by
  refine WP.seq (WP.mono (pro_ok hH hp hz) fun s₁ ⟨h₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hH hp hz h₁ z₁) fun s₂ h₂ => ?_)
  have k₂ := h₂.kr
  refine WP.mono (restore_ok hp hz k₂.r15 k₂.saved k₂.wr)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₂.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₂.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  intro k0 hl hrI hrO
  have hS' := hH.hS; have hD' := hH.hD; have hB' := hH.hB
  rw [hB'] at hl
  rw [hS'] at hrO
  show bytesAt s'.mem (tp s₀) hH.SH.digestBytes = _
  rw [hD', hm, h₂.it k0 ⟨hl, hrI, hrO⟩]
  rfl

end

end VG.Proof.Pbkdf2.Md.X86_64
