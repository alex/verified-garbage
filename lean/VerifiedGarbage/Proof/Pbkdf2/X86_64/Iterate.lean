import VerifiedGarbage.Proof.Pbkdf2.Hmac
import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.X86_64.Contract
import VerifiedGarbage.Proof.Hmac.X86_64.Common
import VerifiedGarbage.Impl.Pbkdf2.X86_64

/-!
# PBKDF2-HMAC-SHA-256's iteration on x86-64

Untrusted: everything here is checked by Lean. Each step is two calls of
`vg_sha256_compress`, used as a black box through its proof (with the extra
fact that it leaves `rdi` and `rcx` unchanged); `VG.Proof.Pbkdf2.hmac_step`
says that they compute HMAC-SHA-256.
-/

namespace VG.Proof.Pbkdf2

open Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open Spec.Sha256 (Repr bytesAt)

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_pbkdf2_hmac_sha256_iterate(key: *const [u8; 192], u: *const [u8; 32], n: u32, t: *mut [u8; 32], scratch: *mut [u64; 48])`:
if, for a 64-byte key `K₀`, the streaming state at `key` represents
`K₀ ⊕ ipad` and the one at `key + 96` represents `K₀ ⊕ opad`, runs `n` steps
`U ← HMAC-SHA-256 (K₀, U)`, `T ← T ⊕ U` from the `U` at `u` and the `T` at
`t`, leaving the final `T` at `t`.

The code may read `key` (192 bytes) and `u` (32 bytes), and read and write
`t` (32 bytes) and `scratch` (384 bytes, whose contents on exit are
unspecified). The written regions may not overlap each other or the read
ones, nor the return address and the 8 bytes below it (where its calls of
`vg_sha256_compress` store their return address). The pointers and `n` are
public (`n` only in the low 32 bits of `rdx`); the key, `U` and `T` are secret. -/
def iterateSha256X86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 192⟩
    let u : Region := ⟨s.gpr .rsi, 32⟩
    let t : Region := ⟨s.gpr .rcx, 32⟩
    let scratch : Region := ⟨s.gpr .r8, 384⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [key, u] ∧ s.wr = [t, scratch] ∧
    key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
    ret.Disjoint key ∧ ret.Disjoint u ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
    stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch
  post s s' := ∀ k0, k0.length = 64 →
    Repr s.mem (s.gpr .rdi) (xorPad k0 ipad) → Repr s.mem (s.gpr .rdi + 96) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx) 32 =
      Spec.Pbkdf2.iterate (hmacBlockKey sha256 k0) ((s.gpr .rdx).setWidth 32).toNat
        (bytesAt s.mem (s.gpr .rsi) 32) (bytesAt s.mem (s.gpr .rcx) 32)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Pbkdf2

namespace VG.Proof.Pbkdf2.X86_64.Iterate

open VG VG.X86_64 VG.Impl.Pbkdf2.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Hmac.X86_64 (bytesAt_length writeBytes_at writeBytes_other bytesAt_getD' stateAt_eq_of_bytes
  bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.X86_64 (contains_offset sub_offset toNat_ofNat_lt ea_at)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_addi wp_mov32i compressBlocks_one callEntry_byte)
open VG.Impl.Sha256.X86_64.Stream (Callee)
open VG.Spec.Sha256 (bytesAt stateAt blockAt compress Repr)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev key : Addr := s₀.gpr .rdi
abbrev uP : Addr := s₀.gpr .rsi
abbrev tP : Addr := s₀.gpr .rcx
abbrev scr : Addr := s₀.gpr .r8
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .rdx).setWidth 32).toNat
abbrev keyR : Region := ⟨key s₀, 192⟩
abbrev uR : Region := ⟨uP s₀, 32⟩
abbrev tR : Region := ⟨tP s₀, 32⟩
abbrev scR : Region := ⟨scr s₀, 384⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 8

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, uR s₀]
  wr : s₀.wr = [tR s₀, scR s₀]
  k_t : (keyR s₀).Disjoint (tR s₀)
  k_s : (keyR s₀).Disjoint (scR s₀)
  u_t : (uR s₀).Disjoint (tR s₀)
  u_s : (uR s₀).Disjoint (scR s₀)
  t_s : (tR s₀).Disjoint (scR s₀)
  ret_k : (retR s₀).Disjoint (keyR s₀)
  ret_u : (retR s₀).Disjoint (uR s₀)
  ret_t : (retR s₀).Disjoint (tR s₀)
  ret_s : (retR s₀).Disjoint (scR s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_u : (stkR s₀).Disjoint (uR s₀)
  stk_t : (stkR s₀).Disjoint (tR s₀)
  stk_s : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Pbkdf2.iterateSha256X86_64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

/-! ## Parts of the scratch space -/

section
variable (s₀ : State)

/-- `vg_sha256_compress`'s scratch space. -/
abbrev cmpR : Region := ⟨scr s₀, 112⟩
/-- The hash value being compressed. -/
abbrev stR : Region := ⟨scr s₀ + 112, 32⟩
/-- The block. -/
abbrev blkR : Region := ⟨scr s₀ + 144, 64⟩

end

theorem cmp_sub (s₀ : State) : Region.Sub (cmpR s₀) (scR s₀) := Region.sub_prefix (by omega)
theorem st_sub (s₀ : State) : Region.Sub (stR s₀) (scR s₀) := sub_offset (off := 112) (by omega) (by omega)
theorem blk_sub (s₀ : State) : Region.Sub (blkR s₀) (scR s₀) := sub_offset (off := 144) (by omega) (by omega)

/-- Two parts of the scratch space at offsets `a` and `b` do not overlap. -/
theorem scr_disj (s₀ : State) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 384) (hb : b + n ≤ 384) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 a, m⟩ ⟨scr s₀ + BitVec.ofNat 64 b, n⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

/-! ## A call of `vg_sha256_compress` on the block -/

/-- Compressing the block at `rcx + 144` into the hash value at `rdi`, with
scratch space at `rcx`, by calling `f`. -/
theorem compressBlock_ok {f : Callee} (hf : f.Ok) {s : State} {st sc : Addr}
    (hdi : s.gpr .rdi = st) (hcx : s.gpr .rcx = sc)
    (d₁ : Region.Disjoint ⟨st, 32⟩ ⟨sc, 112⟩) (d₂ : Region.Disjoint ⟨sc + 144, 64⟩ ⟨st, 32⟩)
    (d₃ : Region.Disjoint ⟨sc + 144, 64⟩ ⟨sc, 112⟩) (d₄ : (below (s.gpr .rsp) 8).Disjoint ⟨st, 32⟩)
    (d₅ : (below (s.gpr .rsp) 8).Disjoint ⟨sc, 112⟩) (d₆ : (below (s.gpr .rsp) 8).Disjoint ⟨sc + 144, 64⟩)
    (hc : Covers [⟨sc + 144, 64⟩, ⟨st, 32⟩, ⟨sc, 112⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 32⟩, ⟨sc, 112⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 32⟩, ⟨sc, 112⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      stateAt s'.mem st = compress (stateAt s.mem st) (blockAt s.mem (sc + 144)) →
      s'.gpr .rdi = st → s'.gpr .rcx = sc → Q s') :
    WP isa (compressBlock f) s Q := by
  unfold compressBlock
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ?_)
  have e₁ : s₃.gpr .rdi = st := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  have e₂ : s₃.gpr .rdx = 1 := by rw [u₃.gpr]; rfl
  have e₃ : s₃.gpr .rcx = sc := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hcx]
  have e₄ : s₃.gpr .rsi = sc + 144 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, hcx]; rfl
  have e₅ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .rsi ∧ r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₃.other _ this.2, u₂.other _ this.1, u₁.other _ this.1]
  have e₆ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have e₇ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have e₈ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hsp : s₃.gpr .rsp = s.gpr .rsp := e₅ _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₃.callEntry.gpr r = s₃.gpr r := fun r h => State.callEntry_gpr _ h
  refine WP.call (k := Proof.Sha256.compressX86_64) hf.verified hf.nosp
    (by rw [hf.depth]; decide) (rd := [⟨sc + 144, 64 * 1⟩]) (wr := [⟨st, 32⟩, ⟨sc, 112⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), e₁, e₂, e₃, e₄, hsp]
    exact ⟨by simp, by simp, d₁, d₂, d₃, d₄, d₅⟩
  · rw [e₆, e₇]; simpa using hc
  · rw [e₇]; exact hw
  · intro s₄ hrd hwr hcs hfr hkeep ⟨s₅, hm₅, _, hpost⟩
    have k₁ := hkeep .rdi hf.keeps_rdi
    have k₃ := hkeep .rcx hf.keeps_rcx
    simp only [Proof.Sha256.compressX86_64, State.withRegions_gpr, State.withRegions_mem,
      hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
      hne _ (by decide : Reg.rdx ≠ .rsp), e₁, e₂, e₄, hm₅] at hpost
    rw [show (1 : BitVec 64).toNat = 1 from rfl, compressBlocks_one] at hpost
    have hst : stateAt s₃.callEntry.mem st = stateAt s.mem st :=
      (Proof.Sha256.Stream.stateAt_congr fun i hi => callEntry_byte s₃ (R := ⟨st, 32⟩) (by rw [hsp]; exact d₄)
        (by simp) hi).trans (by rw [e₈])
    have hblk : blockAt s₃.callEntry.mem (sc + 144) = blockAt s.mem (sc + 144) := by
      simp only [Spec.Sha256.blockAt]
      apply Proof.Sha256.Stream.parseBlock_congr
      intro k hk
      rw [callEntry_byte s₃ (R := ⟨sc + 144, 64⟩) (by rw [hsp]; exact d₆) (by simp) hk, e₈]
    refine hQ s₄ (hrd.trans e₆) (hwr.trans e₇) (fun r hr => (hcs r hr).trans (e₅ r hr))
      (by rw [hf.depth, hsp, e₈] at hfr; simpa using hfr) (by rw [hpost, hst, hblk])
      (by rw [k₁, e₁]) (by rw [k₃, e₃])

/-! ## Memory -/

open VG.Proof.Sha256.X86_64.Stream.Finalize (writeW_bswap32 flat_length)
open VG.Proof.Sha256.X86_64.Stream (wp_mov32m wp_bswap32 wp_store32 wp_movm wp_store wp_subi wp_test)
open VG.Proof.Sha256.X86_64 (ofInt_natCast)
open VG.Proof.Hmac.X86_64 (ea_off extractLsb'_read bytesAt_add)
open VG.Proof.Sha256.Stream (writeBytes_append write_eq_writeBytes writeBytes_nil)
open VG.Spec.Sha256 (HashValue wordBytes)

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem contains_base {a : Addr} {n len : Nat} (h : n ≤ len) : (⟨a, len⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem off_contains {a x : Addr} {o n len : Nat} (h : (x - (a + BitVec.ofNat 64 o)).toNat < n)
    (hl : o + n ≤ len) (ho : o < 2 ^ 64) : (⟨a, len⟩ : Region).Contains x 1 :=
  sub_offset (off := o) (len := n) hl ho x (by simp only [Region.Contains]; omega)

/-- Bytes from `p + a` are not among the first `a` from `p`. -/
theorem sep_after {p x : Addr} {a n : Nat} (h₁ : (x - (p + BitVec.ofNat 64 a)).toNat < n) (h₂ : (x - p).toNat < a)
    (ha : a + n < 2 ^ 64) : False := by
  rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega, BitVec.toNat_add,
    toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h₂
  omega

/-- A block of 32 bytes followed by the padding. -/
theorem blockAt_eq {m : Mem} {p : Addr} (h : bytesAt m (p + 32) 32 = pad96) :
    blockAt m p = block96 (bytesAt m p 32) := by
  simp only [Spec.Sha256.blockAt, block96]
  apply Proof.Sha256.Stream.parseBlock_congr
  intro k hk
  have e := bytesAt_add m p 32 32
  rw [show BitVec.ofNat 64 32 = (32 : Addr) from rfl, h] at e
  rw [← e, bytesAt_getD' _ _ (by omega : k < 32 + 32)]

/-- The first `n` words of the digest of the hash value at `st` into the
block at `sc + 144`. -/
theorem out_ok {st sc : Addr} (hd : Region.Disjoint ⟨st, 32⟩ ⟨sc + 144, 32⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .rdi = st → s.gpr .rcx = sc →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 8, InRegions s.wr (sc + 144 + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (sc + 144) (((stateAt s.mem st).toList.take n).flatMap wordBytes) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap outW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hdi hcx hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hdi hcx hin hout fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    have hP := flat_length (stateAt s.mem st) n (by omega)
    simp only [outW, List.cons_append, List.nil_append]
    refine wp_mov32m (a := st + BitVec.ofNat 64 (4 * n)) (by rw [ea_at, g₁ _ (by decide), hdi, ofInt_natCast])
      (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_bswap32 fun s₃ u₃ => wp_store32 (a := sc + 144 + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hcx]; rfl)
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [rd₄, u₃.rd, u₂.rd, rd₁]) (by rw [wr₄, u₃.wr, u₂.wr, wr₁]) ?_
    have hread : s₁.mem.readW (st + BitVec.ofNat 64 (4 * n)) 32 = (stateAt s.mem st)[n] := by
      rw [m₁, (writeBytes_frame s.mem (sc + 144) _ (R := ⟨sc + 144, 32⟩)
        (contains_base (by rw [hP]; omega))).readW
        (r := ⟨st + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset (by omega) (by omega))
    rw [m₄, u₃.mem, u₂.mem, u₃.gpr, u₂.gpr, hread, BitVec.setWidth_setWidth_of_le _ (by omega),
      BitVec.setWidth_eq, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, m₁,
      writeW_bswap32, show sc + 144 + BitVec.ofNat 64 (4 * n) = sc + 144 + BitVec.ofNat 64
        (((stateAt s.mem st).toList.take n).flatMap wordBytes).length by rw [hP]]
    rw [writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem writeW_xor (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 64 ^^^ m'.readW b 64) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 8) (bytesAt m' a 8)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (64 : Nat) / 8 = 8 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, extractLsb'_read _ _ h₁, extractLsb'_read _ _ h₁, BitVec.xor_comm]

theorem xorBytes_length (a b : List Byte) (h : a.length = b.length) :
    (Spec.Pbkdf2.xorBytes a b).length = a.length := by
  simp [Spec.Pbkdf2.xorBytes, h]

theorem wp_xorm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.mem m) :: is)) s Q := by
  refine Proof.Sha256.X86_64.Stream.WP.cons (s' := (arithFlags s (s.gpr d ^^^ s.mem.readW a 64) false false).setReg d _) ?_
    (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu, readSrc, State.load64, ha, hin]

/-- `T ← T ⊕ U` for the first `n` 64-bit words of `T` at `tp` and `U` at `sc + 144`. -/
theorem xor_ok {tp sc : Addr} (hd : Region.Disjoint ⟨tp, 32⟩ ⟨sc + 144, 32⟩) :
    ∀ n ≤ 4, ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .rbp = tp → s.gpr .rcx = sc →
    (∀ k < 4, InRegions (s.rd ++ s.wr) (sc + 144 + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 4, InRegions s.wr (tp + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem tp
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (8 * n)) (bytesAt s.mem (sc + 144) (8 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap xorW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q hbp hcx hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q hbp hcx hin hout fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_movm (a := sc + 144 + BitVec.ofNat 64 (8 * n))
      (by rw [ea_off, g₁ _ (by decide), hcx]; rfl) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    have hw := hout n (by omega)
    refine wp_xorm (a := tp + BitVec.ofNat 64 (8 * n))
      (by rw [ea_at, u₂.other _ (by decide), g₁ _ (by decide), hbp, ofInt_natCast])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine wp_store (a := tp + BitVec.ofNat 64 (8 * n))
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hbp, ofInt_natCast])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [rd₄, u₃.rd, u₂.rd, rd₁]) (by rw [wr₄, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (8 * n)) (bytesAt s.mem (sc + 144) (8 * n))).length =
        8 * n := by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    rw [m₄, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, writeW_xor, m₁,
      bytesAt_writeBytes_sep (p := tp + BitVec.ofNat 64 (8 * n)),
      bytesAt_writeBytes_sep (p := sc + 144 + BitVec.ofNat 64 (8 * n))]
    · have e := writeBytes_append s.mem tp _ (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp + BitVec.ofNat 64 (8 * n)) 8)
        (bytesAt s.mem (sc + 144 + BitVec.ofNat 64 (8 * n)) 8))
        (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
      rw [hl] at e
      rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
        Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt])]
    · intro x h₁ h₂
      rw [hl] at h₂
      exact hd x (by simp only [Region.Contains]; omega) (off_contains h₁ (by omega) (by omega))
    · omega
    · intro x h₁ h₂
      rw [hl] at h₂
      exact sep_after h₁ h₂ (by omega)
    · omega

/-! ## Regions -/

theorem add_ofNat (a : Addr) (o j : Nat) : a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem InRegions.right {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

section
variable {s₀ : State} (hp : Pre s₀) {s : State}
include hp

theorem in_scr (hwr : s.wr = s₀.wr) {a b n : Nat} (h : a + b + n ≤ 384) :
    InRegions s.wr (scr s₀ + BitVec.ofNat 64 a + BitVec.ofNat 64 b) n :=
  ⟨scR s₀, by simp [hwr, hp.wr], by rw [add_ofNat]; exact contains_offset (by omega) (by omega)⟩

theorem in_t (hwr : s.wr = s₀.wr) {b n : Nat} (h : b + n ≤ 32) :
    InRegions s.wr (tP s₀ + BitVec.ofNat 64 b) n :=
  ⟨tR s₀, by simp [hwr, hp.wr], contains_offset (by omega) (by omega)⟩

theorem in_key (hrd : s.rd = s₀.rd) {a b n : Nat} (h : a + b + n ≤ 192) :
    InRegions (s.rd ++ s.wr) (key s₀ + BitVec.ofNat 64 a + BitVec.ofNat 64 b) n :=
  ⟨keyR s₀, by simp [hrd, hp.rd], by rw [add_ofNat]; exact contains_offset (by omega) (by omega)⟩

end

section
variable (s₀ : State)

/-- The compression's scratch space and the hash value being compressed. -/
abbrev lowR : Region := ⟨scr s₀, 144⟩

/-- A part of the scratch space. -/
abbrev sR (o n : Nat) : Region := ⟨scr s₀ + BitVec.ofNat 64 o, n⟩

end

theorem scr_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 384) : Region.Sub (sR s₀ o n) (scR s₀) :=
  sub_offset h (by omega)

/-- Parts of the scratch space at `[o, o + n)` with `144 ≤ o`, which the
compression and loading its hash value leave. -/
theorem high_disj {s₀ : State} (hp : Pre s₀) {o n : Nat} (h₁ : 144 ≤ o) (h₂ : o + n ≤ 384) :
    ∀ r ∈ [lowR s₀, stkR s₀], Region.Disjoint (sR s₀ o n) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := scr_disj s₀ (a := o) (m := n) (b := 0) (n := 144) (by omega) h₂ (by omega)
    simpa using this
  · exact (hp.stk_s.sub_right (scr_sub s₀ h₂)).symm

theorem t_disj {s₀ : State} (hp : Pre s₀) : ∀ r ∈ [lowR s₀, stkR s₀], Region.Disjoint (tR s₀) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.t_s.sub_right (Region.sub_prefix (by omega))
  · exact hp.stk_t.symm

theorem key_disj {s₀ : State} (hp : Pre s₀) : ∀ r ∈ [tR s₀, scR s₀, stkR s₀], Region.Disjoint (keyR s₀) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.k_t
  · exact hp.k_s
  · exact hp.stk_k.symm

/-! ## A step -/

section
variable (s₀ : State)

/-- The key's inner and outer hash values. -/
abbrev Hi : HashValue := stateAt s₀.mem (key s₀)
abbrev Ho : HashValue := stateAt s₀.mem (key s₀ + 96)

/-- A step, as the code computes it. -/
def stepM (u : List Byte) : List Byte :=
  Pbkdf2.digest (compress (Ho s₀) (block96 (Pbkdf2.digest (compress (Hi s₀) (block96 u)))))

/-- Our caller's registers, saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

/-- The registers the body keeps. -/
def kept : List Reg := [.rbx, .rbp, .rcx, .rdi, .rsp, .r12, .r13, .r14, .r15]

end

/-- From `s` to `s'`, the body only changed the compression's part of the
scratch space and the stack. -/
structure Keep (s₀ s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  gpr : ∀ r ∈ kept, s'.gpr r = s.gpr r
  frame : Frame [lowR s₀, stkR s₀] s.mem s'.mem

theorem Keep.trans {s₀ s₁ s₂ s₃ : State} (h₁ : Keep s₀ s₁ s₂) (h₂ : Keep s₀ s₂ s₃) : Keep s₀ s₁ s₃ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr),
    h₁.frame.trans h₂.frame⟩

/-- The registers and memory at the start of each step. -/
structure Regs (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = key s₀
  rbp : s.gpr .rbp = tP s₀
  rcx : s.gpr .rcx = scr s₀
  rdi : s.gpr .rdi = scr s₀ + 112
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r12 : s.gpr .r12 = s₀.gpr .r12
  r14 : s.gpr .r14 = s₀.gpr .r14
  r15 : s.gpr .r15 = s₀.gpr .r15
  frame : Frame [tR s₀, scR s₀, stkR s₀] s₀.mem s.mem

theorem Regs.keep {s₀ s s' : State} (h : Regs s₀ s) (hk : Keep s₀ s s') : Regs s₀ s' where
  rd := hk.rd.trans h.rd
  wr := hk.wr.trans h.wr
  rbx := (hk.gpr _ (by simp [kept])).trans h.rbx
  rbp := (hk.gpr _ (by simp [kept])).trans h.rbp
  rcx := (hk.gpr _ (by simp [kept])).trans h.rcx
  rdi := (hk.gpr _ (by simp [kept])).trans h.rdi
  rsp := (hk.gpr _ (by simp [kept])).trans h.rsp
  r12 := (hk.gpr _ (by simp [kept])).trans h.r12
  r14 := (hk.gpr _ (by simp [kept])).trans h.r14
  r15 := (hk.gpr _ (by simp [kept])).trans h.r15
  frame := h.frame.trans (hk.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

/-- The key's bytes are as on entry. -/
theorem Regs.key_bytes {s₀ s : State} (hp : Pre s₀) (h : Regs s₀ s) {i : Nat} (hi : i < 192) :
    s.mem (key s₀ + BitVec.ofNat 64 i) = s₀.mem (key s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := keyR s₀) (key_disj hp) (by simp) hi

/-- A copied hash value. -/
theorem stateAt_copy (m m' : Mem) (q p : Addr) :
    stateAt (writeBytes m q (bytesAt m' p 32)) q = stateAt m' p := by
  apply stateAt_eq_of_bytes
  intro i hi
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi]

/-- Loading the hash value at `key + o` into `scratch[112..144)`. -/
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) {o : Nat} (ho : o + 32 ≤ 192)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' → stateAt s'.mem (scr s₀ + 112) = stateAt s₀.mem (key s₀ + BitVec.ofNat 64 o) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (load o ++ rest)) s Q := by
  unfold load
  refine Proof.Hmac.X86_64.copy64_ok (by decide) (by decide) o 0 4 rest s Q
    (fun j hj => by rw [h.rbx]; exact in_key hp h.rd (by omega))
    (fun j hj => by rw [h.rdi, add_ofNat (scr s₀ + 112)]; exact in_scr hp h.wr (a := 112) (by omega))
    ?_ (by omega) fun s' g' rd' wr' m' => k s' ⟨rd', wr', fun r hr => g' r (by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩ ?_
  · rw [h.rbx, h.rdi]
    refine Region.Disjoint.sep hp.k_s ?_ ?_
    · exact contains_offset (by omega) (by omega)
    · rw [show scr s₀ + 112 + BitVec.ofNat 64 0 = scr s₀ + BitVec.ofNat 64 112 by bv_omega]
      exact contains_offset (by omega) (by omega)
  · rw [m']
    refine (writeBytes_frame _ _ _ (R := lowR s₀) ?_).mono (by simp)
    rw [h.rdi, bytesAt_length, show scr s₀ + 112 + BitVec.ofNat 64 0 = scr s₀ + BitVec.ofNat 64 112 by bv_omega]
    exact contains_offset (by omega) (by omega)
  · rw [m', h.rdi, h.rbx, show scr s₀ + 112 + BitVec.ofNat 64 0 = scr s₀ + 112 by bv_omega, stateAt_copy]
    apply Proof.Sha256.Stream.stateAt_congr
    intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.key_bytes hp (by omega)

theorem scr_disj0 (s₀ : State) {a m n : Nat} (h : n ≤ a) (ha : a + m ≤ 384) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 a, m⟩ ⟨scr s₀, n⟩ := by
  have := scr_disj s₀ (a := a) (m := m) (b := 0) (n := n) (by omega) ha (by omega)
  simpa using this

theorem stk_scr {s₀ : State} (hp : Pre s₀) {a m : Nat} (ha : a + m ≤ 384) :
    (stkR s₀).Disjoint ⟨scr s₀ + BitVec.ofNat 64 a, m⟩ :=
  hp.stk_s.sub_right (scr_sub s₀ ha)

/-- A call of the compression function on the block, in the loop. -/
theorem cmp_ok {f : Callee} (hf : f.Ok) {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) {Q : State → Prop}
    (k : ∀ s', Keep s₀ s s' →
      stateAt s'.mem (scr s₀ + 112) = compress (stateAt s.mem (scr s₀ + 112)) (blockAt s.mem (scr s₀ + 144)) →
      Q s') :
    WP isa (compressBlock f) s Q := by
  have hsp : below (s.gpr .rsp) 8 = stkR s₀ := by rw [h.rsp]
  have hsc : (scR s₀) ∈ s.wr := by simp [h.wr, hp.wr]
  refine compressBlock_ok hf (st := scr s₀ + 112) (sc := scr s₀) h.rdi h.rcx
    (scr_disj0 s₀ (a := 112) (by omega) (by omega)) (scr_disj s₀ (a := 144) (b := 112) (by omega) (by omega) (by omega))
    (scr_disj0 s₀ (a := 144) (by omega) (by omega)) (by rw [hsp]; exact stk_scr hp (a := 112) (by omega))
    (by rw [hsp]; simpa using stk_scr hp (a := 0) (m := 112) (by omega))
    (by rw [hsp]; exact stk_scr hp (a := 144) (by omega)) ?_ ?_ ?_
  · refine Covers.of_sub fun r hr => ⟨scR s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨144, rfl, by simp⟩
    · exact ⟨112, rfl, by simp⟩
    · exact ⟨0, by simp, by simp⟩
  · refine Covers.of_sub fun r hr => ⟨scR s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨112, rfl, by simp⟩
    · exact ⟨0, by simp, by simp⟩
  · intro s' hrd hwr hcs hf hst hdi hcx
    refine k s' ⟨hrd, hwr, fun r hr => ?_, ?_⟩ hst
    · simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hcs _ (by simp [calleeSaved])
      · exact hcs _ (by simp [calleeSaved])
      · rw [hcx, h.rcx]
      · rw [hdi, h.rdi]
      · exact hcs _ (by simp [calleeSaved])
      · exact hcs _ (by simp [calleeSaved])
      · exact hcs _ (by simp [calleeSaved])
      · exact hcs _ (by simp [calleeSaved])
      · exact hcs _ (by simp [calleeSaved])
    · rw [hsp] at hf
      refine hf.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨lowR s₀, by simp, sub_offset (off := 112) (by omega) (by omega)⟩
      · exact ⟨lowR s₀, by simp, Region.sub_prefix (by omega)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-! ## The loop -/

/-- What the body writes: the compression's part of the scratch space, the
stack, the block's first 32 bytes and `T`. -/
abbrev bodyR (s₀ : State) : List Region := [lowR s₀, stkR s₀, sR s₀ 144 32, tR s₀]

/-- The loop invariant, with `r` steps left. -/
structure Inv (s₀ : State) (r : Nat) (s : State) : Prop extends Regs s₀ s where
  r13 : s.gpr .r13 = BitVec.ofNat 64 r
  saved : Saved s₀ s.mem
  pad : bytesAt s.mem (scr s₀ + BitVec.ofNat 64 176) 32 = pad96
  le : r ≤ nn s₀
  val : Spec.Pbkdf2.iterate (stepM s₀) (nn s₀) (bytesAt s₀.mem (uP s₀) 32) (bytesAt s₀.mem (tP s₀) 32) =
    Spec.Pbkdf2.iterate (stepM s₀) r (bytesAt s.mem (scr s₀ + 144) 32) (bytesAt s.mem (tP s₀) 32)

theorem Regs.write {s₀ s s' : State} (h : Regs s₀ s) (hg : ∀ r, r ≠ .rax → r ≠ .r13 → s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) {R : Region} (hR : R ∈ [tR s₀, scR s₀, stkR s₀])
    (hm : Frame [R] s.mem s'.mem) : Regs s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := (hg _ (by decide) (by decide)).trans h.rbx
  rbp := (hg _ (by decide) (by decide)).trans h.rbp
  rcx := (hg _ (by decide) (by decide)).trans h.rcx
  rdi := (hg _ (by decide) (by decide)).trans h.rdi
  rsp := (hg _ (by decide) (by decide)).trans h.rsp
  r12 := (hg _ (by decide) (by decide)).trans h.r12
  r14 := (hg _ (by decide) (by decide)).trans h.r14
  r15 := (hg _ (by decide) (by decide)).trans h.r15
  frame := h.frame.trans (hm.mono (by simpa using hR))

/-- The parts of the scratch space from offset 176, which the body leaves. -/
theorem body_disj {s₀ : State} (hp : Pre s₀) {o n : Nat} (h₁ : 176 ≤ o) (h₂ : o + n ≤ 384) :
    ∀ r ∈ bodyR s₀, Region.Disjoint (sR s₀ o n) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact high_disj hp (by omega) h₂ _ (by simp)
  · exact high_disj hp (by omega) h₂ _ (by simp)
  · exact scr_disj s₀ (by omega) h₂ (by omega)
  · exact (hp.t_s.sub_right (scr_sub s₀ h₂)).symm

theorem Saved.frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Saved s₀ m) (hf : Frame (bodyR s₀) m m') :
    Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  have hd : 176 ≤ p.2 ∧ p.2 + 8 ≤ 384 := by rcases hp' with rfl | rfl | rfl <;> simp
  exact hf.readW (r := sR s₀ p.2 8) (Region.contains_self _ _) (body_disj hp hd.1 hd.2) (by decide)

theorem frame_body {s₀ : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, r ∈ bodyR s₀) :
    Frame (bodyR s₀) m m' := hf.mono hs

theorem digest_eq (H : HashValue) : (H.toList.take 8).flatMap wordBytes = Pbkdf2.digest H := by
  rw [List.take_of_length_le (by simp)]; rfl

/-- The digest of the hash value in the scratch space into the block. -/
theorem digest_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Regs s₀ s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Regs s₀ s' → (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → Frame [sR s₀ 144 32] s.mem s'.mem →
      s'.mem = writeBytes s.mem (scr s₀ + 144) (Pbkdf2.digest (stateAt s.mem (scr s₀ + 112))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.Pbkdf2.X86_64.digest ++ rest)) s Q := by
  unfold Impl.Pbkdf2.X86_64.digest
  refine out_ok (st := scr s₀ + 112) (sc := scr s₀) (scr_disj s₀ (a := 112) (b := 144) (by omega) (by omega)
    (by omega)) 8 (Nat.le_refl _) rest s Q h.rdi h.rcx (fun j hj => InRegions.right (in_scr hp h.wr (a := 112) (b := 4 * j) (n := 4) (by omega)))
    (fun j hj => in_scr hp h.wr (a := 144) (by omega)) fun s' g' rd' wr' m' => ?_
  rw [digest_eq] at m'
  have hf : Frame [sR s₀ 144 32] s.mem s'.mem := by
    rw [m']; exact writeBytes_frame _ _ _ (contains_base (by rw [Pbkdf2.digest_length]))
  exact k s' (h.write (fun r hr _ => g' r hr) rd' wr' (R := scR s₀) (by simp) (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)) g' hf m'

theorem digest_self (m : Mem) (q : Addr) (H : HashValue) :
    bytesAt (writeBytes m q (Pbkdf2.digest H)) q 32 = Pbkdf2.digest H := by
  have := bytesAt_writeBytes_self m q (Pbkdf2.digest H) (by rw [Pbkdf2.digest_length]; omega)
  rwa [Pbkdf2.digest_length] at this

theorem body_ok {f : Callee} (hf : f.Ok) {s₀ : State} (hp : Pre s₀) {r : Nat} {s : State}
    (h : Inv s₀ (r + 1) s) :
    WP isa (body f) s fun s' => eval .ne s' = some (r != 0) ∧ Inv s₀ r s' := by
  unfold body
  have hU : ∀ {m : Mem}, Frame [lowR s₀, stkR s₀] s.mem m →
      bytesAt m (scr s₀ + 144) 32 = bytesAt s.mem (scr s₀ + 144) 32 :=
    fun hf => frame_bytesAt hf (high_disj hp (o := 144) (n := 32) (by omega) (by omega)) (by omega)
  have hpad : ∀ {m : Mem}, Frame (bodyR s₀) s.mem m → bytesAt m (scr s₀ + 144 + 32) 32 = pad96 := by
    intro m hf
    rw [show scr s₀ + 144 + 32 = scr s₀ + BitVec.ofNat 64 176 by bv_omega, ← h.pad]
    exact frame_bytesAt hf (body_disj hp (o := 176) (n := 32) (by omega) (by omega)) (by omega)
  -- The inner hash.
  refine WP.seq ?_
  rw [← List.append_nil (load 0)]
  refine load_ok hp h.toRegs (o := 0) (by omega) fun s₁ k₁ e₁ => WP.block_nil ?_
  refine WP.seq (cmp_ok hf hp (h.toRegs.keep k₁) fun s₂ k₂ e₂ => ?_)
  rw [e₁, blockAt_eq (hpad (frame_body k₁.frame (by simp))), hU k₁.frame,
    show key s₀ + BitVec.ofNat 64 0 = key s₀ by simp] at e₂
  -- The outer hash.
  have h₂ := (h.toRegs.keep k₁).keep k₂
  refine WP.seq ?_
  refine digest_ok hp h₂ fun s₃ h₃ g₃ f₃ m₃ => ?_
  refine load_ok hp h₃ (o := 96) (by omega) fun s₄ k₄ e₄ => WP.block_nil ?_
  have f₂₃ : Frame (bodyR s₀) s.mem s₃.mem :=
    (frame_body (k₁.frame.trans k₂.frame) (by simp)).trans (frame_body f₃ (by simp))
  refine WP.seq (cmp_ok hf hp (h₃.keep k₄) fun s₅ k₅ e₅ => ?_)
  have hX : bytesAt s₄.mem (scr s₀ + 144) 32 = Pbkdf2.digest (stateAt s₂.mem (scr s₀ + 112)) := by
    rw [frame_bytesAt (p := scr s₀ + 144) (n := 32) k₄.frame (high_disj hp (o := 144) (n := 32) (by omega) (by omega)) (by omega), m₃,
      digest_self]
  rw [e₄, blockAt_eq (hpad (f₂₃.trans (frame_body k₄.frame (by simp)))), hX, e₂] at e₅
  -- The digest, `T ← T ⊕ U` and the count.
  have h₅ := (h₃.keep k₄).keep k₅
  rw [List.append_assoc]
  refine digest_ok hp h₅ fun s₆ h₆ g₆ f₆ m₆ => ?_
  have hd : Region.Disjoint (tR s₀) ⟨scr s₀ + 144, 32⟩ := hp.t_s.sub_right (scr_sub s₀ (o := 144) (by omega))
  refine xor_ok (tp := tP s₀) (sc := scr s₀) hd 4 (Nat.le_refl _) _ s₆ _ h₆.rbp h₆.rcx
    (fun j hj => InRegions.right (in_scr hp h₆.wr (a := 144) (b := 8 * j) (n := 8) (by omega)))
    (fun j hj => in_t hp h₆.wr (b := 8 * j) (n := 8) (by omega)) fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  rw [show 8 * 4 = 32 from rfl] at m₇
  have f₇ : Frame [tR s₀] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (contains_base (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]))
  have h₇ := h₆.write (fun r hr _ => g₇ r hr) rd₇ wr₇ (R := tR s₀) (by simp) f₇
  refine wp_subi fun s₈ u₈ z₈ => WP.block_nil ?_
  have h₈ := h₇.write (fun r _ hr => u₈.other r hr) u₈.rd u₈.wr (R := tR s₀) (by simp) (by rw [u₈.mem]; exact Frame.refl _ _)
  have r13 : s₇.gpr .r13 = BitVec.ofNat 64 (r + 1) := by
    rw [g₇ _ (by decide), g₆ _ (by decide), k₅.gpr _ (by simp [kept]), k₄.gpr _ (by simp [kept]), g₃ _ (by decide),
      k₂.gpr _ (by simp [kept]), k₁.gpr _ (by simp [kept]), h.r13]
  have hlt : r + 1 < 2 ^ 64 := by have := h.le; have := (s₀.gpr .rdx).setWidth 32 |>.isLt; simp at *; omega
  have e₈ : s₇.gpr .r13 - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 r := by
    rw [r13, show (1 : BitVec 32).signExtend 64 = 1 from rfl, Proof.Sha256.X86_64.Stream.ofNat_pred (by omega)]; rfl
  have fb : Frame (bodyR s₀) s.mem s₈.mem := by
    rw [u₈.mem]
    exact f₂₃.trans (frame_body (k₄.frame.trans k₅.frame) (by simp)) |>.trans (frame_body f₆ (by simp))
      |>.trans (frame_body f₇ (by simp))
  have f₆' : Frame [lowR s₀, stkR s₀, sR s₀ 144 32] s.mem s₆.mem :=
    (k₁.frame.trans k₂.frame).mono (by simp) |>.trans (f₃.mono (by simp)) |>.trans ((k₄.frame.trans k₅.frame).mono
      (by simp)) |>.trans (f₆.mono (by simp))
  have hT : bytesAt s₆.mem (tP s₀) 32 = bytesAt s.mem (tP s₀) 32 := by
    refine frame_bytesAt f₆' (fun r hr => ?_) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact t_disj hp _ (by simp)
    · exact t_disj hp _ (by simp)
    · exact hd
  have hU₆ : bytesAt s₆.mem (scr s₀ + 144) 32 = stepM s₀ (bytesAt s.mem (scr s₀ + 144) 32) := by
    rw [m₆, digest_self, e₅]; rfl
  have hU₈ : bytesAt s₈.mem (scr s₀ + 144) 32 = stepM s₀ (bytesAt s.mem (scr s₀ + 144) 32) := by
    rw [u₈.mem, m₇, bytesAt_writeBytes_sep _ _ (fun x h₁ h₂ => hd x ?_ ?_) (by omega), hU₆]
    · simp only [Region.Contains]; rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at h₂; omega
    · simp only [Region.Contains]; omega
  have hT₈ : bytesAt s₈.mem (tP s₀) 32 =
      Spec.Pbkdf2.xorBytes (bytesAt s.mem (tP s₀) 32) (stepM s₀ (bytesAt s.mem (scr s₀ + 144) 32)) := by
    have := bytesAt_writeBytes_self s₆.mem (tP s₀)
      (Spec.Pbkdf2.xorBytes (bytesAt s₆.mem (tP s₀) 32) (bytesAt s₆.mem (scr s₀ + 144) 32))
      (by rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length] at this
    rw [u₈.mem, m₇, this, hT, hU₆]
  refine ⟨?_, { h₈ with r13 := ?_, saved := h.saved.frame hp fb, pad := ?_, le := by have := h.le; omega, val := ?_ }⟩
  · simp only [eval, z₈, e₈, Option.map_some, Proof.Sha256.X86_64.Stream.ofNat_beq_zero (by omega : r < 2 ^ 64)]
    cases r <;> rfl
  · rw [u₈.gpr, e₈]
  · rw [← h.pad]; exact frame_bytesAt fb (body_disj hp (o := 176) (n := 32) (by omega) (by omega)) (by omega)
  · rw [h.val, hU₈, hT₈]; rfl

theorem loop_ok {f : Callee} (hf : f.Ok) {s₀ : State} (hp : Pre s₀) {n : Nat} {s : State}
    (h : Inv s₀ n s) (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop (body f) .ne)) s (Inv s₀ 0) := by
  refine WP.ite (decide (n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (fun m s => Inv s₀ (m + 1) s) (fun m s hs => WP.mono (body_ok hf hp hs) fun s' ⟨he, hi⟩ => ?_) m s h
    cases m with
    | zero => exact .inl ⟨he, hi⟩
    | succ m => exact .inr ⟨he, m, by omega, hi⟩

/-! ## The result -/

theorem iterate_congr {f g : List Byte → List Byte} (hfg : ∀ u, u.length = 32 → f u = g u)
    (hg : ∀ u, (g u).length = 32) :
    ∀ n u t, u.length = 32 → Spec.Pbkdf2.iterate f n u t = Spec.Pbkdf2.iterate g n u t := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro u t hu
    simp only [Spec.Pbkdf2.iterate]
    rw [hfg u hu]
    exact ih _ _ (hg u)

/-- With the key's streaming states as the contract requires, a step is HMAC-SHA-256. -/
theorem stepM_eq {s₀ : State} {k0 : List Byte} (hk : k0.length = 64)
    (hi : Repr s₀.mem (key s₀) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad))
    (ho : Repr s₀.mem (key s₀ + 96) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)) {u : List Byte} (hu : u.length = 32) :
    Spec.Hmac.hmacBlockKey Spec.Hmac.sha256 k0 u = stepM s₀ u := by
  have li : (Spec.Hmac.xorPad k0 Spec.Hmac.ipad).length = 64 := by simp [Spec.Hmac.xorPad, hk]
  have lo : (Spec.Hmac.xorPad k0 Spec.Hmac.opad).length = 64 := by simp [Spec.Hmac.xorPad, hk]
  rw [hmac_step hk hu, stepM, Hi, Ho, hi.1, ho.1, li, lo]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ 0 s) :
    WP isa (.block epilogue) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Pbkdf2.iterateSha256X86_64.post s₀ s' := by
  have i : ∀ {s' : State}, s'.rd = s₀.rd → s'.wr = s₀.wr → ∀ d : Nat, d + 8 ≤ 384 →
      InRegions (s'.rd ++ s'.wr) (scr s₀ + BitVec.ofNat 64 d) 8 := fun hrd hwr d hd => by
    have := InRegions.right (rd := s₀.rd) (in_scr hp hwr (a := d) (b := 0) (n := 8) (by omega))
    rw [hrd]; simpa using this
  simp only [epilogue, saved, List.map_cons, List.map_nil]
  refine wp_movm (a := scr s₀ + BitVec.ofNat 64 208) (by rw [ea_at, h.rcx, ofInt_natCast]) (i h.rd h.wr 208 (by omega))
    fun s₁ u₁ => ?_
  refine wp_movm (a := scr s₀ + BitVec.ofNat 64 216)
    (by rw [ea_at, u₁.other _ (by decide), h.rcx, ofInt_natCast])
    (i (u₁.rd.trans h.rd) (u₁.wr.trans h.wr) 216 (by omega)) fun s₂ u₂ => ?_
  refine wp_movm (a := scr s₀ + BitVec.ofNat 64 224)
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.rcx, ofInt_natCast])
    (i (u₂.rd.trans (u₁.rd.trans h.rd)) (u₂.wr.trans (u₁.wr.trans h.wr)) 224 (by omega)) fun s₃ u₃ => WP.block_nil ?_
  have hm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun k0 hk hi ho => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      exact h.saved (.rbx, 208) (by simp [saved])
    · rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]
      exact h.saved (.rbp, 216) (by simp [saved])
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.rsp]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r12]
    · rw [u₃.gpr, u₂.mem, u₁.mem]
      exact h.saved (.r13, 224) (by simp [saved])
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r14]
    · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r15]
  · rw [hm]
    refine h.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_t
    · exact hp.ret_s
    · exact ret_stk s₀
  · have := h.val
    simp only [Spec.Pbkdf2.iterate] at this
    rw [hm, ← this]
    refine (iterate_congr (fun u hu => stepM_eq hk hi ho hu) (fun u => Pbkdf2.digest_length _) _ _ _
      (bytesAt_length _ _ _)).symm

/-! ## The prologue -/

theorem writeW_bytes (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (xs : List Byte)
    (h : ((List.range (w / 8)).map fun j => (v.setWidth (8 * (w / 8))).extractLsb' (8 * j) 8) = xs) :
    m.writeW a v = writeBytes m a xs := by
  rw [Mem.writeW, write_eq_writeBytes, h]

theorem writeBytes_append' (m : Mem) {q q' : Addr} (xs ys : List Byte) (hq : q' = q + BitVec.ofNat 64 xs.length)
    (h : xs.length + ys.length < 2 ^ 64) : writeBytes (writeBytes m q xs) q' ys = writeBytes m q (xs ++ ys) := by
  subst hq; exact writeBytes_append m q xs ys h

/-- The padding into `scratch[176..208)`. -/
theorem padding_ok {s₀ : State} (hp : Pre s₀) {s : State} (hcx : s.gpr .rcx = scr s₀) (hwr : s.wr = s₀.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 176) pad96 → WP isa (.block rest) s' Q) :
    WP isa (.block (padding ++ rest)) s Q := by
  have io : ∀ {s' : State}, s'.wr = s.wr → ∀ d n : Nat, d + n ≤ 384 → InRegions s'.wr (scr s₀ + BitVec.ofNat 64 d) n :=
    fun hw d n hd => by have := in_scr hp (hw.trans hwr) (a := d) (b := 0) (n := n) (by omega); simpa using this
  simp only [padding, List.cons_append, List.nil_append]
  refine wp_mov32i fun s₁ u₁ _ _ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofNat 64 176) (by rw [ea_at, u₁.other _ (by decide), hcx, ofInt_natCast])
    (io u₁.wr 176 8 (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_mov32i fun s₃ u₃ _ _ => ?_
  have c₃ : s₃.gpr .rcx = scr s₀ := by rw [u₃.other _ (by decide), g₂, u₁.other _ (by decide), hcx]
  have w₃ : s₃.wr = s.wr := by rw [u₃.wr, wr₂, u₁.wr]
  refine wp_store (a := scr s₀ + BitVec.ofNat 64 184) (by rw [ea_at, c₃, ofInt_natCast])
    (io w₃ 184 8 (by omega)) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofNat 64 192) (by rw [ea_at, g₄, c₃, ofInt_natCast])
    (io (wr₄.trans w₃) 192 8 (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store32 (a := scr s₀ + BitVec.ofNat 64 200) (by rw [ea_at, g₅, g₄, c₃, ofInt_natCast])
    (io (wr₅.trans (wr₄.trans w₃)) 200 4 (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  refine wp_mov32i fun s₇ u₇ _ _ => ?_
  refine wp_store32 (a := scr s₀ + BitVec.ofNat 64 204)
    (by rw [ea_at, u₇.other _ (by decide), g₆, g₅, g₄, c₃, ofInt_natCast])
    (by rw [u₇.wr]; exact io (wr₆.trans (wr₅.trans (wr₄.trans w₃))) 204 4 (by omega)) fun s₈ g₈ m₈ rd₈ wr₈ => ?_
  refine k s₈ (fun r hr => ?_) (by rw [rd₈, u₇.rd, rd₆, rd₅, rd₄, u₃.rd, rd₂, u₁.rd])
    (by rw [wr₈, u₇.wr, wr₆, wr₅, wr₄, u₃.wr, wr₂, u₁.wr]) ?_
  · rw [g₈, u₇.other r hr, g₆, g₅, g₄, u₃.other r hr, g₂, u₁.other r hr]
  · have e₂ : s₂.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 176) [0x80, 0, 0, 0, 0, 0, 0, 0] := by
      rw [m₂, u₁.gpr, u₁.mem]; exact writeW_bytes _ _ _ _ (by decide)
    have e₄ : s₄.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 176)
        ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]) := by
      rw [m₄, u₃.gpr, u₃.mem, e₂, writeW_bytes _ _ _ [0, 0, 0, 0, 0, 0, 0, 0] (by decide)]
      exact writeBytes_append' _ _ _ (by simp only [List.length_cons, List.length_nil]; bv_omega) (by simp)
    have e₅ : s₅.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 176)
        ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0]) := by
      rw [m₅, g₄, u₃.gpr, e₄, writeW_bytes _ _ _ [0, 0, 0, 0, 0, 0, 0, 0] (by decide)]
      exact writeBytes_append' _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; bv_omega)
        (by simp)
    have e₆ : s₆.mem = writeBytes s.mem (scr s₀ + BitVec.ofNat 64 176)
        ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
      rw [m₆, g₅, g₄, u₃.gpr, e₅, writeW_bytes _ _ _ [0, 0, 0, 0] (by decide)]
      exact writeBytes_append' _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; bv_omega)
        (by simp)
    rw [m₈, u₇.gpr, u₇.mem, e₆, writeW_bytes _ _ _ [0, 0, 3, 0] (by decide),
      writeBytes_append' _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; bv_omega)
        (by simp)]
    rfl

theorem wp_mov32r {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem readW_writeW_ne (m : Mem) {a b : Addr} (v : BitVec 64) (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  (Frame.writeW (Frame.refl [⟨b, 8⟩] m) (r := ⟨b, 8⟩) (List.mem_singleton_self _) v
    (contains_base (by decide))).readW (r := ⟨a, 8⟩)
    (contains_base (by decide)) (by simpa using h) (by decide)

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s => Inv s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0)) := by
  have io : ∀ {s : State}, s.wr = s₀.wr → ∀ d n : Nat, d + n ≤ 384 → InRegions s.wr (scr s₀ + BitVec.ofNat 64 d) n :=
    fun hw d n hd => by have := in_scr hp hw (a := d) (b := 0) (n := n) (by omega); simpa using this
  unfold prologue
  simp only [saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
  -- Saving our caller's registers.
  refine wp_store (a := scr s₀ + BitVec.ofNat 64 208) (by rw [ea_at, ofInt_natCast]) (io rfl 208 8 (by omega))
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofNat 64 216) (by rw [ea_at, g₁, ofInt_natCast])
    (io wr₁ 216 8 (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofNat 64 224) (by rw [ea_at, g₂, g₁, ofInt_natCast])
    (io (wr₂.trans wr₁) 224 8 (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  have g₃' : s₃.gpr = s₀.gpr := by rw [g₃, g₂, g₁]
  have mS : s₃.mem = ((s₀.mem.writeW (scr s₀ + BitVec.ofNat 64 208) (s₀.gpr .rbx)).writeW
      (scr s₀ + BitVec.ofNat 64 216) (s₀.gpr .rbp)).writeW (scr s₀ + BitVec.ofNat 64 224) (s₀.gpr .r13) := by
    rw [m₃, m₂, m₁, g₂, g₁]
  -- Our registers.
  refine wp_mov32r fun s₄ u₄ => wp_mov fun s₅ u₅ _ _ => wp_mov fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ =>
    wp_mov fun s₈ u₈ _ _ => wp_addi fun s₉ u₉ => ?_
  have hr : ∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r13 → r ≠ .rcx → r ≠ .rdi → s₉.gpr r = s₀.gpr r := by
    intro r h₁ h₂ h₃ h₄ h₅
    rw [u₉.other r h₅, u₈.other r h₅, u₇.other r h₄, u₆.other r h₂, u₅.other r h₁, u₄.other r h₃, g₃']
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂, rd₁]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂, wr₁]
  have mm₉ : s₉.mem = s₃.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have rcx₉ : s₉.gpr .rcx = scr s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₃']
  have rdi₉ : s₉.gpr .rdi = scr s₀ + 112 := by
    rw [u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₃']; rfl
  have rbx₉ : s₉.gpr .rbx = key s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, u₄.other _ (by decide), g₃']
  have rbp₉ : s₉.gpr .rbp = tP s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      u₅.other _ (by decide), u₄.other _ (by decide), g₃']
  have r13₉ : s₉.gpr .r13 = BitVec.ofNat 64 (nn s₀) := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, g₃']
    apply BitVec.eq_of_toNat_eq
    have := ((s₀.gpr .rdx).setWidth 32).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, nn]
  -- `U` and the padding.
  refine Proof.Hmac.X86_64.copy64_ok (by decide) (by decide) 0 144 4 _ s₉ _
    (fun j hj => by
      rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide), rd₉, wr₉]
      exact ⟨uR s₀, by simp [hp.rd], by rw [add_ofNat]; exact contains_offset (by omega) (by omega)⟩)
    (fun j hj => by rw [rcx₉, add_ofNat]; exact io wr₉ _ _ (by omega)) ?_ (by omega) fun s₁₀ g₁₀ rd₁₀ wr₁₀ m₁₀ => ?_
  · rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide), rcx₉]
    exact Region.Disjoint.sep hp.u_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega))
  refine padding_ok hp (by rw [g₁₀ _ (by decide), rcx₉]) (wr₁₀.trans wr₉) fun s₁₁ g₁₁ rd₁₁ wr₁₁ m₁₁ => ?_
  refine wp_test fun s₁₂ g₁₂ m₁₂ rd₁₂ wr₁₂ z₁₂ => WP.block_nil ?_
  have G : ∀ r, r ≠ .rax → s₁₂.gpr r = s₉.gpr r := fun r h => by rw [g₁₂, g₁₁ r h, g₁₀ r h]
  have G' : ∀ r ∈ [Reg.rsp, .r12, .r14, .r15], s₁₂.gpr r = s₀.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [G _ (by decide), hr _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hm : s₁₂.mem = writeBytes (writeBytes s₃.mem (scr s₀ + BitVec.ofNat 64 144) (bytesAt s₃.mem (uP s₀) 32))
      (scr s₀ + BitVec.ofNat 64 176) pad96 := by
    rw [m₁₂, m₁₁, m₁₀, rcx₉, hr .rsi (by decide) (by decide) (by decide) (by decide) (by decide), mm₉,
      show 8 * 4 = 32 from rfl]
    simp
  have inS : ∀ d n : Nat, d + n ≤ 384 → (scR s₀).Contains (scr s₀ + BitVec.ofNat 64 d) n :=
    fun d n h => contains_offset h (by omega)
  have F₃ : Frame [scR s₀] s₀.mem s₃.mem := by
    rw [mS]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (inS 208 8 (by omega))).writeW
      (List.mem_singleton_self _) _ (inS 216 8 (by omega)) |>.writeW (List.mem_singleton_self _) _ (inS 224 8 (by omega))
  have F : Frame [scR s₀] s₀.mem s₁₂.mem := by
    rw [hm]
    exact F₃.trans (writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact inS 144 32 (by omega))) |>.trans
      (writeBytes_frame _ _ _ (inS 176 32 (by omega)))
  have hsep : Mem.Sep (scr s₀ + BitVec.ofNat 64 144) 32 (scr s₀ + BitVec.ofNat 64 176) pad96.length :=
    Region.Disjoint.sep (scr_disj s₀ (a := 144) (m := 32) (b := 176) (n := 32) (by omega) (by omega) (by omega))
      (contains_base (Nat.le_refl _)) (contains_base (Nat.le_refl _))
  have hU : bytesAt s₁₂.mem (scr s₀ + 144) 32 = bytesAt s₀.mem (uP s₀) 32 := by
    show bytesAt s₁₂.mem (scr s₀ + BitVec.ofNat 64 144) 32 = _
    have := bytesAt_writeBytes_self s₃.mem (scr s₀ + BitVec.ofNat 64 144) (bytesAt s₃.mem (uP s₀) 32)
      (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [hm, bytesAt_writeBytes_sep _ _ hsep (by omega), this]
    exact frame_bytesAt F₃ (by simpa using hp.u_s) (by omega)
  have hT : bytesAt s₁₂.mem (tP s₀) 32 = bytesAt s₀.mem (tP s₀) 32 :=
    frame_bytesAt F (by simpa using hp.t_s) (by omega)
  have hS : ∀ {d : Nat}, 208 ≤ d → d + 8 ≤ 232 →
      s₁₂.mem.readW (scr s₀ + BitVec.ofNat 64 d) 64 = s₃.mem.readW (scr s₀ + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    rw [hm]
    let A : Region := ⟨scr s₀ + BitVec.ofNat 64 144, 32⟩
    let B : Region := ⟨scr s₀ + BitVec.ofNat 64 176, 32⟩
    have f₁ : Frame [A, B] s₃.mem (writeBytes s₃.mem (scr s₀ + BitVec.ofNat 64 144) (bytesAt s₃.mem (uP s₀) 32)) :=
      (writeBytes_frame _ _ _ (R := A) (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono (by simp)
    have f₂ : Frame [A, B] (writeBytes s₃.mem (scr s₀ + BitVec.ofNat 64 144) (bytesAt s₃.mem (uP s₀) 32))
        (writeBytes (writeBytes s₃.mem (scr s₀ + BitVec.ofNat 64 144) (bytesAt s₃.mem (uP s₀) 32))
          (scr s₀ + BitVec.ofNat 64 176) pad96) :=
      (writeBytes_frame _ _ _ (R := B) (contains_base (by decide))).mono (by simp)
    refine (f₁.trans f₂).readW (r := ⟨scr s₀ + BitVec.ofNat 64 d, 8⟩) (contains_base (Nat.le_refl _)) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_disj s₀ (by omega) (by omega) (by omega)
    · exact scr_disj s₀ (by omega) (by omega) (by omega)
  have d₁ : Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 208, 8⟩ ⟨scr s₀ + BitVec.ofNat 64 216, 8⟩ :=
    scr_disj s₀ (by omega) (by omega) (by omega)
  have d₂ : Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 208, 8⟩ ⟨scr s₀ + BitVec.ofNat 64 224, 8⟩ :=
    scr_disj s₀ (by omega) (by omega) (by omega)
  have d₃ : Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 216, 8⟩ ⟨scr s₀ + BitVec.ofNat 64 224, 8⟩ :=
    scr_disj s₀ (by omega) (by omega) (by omega)
  refine ⟨⟨⟨by rw [rd₁₂, rd₁₁, rd₁₀, rd₉], by rw [wr₁₂, wr₁₁, wr₁₀, wr₉], by rw [G _ (by decide), rbx₉],
    by rw [G _ (by decide), rbp₉], by rw [G _ (by decide), rcx₉], by rw [G _ (by decide), rdi₉],
    G' _ (by simp), G' _ (by simp), G' _ (by simp), G' _ (by simp), F.mono (by simp)⟩,
    by rw [G _ (by decide), r13₉], ?_, ?_, (Nat.le_refl _), by rw [hU, hT]⟩, ?_⟩
  · intro p hp'
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · rw [hS (by simp) (by simp), mS, readW_writeW_ne _ _ d₂, readW_writeW_ne _ _ d₁, Mem.readW_writeW_self64]
    · rw [hS (by simp) (by simp), mS, readW_writeW_ne _ _ d₃, Mem.readW_writeW_self64]
    · rw [hS (by simp) (by simp), mS, Mem.readW_writeW_self64]
  · rw [hm]
    have := bytesAt_writeBytes_self (writeBytes s₃.mem (scr s₀ + BitVec.ofNat 64 144) (bytesAt s₃.mem (uP s₀) 32))
      (scr s₀ + BitVec.ofNat 64 176) pad96 (by decide)
    exact this
  · rw [z₁₂, g₁₁ .r13 (by decide), g₁₀ .r13 (by decide), r13₉, BitVec.and_self,
      Proof.Sha256.X86_64.Stream.ofNat_beq_zero (by have := ((s₀.gpr .rdx).setWidth 32).isLt; simp [nn]; omega)]

/-! ## Correctness -/

theorem correct {f : Callee} (hf : f.Ok) {s₀ : State} (hp : Pre s₀) :
    WP isa (iterate f) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Pbkdf2.iterateSha256X86_64.post s₀ s' := by
  unfold iterate
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h, hz⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hf hp h hz) fun s₂ h₂ => epilogue_ok hp h₂)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rcx => 0x3000 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 192⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 384⟩]

/-- `iterate f` is verified if it is constant time and never loads MXCSR. -/
theorem iterate_ok {f : Callee} (hf : f.Ok)
    (hm : (iterate f).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (hs : Proof.Pbkdf2.iterateSha256X86_64.pre s) :
    ∃ t s', Exec isa (iterate f) s t s' ∧ abiPreserved s s' ∧
      Proof.Pbkdf2.iterateSha256X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct hf (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩

end VG.Proof.Pbkdf2.X86_64.Iterate
