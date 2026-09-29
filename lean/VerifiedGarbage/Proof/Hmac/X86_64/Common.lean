import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Impl.Hmac.X86_64
import VerifiedGarbage.Spec.Hmac
import VerifiedGarbage.Proof.Sha256.X86_64.Contract

/-!
# HMAC-SHA-256 on x86-64: common lemmas

Untrusted: everything here is checked by Lean. Words copied between memory
regions, and bytes and hash values read back.
-/

namespace VG.Proof.Hmac

open Spec.Hmac
open Spec.Sha256 (Repr bytesAt)

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_hmac_sha256_init(inner: *mut [u8; 96], outer: *mut [u8; 96], key: *const u8, key_len: usize, scratch: *mut [u64; 20])`,
for a key of at most 64 bytes (the SHA-256 block size): makes the streaming
state at `inner` represent `K₀ ⊕ ipad` and the one at `outer` represent
`K₀ ⊕ opad`, for the key `K₀` made of the `key_len` bytes at `key`.

The code may read `key` (`key_len` bytes) and read and write `inner` and
`outer` (96 bytes each) and `scratch` (160 bytes, whose contents on exit are
unspecified). These may not overlap each other, nor the return address on
the stack. The pointers and `key_len` are public; the key is secret. -/
def initSha256X86_64 : Contract X86_64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, 96⟩
    let outer : Region := ⟨s.gpr .rsi, 96⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 160⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    (s.gpr .rcx).toNat ≤ 64 ∧ s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch
  post s s' :=
    let k0 := blockKey sha256 (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86-64 contract for
`vg_hmac_sha256_finalize(inner: *mut [u8; 96], outer: *const [u8; 96], count: u64, scratch: *mut [u64; 30])`:
if, for a 64-byte key `K₀` and a text, the streaming state at `inner`
represents `(K₀ ⊕ ipad) ‖ text`, of `count` bytes (modulo 2⁶⁴), and the one at
`outer` represents `K₀ ⊕ opad`, leaves the HMAC-SHA-256 of the text under
`K₀` in bytes 176 to 207 of `scratch`.

The MAC is left in `scratch` rather than written through a pointer of its
own so that the code can address every region from the two pointers it
keeps in registers across the inlined SHA-256 finalizations.

The code may read `outer` (96 bytes), and read and write `inner` (96 bytes,
whose contents on exit are unspecified) and `scratch` (240 bytes, whose
contents on exit are unspecified apart from the MAC). These may not overlap
each other, nor the return address on the stack. The pointers and `count`
are public; the states are secret. -/
def finalizeSha256X86_64 : Contract X86_64.isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, 96⟩
    let outer : Region := ⟨s.gpr .rsi, 96⟩
    let scratch : Region := ⟨s.gpr .rcx, 240⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [outer] ∧ s.wr = [inner, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint scratch
  post s s' := ∀ k0 text, k0.length = 64 →
    Repr s.mem (s.gpr .rdi) (xorPad k0 ipad ++ text) →
    s.gpr .rdx = BitVec.ofNat 64 (64 + text.length) →
    Repr s.mem (s.gpr .rsi) (xorPad k0 opad) →
    bytesAt s'.mem (s.gpr .rcx + 176) 32 = hmacBlockKey sha256 k0 text
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Hmac

namespace VG.Proof.Hmac.X86_64
open VG VG.X86_64
open VG.Proof.Sha256.Stream (writeBytes write_eq_writeBytes writeBytes_append writeBytes_nil)
open VG.Spec.Sha256 (bytesAt)

theorem extractLsb'_read (m : Mem) (a : Addr) {n j : Nat} (hj : j < n) :
    (m.read a n).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    simp only [Mem.read]
    cases j with
    | zero =>
      rw [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      ext i hi
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
      simp [hi]
    | succ j =>
      rw [show a + BitVec.ofNat 64 (j + 1) = a + 1 + BitVec.ofNat 64 j by bv_omega,
        ← ih (a := a + 1) (by omega)]
      ext i hi
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append,
        show ¬ (8 * (j + 1) + i < 8) by omega, ite_false]
      congr 1; omega

/-- Writing a word read from memory writes its bytes. -/
theorem writeW_readW (m m' : Mem) (d s : Addr) (n : Nat) :
    m.writeW d (m'.readW s (8 * n)) = writeBytes m d (bytesAt m' s n) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show 8 * n / 8 = n by omega, BitVec.setWidth_eq, BitVec.setWidth_eq, write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => extractLsb'_read _ _ (List.mem_range.mp hj)

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_writeBytes_sep (m : Mem) {p q : Addr} {n : Nat} (xs : List Byte)
    (h : Mem.Sep p n q xs.length) (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m q xs) p n = bytesAt m p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  simp only [writeBytes]
  split
  · exact absurd ‹_› (h _ (by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hi))
  · rfl

/-- One more word copied from `A` to `B`. -/
theorem copy_mem (m : Mem) (A B : Addr) (n w : Nat)
    (hsep : Mem.Sep A (w * n + w) B (w * n + w)) (hlt : w * n + w < 2 ^ 64) :
    (writeBytes m B (bytesAt m A (w * n))).writeW (B + BitVec.ofNat 64 (w * n))
      ((writeBytes m B (bytesAt m A (w * n))).readW (A + BitVec.ofNat 64 (w * n)) (8 * w)) =
      writeBytes m B (bytesAt m A (w * n + w)) := by
  rw [writeW_readW, bytesAt_writeBytes_sep]
  · rw [bytesAt_add]
    have := writeBytes_append m B (bytesAt m A (w * n)) (bytesAt m (A + BitVec.ofNat 64 (w * n)) w)
      (by simp [bytesAt]; omega)
    simpa [bytesAt] using this
  · intro x hx hy
    simp only [bytesAt, List.length_map, List.length_range] at hy
    apply hsep x _ (by omega)
    rw [show x - A = (x - (A + BitVec.ofNat 64 (w * n))) + BitVec.ofNat 64 (w * n) by bv_omega,
      BitVec.toNat_add, Proof.Sha256.X86_64.toNat_ofNat_lt (by omega)]
    have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (w * n))).toNat + w * n) (2 ^ 64)
    omega
  · omega

open VG.Impl.Sha256.X86_64 (at_)
open VG.Impl.Hmac.X86_64 (cp32 cp64)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov32m wp_store32 wp_movm wp_store)

theorem ea_off (s : State) (b : Reg) (o j : Nat) :
    s.ea (at_ b (o + j)) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  simp only [State.ea, at_, Proof.Sha256.X86_64.ofInt_natCast, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_zero (m : Mem) (p : Addr) : bytesAt m p 0 = [] := rfl

theorem copy32_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp32 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [cp32, List.cons_append, List.nil_append]
    refine wp_mov32m (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, g₁ _ hs]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_store32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, u₂.other _ hd, g₁ _ hd]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (fun r hr => by rw [g₃, u₂.other r hr, g₁ r hr])
        (by rw [rd₃, u₂.rd, rd₁]) (by rw [wr₃, u₂.wr, wr₁]) ?_
    rw [m₃, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega)

theorem copy64_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (8 * k)) 8) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (8 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (8 * n) →
    8 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (8 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (cp64 src dst o₁ o₂) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [cp64, List.cons_append, List.nil_append]
    refine wp_movm (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (8 * n))
      (by rw [ea_off, g₁ _ hs]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_store (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (8 * n))
      (by rw [ea_off, u₂.other _ hd, g₁ _ hd]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (fun r hr => by rw [g₃, u₂.other r hr, g₁ r hr])
        (by rw [rd₃, u₂.rd, rd₁]) (by rw [wr₃, u₂.wr, wr₁]) ?_
    rw [m₃, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 8 (by rwa [← Nat.mul_succ]) (by omega)

end VG.Proof.Hmac.X86_64

namespace VG.Proof.Hmac.X86_64
open VG VG.X86_64
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Spec.Sha256 (bytesAt stateAt)

theorem read_congr₂ {m m' : Mem} {a b : Addr} {n : Nat}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (b + BitVec.ofNat 64 i)) : m.read a n = m'.read b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega)
    rwa [show a + BitVec.ofNat 64 (i + 1) = a + 1 + BitVec.ofNat 64 i by bv_omega,
      show b + BitVec.ofNat 64 (i + 1) = b + 1 + BitVec.ofNat 64 i by bv_omega] at this

/-- A hash value is determined by its 32 bytes. -/
theorem stateAt_eq_of_bytes {m m' : Mem} {p q : Addr}
    (h : ∀ i < 32, m (p + BitVec.ofNat 64 i) = m' (q + BitVec.ofNat 64 i)) : stateAt m p = stateAt m' q := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Mem.readW]
  congr 1
  refine read_congr₂ fun i hi => ?_
  have := h (4 * j + i) (by omega)
  rwa [show p + BitVec.ofNat 64 (4 * j + i) = p + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 i by
      simp only [BitVec.ofNat_add, BitVec.add_assoc],
    show q + BitVec.ofNat 64 (4 * j + i) = q + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 i by
      simp only [BitVec.ofNat_add, BitVec.add_assoc]] at this

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < xs.length)
    (hl : xs.length < 2 ^ 64) : writeBytes m q xs (q + BitVec.ofNat 64 i) = xs.getD i 0 := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q (show i < 2 ^ 64 by omega), hi, ite_true]

theorem writeBytes_other (m : Mem) (q : Addr) (xs : List Byte) {x : Addr}
    (hx : ¬ (x - q).toNat < xs.length) : writeBytes m q xs x = m x := by
  simp only [writeBytes, hx, ite_false]

theorem bytesAt_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (hl : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [writeBytes_at _ _ _ h₂ hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

end VG.Proof.Hmac.X86_64
