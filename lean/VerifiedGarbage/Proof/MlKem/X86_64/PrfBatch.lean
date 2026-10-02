import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.MlKem.X86_64.Lay
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlKem.X86_64.Rel

/-!
# ML-KEM on x86-64: four instances of `PRF₂` at once

`Prf4.batch N₀ m o wl` (`Impl/MlKem/X86_64/Frag.lean`) writes `PRF₂(σ, N₀ +
k)` to `scratch + o + 128 k` for each `k < m`, with `σ` at `scratch + 1056`
and `scratch` in `rbx` (`batch_ok`). The input `σ ‖ N` is one block, whose
padded state (`P0`) the code writes into each of the four states, byte by byte
as `vg_mlkem_sample_ntt4_avx2` does (`S4Absorb.lean`); the permutation is
`permute4` (`permute4_ok`), and the output the first 128 bytes of each
permuted state (`prf_byte`).
-/

namespace VG.Proof.MlKem.X86_64.Prf4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Prf4
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF RC bytesAt)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF)
open VG.Proof.MlKem (padded prf_eq prf_length)
open VG.Proof.Sha3.X86_64.X4 (q4 la ba la_byte Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok wp_vmovq wp_vbcast
  wp_vst wp_vxor readW_write256 q4_ymm)
open VG.Proof.MlKem.X86_64.S4 (bytes_write wb_in wb_out byte_setWidth vz_ok)
open VG.Proof.Sha3.X86_64 (wp_movi64 wp_movm wp_store wp_store8 wp_mov32i wp_nil)

/-! ## The padded input and the output -/

/-- The state whose permutation is the padded `σ ‖ n` (one block of SHAKE256). -/
def P0 (σ : List Byte) (n : Byte) : Spec.Sha3.State :=
  xorByte (xorByte (Rep 136 (σ ++ [n])) 33 0x1f) 135 0x80

theorem padded_P0 {σ : List Byte} (h : σ.length = 32) (n : Byte) :
    padded 136 Spec.Sha3.shakeSuffix (σ ++ [n]) = keccakF (P0 σ n) := by
  rw [padded, absorb_pad (by decide) (by decide), List.length_append, h]; rfl

/-- Byte `q` of the padded state. -/
abbrev PF (σ : List Byte) (n : Byte) (q : Nat) : Byte :=
  if q < 32 then σ.getD q 0 else if q = 32 then n else if q = 33 then 0x1f else if q = 135 then 0x80 else 0

theorem byteOf_P0 {σ : List Byte} (h : σ.length = 32) (n : Byte) {q : Nat} (hq : q < 200) :
    byteOf (P0 σ n) q = PF σ n q := by
  have hz : byteOf Spec.Sha3.zero q = 0 := by
    simp only [byteOf, Spec.Sha3.zero, getElem!_pos (Vector.replicate 25 (0 : BitVec 64)) (q / 8) (by omega),
      Vector.getElem_replicate]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  have hl : (σ ++ [n]).length = 33 := by rw [List.length_append, h]; rfl
  have ha : Spec.Sha3.absorb 136 (σ ++ [n]) = Spec.Sha3.zero := by simp [Spec.Sha3.absorb, hl]
  have hr : byteOf (Rep 136 (σ ++ [n])) q = (σ ++ [n]).getD q 0 := by
    rw [Rep, ha, byteOf_xorBytes _ _ hq, hz, hl, show 136 * (33 / 136) = 0 from rfl, List.drop_zero]
    exact BitVec.zero_xor
  have hg : (σ ++ [n]).getD q 0 = if q < 32 then σ.getD q 0 else if q = 32 then n else 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append]
    by_cases e1 : q < 32
    · rw [ifp (show q < σ.length by omega), ifp e1, List.getD_eq_getElem?_getD]
    · rw [ifn (show ¬ q < σ.length by omega), ifn e1, h]
      by_cases e2 : q = 32
      · subst e2; rw [ifp rfl]; rfl
      · rw [ifn e2, List.getElem?_singleton, ifn (by omega)]; rfl
  rw [P0, byteOf_xorByte _ _ _ hq, byteOf_xorByte _ _ _ hq, hr, hg, PF]
  by_cases e1 : q < 32
  · rw [ifn (show ¬ q = 135 by omega), ifn (show ¬ q = 33 by omega), ifp e1, ifp e1]
  · rw [ifn e1, ifn e1]
    by_cases e2 : q = 32
    · rw [ifn (show ¬ q = 135 by omega), ifn (show ¬ q = 33 by omega), ifp e2, ifp e2]
    · rw [ifn e2, ifn e2]
      by_cases e3 : q = 33
      · rw [ifn (show ¬ q = 135 by omega), ifp e3, ifp e3]; exact BitVec.zero_xor
      · rw [ifn e3, ifn e3]
        by_cases e4 : q = 135
        · rw [ifp e4, ifp e4]; exact BitVec.zero_xor
        · rw [ifn e4, ifn e4]

/-- Byte `j` of `PRF₂(σ, n)`: of the permuted padded state. -/
theorem prf_byte {σ : List Byte} (h : σ.length = 32) (n : Byte) {j : Nat} (hj : j < 128) :
    (prf 2 σ n)[j]'(by rw [prf_length]; exact hj) = byteOf (keccakF (P0 σ n)) j := by
  have e := Proof.Sha3.squeezeFrom_getElem (rate := 136) (by decide) (by decide)
    (padded 136 Spec.Sha3.shakeSuffix (σ ++ [n])) (pos := 0) (d := 64 * 2) (i := j) (by omega)
  rw [List.getElem_of_eq (prf_eq 2 σ n), e, show (0 + j) / 136 = 0 by omega, show (0 + j) % 136 = j by omega,
    padded_P0 h]
  rfl

/-- `PRF₂(σ, n)` in memory, from its bytes. -/
theorem bytes_prf {m : Mem} {p : Addr} {σ : List Byte} (h : σ.length = 32) {n : Byte}
    (hb : ∀ j < 128, m (p + BitVec.ofNat 64 j) = byteOf (keccakF (P0 σ n)) j) :
    bytesAt m p 128 = prf 2 σ n := by
  apply List.ext_getElem (by rw [prf_length]; simp [bytesAt])
  intro j h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  rw [prf_byte h n h₁]
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  exact hb j h₁

/-! ## Where the code works -/

section
variable (b : Addr) (wl o m : Nat)
/-- The four states, from lane `wl` of `scratch` (at `b`). -/
abbrev sP : Addr := b + BitVec.ofNat 64 (32 * wl)
/-- `σ`. -/
abbrev sS : Addr := b + BitVec.ofNat 64 (oG + 32)
/-- The working space. -/
abbrev wR : Region := ⟨sP b wl, 2368⟩
/-- The outputs. -/
abbrev oR : Region := ⟨b + BitVec.ofNat 64 o, 128 * m⟩
abbrev sR : Region := ⟨sS b, 32⟩
end

/-- What `batch N₀ m o wl` needs of the state `s₀` it starts from, with
`scratch` at `b`. -/
structure BPre (b : Addr) (wl o m : Nat) (s₀ : State) : Prop where
  rbx : s₀.gpr .rbx = b
  w : InRegions s₀.wr (sP b wl) 2368
  out : InRegions s₀.wr (b + BitVec.ofNat 64 o) (128 * m)
  sig : InRegions (s₀.rd ++ s₀.wr) (sS b) 32
  dWO : (wR b wl).Disjoint (oR b o m)
  dWS : (wR b wl).Disjoint (sR b)
  dOS : (oR b o m).Disjoint (sR b)
  hm : m ≤ 4
  small : 32 * wl + 2368 < 2 ^ 31

/-- Between the pieces of `batch`, from `s₀`. -/
structure BEnv (b : Addr) (wl o m : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cs : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  frame : Frame [wR b wl, oR b o m] s₀.mem s.mem

theorem rax_ncs : ∀ r ∈ calleeSaved, r ≠ .rax := by decide

/-- `σ`, from `s₀`. -/
abbrev sig (b : Addr) (s₀ : State) : List Byte := bytesAt s₀.mem (sS b) 32

theorem sig_length (b : Addr) (s₀ : State) : (sig b s₀).length = 32 := by simp [bytesAt]

theorem sig_getD (b : Addr) (s₀ : State) {q : Nat} (hq : q < 32) :
    (sig b s₀).getD q 0 = s₀.mem (sS b + BitVec.ofNat 64 q) := by
  simp [bytesAt, hq]

/-- An address of the working space. -/
theorem at_w (b : Addr) {wl x d : Nat} (h : x = 32 * wl + d) :
    b + BitVec.ofNat 64 x = sP b wl + BitVec.ofNat 64 d := by
  rw [sP, Offset.add_add, h]

section
variable {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀)
include hp

theorem BEnv.rbx {s : State} (he : BEnv b wl o m s₀ s) : s.gpr .rbx = b := (he.cs .rbx (by decide)).trans hp.rbx

omit hp in
theorem BEnv.refl : BEnv b wl o m s₀ s₀ := ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem in_w {s : State} (he : BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 2368) :
    InRegions s.wr (sP b wl + BitVec.ofNat 64 a) n := by
  rw [he.wr]; exact inRegions_sub hp.w h (by decide)

theorem in_w' {s : State} (he : BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 2368) :
    InRegions (s.rd ++ s.wr) (sP b wl + BitVec.ofNat 64 a) n :=
  VG.Proof.Sha3.X86_64.X4.in_append (in_w hp he h)

theorem in_o {s : State} (he : BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 128 * m) :
    InRegions s.wr (b + BitVec.ofNat 64 o + BitVec.ofNat 64 a) n := by
  rw [he.wr]; exact inRegions_sub hp.out h (by have := hp.hm; omega)

theorem in_s {s : State} (he : BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 32) :
    InRegions (s.rd ++ s.wr) (sS b + BitVec.ofNat 64 a) n := by
  rw [he.rd, he.wr]; exact inRegions_sub hp.sig h (by decide)

/-- `σ` is not written. -/
theorem sig_readW {s : State} (he : BEnv b wl o m s₀ s) {i : Nat} (hi : i < 4) :
    s.mem.readW (sS b + BitVec.ofNat 64 (8 * i)) 64 = s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * i)) 64 :=
  he.frame.readW (r := sR b) (Offset.contains_base _ (by omega) (by omega))
    (by simpa using ⟨hp.dWS.symm, hp.dOS.symm⟩) (by decide)

omit hp in
/-- A write within the working space. -/
theorem BEnv.write {s s' : State} (he : BEnv b wl o m s₀ s) {e n : Nat} (hn : e + n ≤ 2368)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 e) v) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : BEnv b wl o m s₀ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, fun r hr => (hg r hr).trans (he.cs r hr), ?_⟩
  rw [hm]
  exact he.frame.writeW (List.mem_cons_self ..) v (by
    rw [show 8 * n / 8 = n by omega]; exact Offset.contains_base _ hn (by omega))

/-- A write within the outputs. -/
theorem BEnv.writeO {s s' : State} (he : BEnv b wl o m s₀ s) {e n : Nat} (hn : e + n ≤ 128 * m)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (b + BitVec.ofNat 64 o + BitVec.ofNat 64 e) v)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    BEnv b wl o m s₀ s' := by
  have := hp.hm
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, fun r hr => (hg r hr).trans (he.cs r hr), ?_⟩
  rw [hm]
  exact he.frame.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) v (by
    rw [show 8 * n / 8 = n by omega]; exact Offset.contains_base _ hn (by omega))

end

/-! ## The round constants -/

/-- The table of the round constants, from lane 50 of the states. -/
abbrev Tbl (p : Addr) (n : Nat) (mem : Mem) : Prop := ∀ r < n, ∀ k < 4, mem.readW (la p (50 + r) k) 64 = RC r

theorem rc_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {r : Nat} (hr : r < 24) {s : State}
    (h : BEnv b wl o m s₀ s ∧ Tbl (sP b wl) r s.mem) :
    WP isa (.block [.movImm64 .rax (RC r), .vop (.vmovq .xmm0 .rax),
      .vop (.vpbroadcastq .l256 .xmm0 .xmm0), Impl.Sha3.X86_64.X4.st .rbx (wl + 50 + r) .xmm0]) s
      (fun s' => BEnv b wl o m s₀ s' ∧ Tbl (sP b wl) (r + 1) s'.mem) := by
  obtain ⟨he, ht⟩ := h
  have hbx := he.rbx hp
  have := hp.small
  refine wp_movi64 fun s₁ u₁ => wp_vmovq fun s₂ u₂ => wp_vbcast fun s₃ u₃ =>
    wp_vst (a := sP b wl + BitVec.ofNat 64 (32 * (50 + r)))
      (by rw [VG.Proof.Sha3.X86_64.ea_at, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hbx]; exact at_w b (by omega))
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact in_w hp he (by omega))
      fun s₄ g₄ _ m₄ r₄ w₄ => wp_nil ?_
  have hv : ∀ k < 4, q4 s₃ .xmm0 k = RC r := fun k hk => by
    rw [u₃.val k hk, u₂.val 0 (by decide), ite_eq_left rfl, u₁.gpr]
  have hm : s₄.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 (32 * (50 + r))) (s₃.ymm .xmm0) := by
    rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨he.write (n := 32) (by omega) hm (by rw [r₄, u₃.rd, u₂.rd, u₁.rd]) (by rw [w₄, u₃.wr, u₂.wr, u₁.wr])
    fun g hg => by rw [g₄, u₃.gpr, u₂.gpr, u₁.other g (rax_ncs g hg)], fun r' hr' k hk => ?_⟩
  rw [hm]
  by_cases e : r' = r
  · subst e
    rw [la, ← Offset.add_add, readW_write256 _ _ _ hk, q4_ymm _ _ hk, hv k hk]
  · have e := readW_writeW_off s.mem (sP b wl) (s₃.ymm .xmm0) (d := 32 * (50 + r') + 8 * k)
      (e := 32 * (50 + r)) (n := 8) (by omega) (by omega) (by omega)
    exact e.trans (ht r' (by omega) k hk)

theorem rcTable_eq (wl : Nat) : Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50) = (List.range 24).flatMap fun r =>
    [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      Impl.Sha3.X86_64.X4.st .rbx (wl + 50 + r) .xmm0] := rfl

theorem rc_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {s : State}
    (he : BEnv b wl o m s₀ s) :
    WP isa (.block (Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50))) s
      (fun s' => BEnv b wl o m s₀ s' ∧ Tbl (sP b wl) 24 s'.mem) := by
  rw [rcTable_eq]
  exact wp_range_flatMap (M := isa) (fun r s => BEnv b wl o m s₀ s ∧ Tbl (sP b wl) r s.mem)
    (fun r s hr h => rc_step hp hr h) 24 (Nat.le_refl _) s ⟨he, fun _ h => absurd h (by omega)⟩

/-! ## The padded inputs, byte by byte -/

/-- The four states at `p` hold `F`. -/
def SB (p : Addr) (mem : Mem) (F : Nat → Nat → Byte) : Prop := ∀ k < 4, ∀ q < 200, mem (ba p k q) = F k q

/-- While the states are written, after the table (in `m₁`). -/
structure AI (b : Addr) (wl o m : Nat) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  env : BEnv b wl o m s₀ s
  fr : Frame [⟨sP b wl, 800⟩] m₁ s.mem

theorem AI.write {b : Addr} {wl o m : Nat} {s₀ : State} {m₁ : Mem} {s s' : State}
    (h : AI b wl o m s₀ m₁ s) {e n : Nat} (hn : e + n ≤ 800)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 e) v) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : AI b wl o m s₀ m₁ s' :=
  ⟨h.env.write (by omega) hm hrd hwr hg, by
    rw [hm]
    exact h.fr.writeW (List.mem_singleton_self _) v (by
      rw [show 8 * n / 8 = n by omega]; exact Offset.contains_base _ hn (by omega))⟩

/-- A step that writes no memory and no callee-saved register. -/
theorem AI.keep {b : Addr} {wl o m : Nat} {s₀ : State} {m₁ : Mem} {s s' : State}
    (h : AI b wl o m s₀ m₁ s) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : AI b wl o m s₀ m₁ s' :=
  h.write (e := 0) (n := 0) (v := 0) (by omega) (by rw [hm]; funext x; simp [Mem.writeW, Mem.write]) hrd hwr hg

/-! ### Zeroing -/

structure ZInv (b : Addr) (wl o m : Nat) (s₀ : State) (m₁ : Mem) (n : Nat) (s : State) : Prop where
  ai : AI b wl o m s₀ m₁ s
  x0 : ∀ k < 4, q4 s .xmm0 k = 0
  bytes : ∀ k < 4, ∀ q < 200, q / 8 < n → s.mem (ba (sP b wl) k q) = 0

theorem zero_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {i : Nat}
    (hi : i < 25) {s : State} (h : ZInv b wl o m s₀ m₁ i s) :
    WP isa (.block [Impl.Sha3.X86_64.X4.st .rbx (wl + i) .xmm0]) s (ZInv b wl o m s₀ m₁ (i + 1)) := by
  have := hp.small
  refine wp_vst (a := sP b wl + BitVec.ofNat 64 (32 * i))
    (by rw [VG.Proof.Sha3.X86_64.ea_at, h.ai.env.rbx hp]; exact at_w b (by omega))
    (in_w hp h.ai.env (by omega)) fun s' g' q' m' r' w' => wp_nil ?_
  refine ⟨h.ai.write (e := 32 * i) (n := 32) (by omega) m' r' w' fun r _ => by rw [g'],
    fun k hk => by rw [q', h.x0 k hk], fun k hk q hq hn => ?_⟩
  rw [m']
  have hb := bytes_write (m := s.mem) (p := sP b wl) (F := fun k q => s.mem (ba (sP b wl) k q))
    (fun _ _ _ _ => rfl) (s.ymm .xmm0) (e := 32 * i) (by decide) (by omega) hk hq
  rw [hb]
  split
  · rename_i hc
    simp only [S4.off4] at hc ⊢
    rw [show 8 * (32 * (q / 8) + 8 * k + q % 8 - 32 * i) = 64 * k + 8 * (q % 8) by omega,
      ← extract_extract (s.ymm .xmm0) (64 * k) 64 (8 * (q % 8)) 8 (by omega), q4_ymm _ _ hk, h.x0 k hk]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · rename_i hc
    simp only [S4.off4] at hc
    exact h.bytes k hk q hq (by omega)

theorem zero_eq (wl : Nat) : zero wl = Impl.Sha3.X86_64.X4.vb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 25).flatMap fun i => [Impl.Sha3.X86_64.X4.st .rbx (wl + i) .xmm0] := rfl

theorem zero_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {s : State}
    (h : AI b wl o m s₀ m₁ s) :
    WP isa (.block (zero wl)) s (fun s' => AI b wl o m s₀ m₁ s' ∧ SB (sP b wl) s'.mem fun _ _ => 0) := by
  rw [zero_eq]
  refine wp_vxor fun s₁ u₁ => WP.mono (wp_range_flatMap (M := isa) (ZInv b wl o m s₀ m₁)
    (fun i s hi h => zero_step hp hi h) 25 (Nat.le_refl _) s₁
    ⟨h.keep u₁.mem u₁.rd u₁.wr fun r _ => by rw [u₁.gpr],
      fun k hk => by rw [u₁.val k hk, BitVec.xor_self]; rfl, fun _ _ _ _ h => absurd h (by omega)⟩)
    fun s' h' => ⟨h'.ai, fun k hk q hq => h'.bytes k hk q hq (by omega)⟩

/-! ### `σ` -/

/-- The states after the first `I` lanes of `σ` (and the first `K` states of lane `I`). -/
def GF (b : Addr) (s₀ : State) (I K : Nat) (k q : Nat) : Byte :=
  if q < 8 * I ∨ (q / 8 = I ∧ k < K) then s₀.mem (sS b + BitVec.ofNat 64 q) else 0

theorem sig_store {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {I K : Nat}
    (hI : I < 4) (hK : K < 4) {s : State}
    (h : AI b wl o m s₀ m₁ s ∧ s.gpr .rax = s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * I)) 64 ∧
      SB (sP b wl) s.mem (GF b s₀ I K)) :
    WP isa (.block [.store (at_ .rbx (32 * (wl + I) + 8 * K)) .rax]) s (fun s' => AI b wl o m s₀ m₁ s' ∧
      s'.gpr .rax = s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * I)) 64 ∧ SB (sP b wl) s'.mem (GF b s₀ I (K + 1))) := by
  obtain ⟨ha, hx, hb⟩ := h
  have := hp.small
  refine wp_store (a := sP b wl + BitVec.ofNat 64 (32 * I + 8 * K))
    (by rw [ea_at, ha.env.rbx hp]; exact at_w b (by omega)) (in_w hp ha.env (by omega))
    fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 (32 * I + 8 * K))
      (s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * I)) 64) := by rw [m₂, hx]
  refine ⟨ha.write (n := 8) (by omega) hm r₂ w₂ fun r _ => by rw [g₂], by rw [g₂, hx], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega) hk hq]
  simp only [S4.off4]
  by_cases hc : 32 * I + 8 * K ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 32 * I + 8 * K + 64 / 8
  · have hk' : k = K := by omega
    have hq' : q / 8 = I := by omega
    subst hk'
    rw [ifp hc, GF, ifp (.inr ⟨hq', by omega⟩),
      show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * I + 8 * k)) = 8 * (q % 8) by omega,
      byte_readW _ _ (by omega), Offset.add_add, show 8 * I + q % 8 = q by omega]
  · rw [ifn hc, GF, GF]
    by_cases hc' : q < 8 * I ∨ (q / 8 = I ∧ k < K)
    · rw [ifp hc', ifp (by omega)]
    · rw [ifn hc', ifn (by omega)]

theorem sig_lane {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {I : Nat}
    (hI : I < 4) {s : State} (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (GF b s₀ I 0)) :
    WP isa (.block (.mov .rax (.mem (at_ .rbx (oG + 32 + 8 * I))) ::
      (List.range 4).flatMap fun k => [.store (at_ .rbx (32 * (wl + I) + 8 * k)) .rax])) s
      (fun s' => AI b wl o m s₀ m₁ s' ∧ SB (sP b wl) s'.mem (GF b s₀ (I + 1) 0)) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movm (a := sS b + BitVec.ofNat 64 (8 * I)) (by rw [ea_at, ha.env.rbx hp, Offset.add_add])
    (in_s hp ha.env (by omega)) fun s₁ u₁ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => AI b wl o m s₀ m₁ s ∧
      s.gpr .rax = s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * I)) 64 ∧ SB (sP b wl) s.mem (GF b s₀ I K))
    (fun K s hK h => sig_store hp hI hK h) 4 (Nat.le_refl _) s₁
    ⟨ha.keep u₁.mem u₁.rd u₁.wr fun r hr => u₁.other r (rax_ncs r hr), by
      rw [u₁.gpr, sig_readW hp ha.env hI], by rw [u₁.mem]; exact hb⟩) fun s' ⟨ha', _, hb'⟩ =>
    ⟨ha', fun k hk q hq => ?_⟩
  rw [hb' k hk q hq, GF, GF]
  by_cases hc : q < 8 * I ∨ (q / 8 = I ∧ k < 4)
  · rw [ifp hc, ifp (by omega)]
  · rw [ifn hc, ifn (by omega)]

theorem sigLanes_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {s : State}
    (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem fun _ _ => 0) :
    WP isa (.block (sigLanes wl)) s (fun s' => AI b wl o m s₀ m₁ s' ∧ SB (sP b wl) s'.mem (GF b s₀ 4 0)) :=
  wp_range_flatMap (M := isa) (fun I s => AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (GF b s₀ I 0))
    (fun I s hI h => sig_lane hp hI h) 4 (Nat.le_refl _) s
    ⟨h.1, fun k hk q hq => by rw [h.2 k hk q hq, GF, ifn (by omega)]⟩

/-! ### The indices and the padding -/

/-- The byte `c` (in `rax`) to byte `q₀` of state `K`. -/
theorem cbyte_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem}
    {F : Nat → Nat → Byte} {K q₀ : Nat} (hK : K < 4) (hq₀ : q₀ < 200) {c : Byte} {s : State}
    (hax : s.gpr .rax = c.setWidth 64) (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem F) :
    WP isa (.block [.store8 (at_ .rbx (32 * (wl + q₀ / 8) + 8 * K + q₀ % 8)) .rax]) s
      (fun s' => AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        SB (sP b wl) s'.mem fun k q => if k = K ∧ q = q₀ then c else F k q) := by
  obtain ⟨ha, hb⟩ := h
  have := hp.small
  refine wp_store8 (a := sP b wl + BitVec.ofNat 64 (32 * (q₀ / 8) + 8 * K + q₀ % 8))
    (by rw [ea_at, ha.env.rbx hp]; exact at_w b (by omega)) (in_w hp ha.env (by omega))
    fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 (32 * (q₀ / 8) + 8 * K + q₀ % 8)) c := by
    rw [m₂, hax, byte_setWidth]
  refine ⟨ha.write (n := 1) (by omega) hm r₂ w₂ fun r _ => by rw [g₂], by rw [g₂], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by omega) hk hq]
  simp only [S4.off4]
  by_cases hc : 32 * (q₀ / 8) + 8 * K + q₀ % 8 ≤ 32 * (q / 8) + 8 * k + q % 8 ∧
      32 * (q / 8) + 8 * k + q % 8 < 32 * (q₀ / 8) + 8 * K + q₀ % 8 + 8 / 8
  · have e : k = K ∧ q = q₀ := by omega
    rw [ifp hc, ifp e, show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * (q₀ / 8) + 8 * K + q₀ % 8)) = 0 by omega,
      Proof.Sha3.extractLsb'_byte]
  · rw [ifn hc, ifn (by omega)]

theorem b8_of32 {n : Nat} (hn : n < 256) :
    ((BitVec.ofNat 32 n).setWidth 64 : BitVec 64) = (BitVec.ofNat 8 n).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : n < 4294967296), Nat.mod_eq_of_lt (by omega : n < 18446744073709551616),
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]

/-- The states after the indices of the first `K`. -/
def NF (b : Addr) (s₀ : State) (N₀ K : Nat) (k q : Nat) : Byte :=
  if q = 32 ∧ k < K then BitVec.ofNat 8 (N₀ + k) else GF b s₀ 4 0 k q

theorem nonces_eq (N₀ wl : Nat) : nonces N₀ wl = (List.range 4).flatMap fun k =>
    ([.mov32 .rax (.imm (BitVec.ofNat 32 (N₀ + k)))] : List Instr) ++
      ([.store8 (at_ .rbx (32 * (wl + 32 / 8) + 8 * k + 32 % 8)) .rax] : List Instr) := rfl

theorem nonces_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {N₀ : Nat}
    (hN : N₀ + 4 ≤ 256) {s : State} (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (GF b s₀ 4 0)) :
    WP isa (.block (nonces N₀ wl)) s (fun s' => AI b wl o m s₀ m₁ s' ∧ SB (sP b wl) s'.mem (NF b s₀ N₀ 4)) := by
  rw [nonces_eq]
  refine wp_range_flatMap (M := isa) (fun K s => AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (NF b s₀ N₀ K))
    (fun K s hK ⟨ha, hb⟩ => ?_) 4 (Nat.le_refl _) s ⟨h.1, fun k hk q hq => by rw [h.2 k hk q hq, NF, ifn (by omega)]⟩
  rw [WP.block_append_iff]
  refine wp_mov32i fun s₁ u₁ => wp_nil ?_
  refine WP.mono (cbyte_step hp (F := NF b s₀ N₀ K) (q₀ := 32) (c := BitVec.ofNat 8 (N₀ + K)) hK (by decide)
    (by rw [u₁.gpr, b8_of32 (by omega)]) ⟨ha.keep u₁.mem u₁.rd u₁.wr fun r hr => u₁.other r (rax_ncs r hr),
      by rw [u₁.mem]; exact hb⟩) fun s' ⟨ha', _, hb'⟩ => ⟨ha', fun k hk q hq => ?_⟩
  rw [hb' k hk q hq]
  simp only [NF]
  by_cases e : k = K ∧ q = 32
  · rw [ifp e, ifp ⟨e.2, by omega⟩, e.1]
  · rw [ifn e]
    by_cases e' : q = 32 ∧ k < K
    · rw [ifp e', ifp ⟨e'.1, by omega⟩]
    · rw [ifn e', ifn (by omega)]

/-- The byte `c` to byte `q₀` of each state. -/
theorem cbytes_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem}
    {F : Nat → Nat → Byte} {q₀ : Nat} (hq₀ : q₀ < 200) {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64)
    (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem F) :
    WP isa (.block ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (wl + q₀ / 8) + 8 * k + q₀ % 8)) .rax])) s
      (fun s' => AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        SB (sP b wl) s'.mem fun k q => if q = q₀ then c else F k q) := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s' => AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = c.setWidth 64 ∧
      SB (sP b wl) s'.mem fun k q => if k < K ∧ q = q₀ then c else F k q)
    (fun K s' hK ⟨ha, hx, hb⟩ => WP.mono (cbyte_step hp hK hq₀ hx ⟨ha, hb⟩) fun s'' ⟨ha', hx', hb'⟩ =>
      ⟨ha', hx'.trans hx, fun k hk q hq => ?_⟩) 4 (Nat.le_refl _) s ⟨h.1, hax, fun k hk q hq => ?_⟩)
    fun s' ⟨ha, hx, hb⟩ => ⟨ha, hx.trans hax.symm, fun k hk q hq => ?_⟩
  · rw [hb' k hk q hq]
    dsimp only
    by_cases e : k = K ∧ q = q₀
    · rw [ifp e, ifp (by omega)]
    · rw [ifn e]
      by_cases e' : k < K ∧ q = q₀
      · rw [ifp e', ifp (by omega)]
      · rw [ifn e', ifn (by omega)]
  · rw [h.2 k hk q hq]; dsimp only; rw [ifn (by omega)]
  · rw [hb k hk q hq]
    dsimp only
    by_cases e : q = q₀
    · rw [ifp e, ifp ⟨hk, e⟩]
    · rw [ifn e, ifn (by omega)]

theorem pads_eq (wl : Nat) : pads wl = ([.mov32 .rax (.imm 0x1f)] : List Instr) ++
    ((List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (wl + 33 / 8) + 8 * k + 33 % 8)) .rax]) ++
    (([.mov32 .rax (.imm 0x80)] : List Instr) ++
      (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (wl + 135 / 8) + 8 * k + 135 % 8)) .rax]))) :=
  rfl

/-- The padded inputs, from the states that hold `σ` and the indices. -/
theorem pads_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {N₀ : Nat}
    {s : State} (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (NF b s₀ N₀ 4)) :
    WP isa (.block (pads wl)) s (fun s' => AI b wl o m s₀ m₁ s' ∧
      SB (sP b wl) s'.mem fun k q => PF (sig b s₀) (BitVec.ofNat 8 (N₀ + k)) q) := by
  rw [pads_eq, WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₁ u₁ => wp_nil
    (Q := fun s₁ => AI b wl o m s₀ m₁ s₁ ∧ s₁.gpr .rax = (0x1f : Byte).setWidth 64 ∧ SB (sP b wl) s₁.mem (NF b s₀ N₀ 4))
    ⟨h.1.keep u₁.mem u₁.rd u₁.wr fun r hr => u₁.other r (rax_ncs r hr), by rw [u₁.gpr]; rfl,
      by rw [u₁.mem]; exact h.2⟩) fun s₁ ⟨a₁, x₁, b₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cbytes_ok hp (by decide) x₁ ⟨a₁, b₁⟩) fun s₂ ⟨a₂, _, b₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₃ u₃ => wp_nil
    (Q := fun s₃ => AI b wl o m s₀ m₁ s₃ ∧ s₃.gpr .rax = (0x80 : Byte).setWidth 64 ∧
      SB (sP b wl) s₃.mem fun k q => if q = 33 then 0x1f else NF b s₀ N₀ 4 k q)
    ⟨a₂.keep u₃.mem u₃.rd u₃.wr fun r hr => u₃.other r (rax_ncs r hr), by rw [u₃.gpr]; rfl,
      by rw [u₃.mem]; exact b₂⟩) fun s₃ ⟨a₃, x₃, b₃⟩ => ?_
  refine WP.mono (cbytes_ok hp (by decide) x₃ ⟨a₃, b₃⟩) fun s₄ ⟨a₄, _, b₄⟩ => ⟨a₄, fun k hk q hq => ?_⟩
  rw [b₄ k hk q hq]
  dsimp only [PF]
  rw [NF, GF]
  by_cases e1 : q < 32
  · rw [ifn (show ¬ q = 135 by omega), ifn (show ¬ q = 33 by omega), ifn (show ¬ (q = 32 ∧ k < 4) by omega),
      ifp (show q < 8 * 4 ∨ (q / 8 = 4 ∧ k < 0) by omega), ifp e1, sig_getD b s₀ e1]
  · rw [ifn e1]
    by_cases e2 : q = 32
    · rw [ifn (show ¬ q = 135 by omega), ifn (show ¬ q = 33 by omega), ifp ⟨e2, hk⟩, ifp e2]
    · rw [ifn e2, ifn (show ¬ (q = 32 ∧ k < 4) by omega), ifn (show ¬ (q < 8 * 4 ∨ (q / 8 = 4 ∧ k < 0)) by omega)]
      by_cases e3 : q = 33
      · rw [ifn (show ¬ q = 135 by omega), ifp e3, ifp e3]
      · rw [ifn e3, ifn e3]

/-! ## The setup -/

theorem setup_eq (N₀ wl : Nat) : setup N₀ wl =
    Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50) ++ (zero wl ++ (sigLanes wl ++ (nonces N₀ wl ++ (pads wl ++ args wl)))) := by
  simp only [setup, List.append_assoc]

theorem args_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {s : State}
    (he : BEnv b wl o m s₀ s) :
    WP isa (.block (args wl)) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = sP b wl ∧
      s'.gpr .rsi = sP b wl + BitVec.ofNat 64 800 ∧ s'.gpr .rdx = sP b wl + BitVec.ofNat 64 1600 ∧
      s'.gpr .rcx = sP b wl + BitVec.ofNat 64 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  have := hp.small
  have e1 : b + BitVec.ofNat 64 (32 * (wl + 25)) = sP b wl + BitVec.ofNat 64 800 := at_w b (by omega)
  have e2 : b + BitVec.ofNat 64 (32 * (wl + 50)) = sP b wl + BitVec.ofNat 64 1600 := at_w b (by omega)
  have e3 : b + BitVec.ofNat 64 (32 * (wl + 74)) = sP b wl + BitVec.ofNat 64 2368 := at_w b (by omega)
  refine WP.keep _ ?_ (by kernel_rfl)
  unfold args
  xrun [he.rbx hp, sx_ofNat (show 32 * wl < 2 ^ 31 by omega), sx_ofNat (show 32 * (wl + 25) < 2 ^ 31 by omega),
    sx_ofNat (show 32 * (wl + 50) < 2 ^ 31 by omega), sx_ofNat (show 32 * (wl + 74) < 2 ^ 31 by omega), e1, e2, e3]

/-- After the setup: the table, the padded inputs, and the arguments of the permutation. -/
structure SetupPost (b : Addr) (wl o m N₀ : Nat) (s₀ s : State) : Prop where
  env : BEnv b wl o m s₀ s
  tbl : Tbl (sP b wl) 24 s.mem
  lanes : Lanes4 s.mem (sP b wl) fun k => P0 (sig b s₀) (BitVec.ofNat 8 (N₀ + k))
  rdi : s.gpr .rdi = sP b wl
  rsi : s.gpr .rsi = sP b wl + BitVec.ofNat 64 800
  rdx : s.gpr .rdx = sP b wl + BitVec.ofNat 64 1600
  rcx : s.gpr .rcx = sP b wl + BitVec.ofNat 64 2368

theorem setup_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {N₀ : Nat} (hN : N₀ + 4 ≤ 256) :
    WP isa (.block (setup N₀ wl)) s₀ (SetupPost b wl o m N₀ s₀) := by
  rw [setup_eq, WP.block_append_iff]
  refine WP.mono (rc_ok hp (BEnv.refl (b := b) (wl := wl) (o := o) (m := m) (s₀ := s₀))) fun s₁ ⟨e₁, t₁⟩ => ?_
  have a₁ : AI b wl o m s₀ s₁.mem s₁ := ⟨e₁, Frame.refl _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok hp a₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sigLanes_ok hp h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nonces_ok hp hN h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pads_ok hp h₄) fun s₅ ⟨a₅, b₅⟩ => ?_
  refine WP.mono (args_ok hp a₅.env) fun s₆ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k⟩ => ?_
  refine ⟨⟨k.2.1.trans a₅.env.rd, k.2.2.trans a₅.env.wr,
      fun r hr => (k.gpr (by revert hr; decide +revert)).trans (a₅.env.cs r hr), by rw [hm]; exact a₅.env.frame⟩,
    fun r hr j hj => ?_, ?_, hdi, hsi, hdx, hcx⟩
  · rw [hm, a₅.fr.readW (Region.contains_self _ _) (by
      simpa using Offset.disjoint_base (sP b wl) (k := 800) (d := 32 * (50 + r) + 8 * j) (n := 8) (by omega)
        (by omega)) (by decide)]
    exact t₁ r hr j hj
  · rw [hm]
    exact lanes4_of_bytes fun k hk q hq => by rw [b₅ k hk q hq, byteOf_P0 (sig_length b s₀) _ hq]

/-! ## The permutation -/

theorem perm_ok {b : Addr} {wl o m N₀ : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {s : State}
    (h : SetupPost b wl o m N₀ s₀ s) :
    WP isa Impl.Sha3.X86_64.X4.permute4 s fun s' => BEnv b wl o m s₀ s' ∧
      Lanes4 s'.mem (sP b wl) fun k => keccakF (P0 (sig b s₀) (BitVec.ofNat 8 (N₀ + k))) := by
  have := hp.small
  have pre : Pre4 s (sP b wl) (sP b wl + BitVec.ofNat 64 800) (sP b wl + BitVec.ofNat 64 1600) :=
    ⟨fun i _ => in_w hp h.env (by omega),
      fun i _ => by rw [Offset.add_add]; exact in_w hp h.env (by omega),
      fun r _ => by rw [Offset.add_add]; exact in_w' hp h.env (by omega),
      Offset.base_disjoint _ (by omega) (by omega),
      Offset.base_disjoint _ (by omega) (by omega),
      Offset.disjoint _ (by omega) (by omega) (by omega),
      fun r hr k hk => by
        rw [la, Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by omega]
        exact h.tbl r hr k hk⟩
  refine WP.mono (permute4_ok pre h.rdi h.rsi h.rdx (by rw [h.rcx, Offset.add_add (sP b wl) 1600 768]) h.lanes)
    fun s' ⟨hl, hf, hrd, hwr, _, hg⟩ => ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, fun r hr => ?_,
      h.env.frame.trans (hf.sub fun r hr => ⟨wR b wl, by simp, ?_⟩)⟩, hl⟩
  · rw [hg r (rax_ncs r hr) (by revert hr; decide +revert)]; exact h.env.cs r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by omega)
    · exact Offset.sub_base _ (by omega)

/-! ## The outputs -/

/-- During the copies: the first `I` lanes of state `K` copied, and all of the states before it. -/
structure EXI (b : Addr) (wl o m : Nat) (s₀ : State) (L : Nat → Spec.Sha3.State) (K I : Nat) (s : State) : Prop where
  env : BEnv b wl o m s₀ s
  lanes : Lanes4 s.mem (sP b wl) L
  out : ∀ k < m, ∀ j < 128, (k < K ∨ (k = K ∧ j < 8 * I)) →
    s.mem (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * k + j)) = byteOf (L k) j

theorem ext_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {L : Nat → Spec.Sha3.State}
    {K I : Nat} (hK : K < m) (hI : I < 16) {s : State} (h : EXI b wl o m s₀ L K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * (wl + I) + 8 * K))),
      .store (at_ .rbx (o + 128 * K + 8 * I)) .rax]) s (EXI b wl o m s₀ L K (I + 1)) := by
  have := hp.small
  have hm4 := hp.hm
  refine wp_movm (a := la (sP b wl) I K) (by rw [ea_at, h.env.rbx hp, la]; exact at_w b (by omega))
    (in_w' hp h.env (by omega)) fun s₁ u₁ => wp_store (a := b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * K + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx hp, Offset.add_add, Nat.add_assoc])
      (by rw [u₁.wr]; exact in_o hp h.env (by omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * K + 8 * I))
      (s.mem.readW (la (sP b wl) I K) 64) := by rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨h.env.writeO hp (n := 8) (by omega) hm (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by rw [g₂, u₁.other r (rax_ncs r hr)], fun i hi k hk => ?_, fun k hk j hj hc => ?_⟩
  · rw [hm, Mem.readW_writeW_sep (((hp.dWO.sub_left (Offset.sub_base (sP b wl) (d := 32 * i + 8 * k) (n := 8)
      (k := 2368) (by omega))).sub_right (Offset.sub_base (b + BitVec.ofNat 64 o) (d := 128 * K + 8 * I) (n := 8)
      (k := 128 * m) (by omega))).sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    exact h.lanes i hi k hk
  · rw [hm]
    by_cases hw : k = K ∧ 8 * I ≤ j ∧ j < 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by omega) (by omega) (by decide),
        show 8 * (128 * k + j - (128 * k + 8 * I)) = 8 * (j - 8 * I) by omega,
        byte_readW _ _ (by omega), la_byte _ (by omega), byte_of_lanes4 h.lanes (by omega) (by omega),
        show 8 * I + (j - 8 * I) = j by omega]
    · rw [wb_out _ _ _ (by omega) (by omega) (by omega)]
      exact h.out k hk j hj (by omega)

theorem extract_eq (m o wl : Nat) : extract m o wl = (List.range m).flatMap fun K => (List.range 16).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * (wl + I) + 8 * K))), .store (at_ .rbx (o + 128 * K + 8 * I)) .rax] := rfl

theorem extract_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {L : Nat → Spec.Sha3.State}
    {s : State} (he : BEnv b wl o m s₀ s) (hl : Lanes4 s.mem (sP b wl) L) :
    WP isa (.block (extract m o wl)) s fun s' => BEnv b wl o m s₀ s' ∧
      ∀ k < m, ∀ j < 128, s'.mem (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * k + j)) = byteOf (L k) j := by
  rw [extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => EXI b wl o m s₀ L K 0 s) (fun K s hK h => ?_) m
    (Nat.le_refl _) s ⟨he, hl, fun _ _ _ _ hc => absurd hc (by omega)⟩)
    fun s' h' => ⟨h'.env, fun k hk j hj => h'.out k hk j hj (by omega)⟩
  exact WP.mono (wp_range_flatMap (M := isa) (fun I s => EXI b wl o m s₀ L K I s)
    (fun I s hI h => ext_step hp hK hI h) 16 (Nat.le_refl _) s h)
    fun s' h' => ⟨h'.env, h'.lanes, fun k hk j hj hc => h'.out k hk j hj (by omega)⟩

/-! ## The whole -/

/-- `batch N₀ m o wl`: `PRF₂(σ, N₀ + k)` to `scratch + o + 128 k` for each `k < m`. -/
theorem batch_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {N₀ : Nat} (hN : N₀ + 4 ≤ 256) :
    WP isa (batch N₀ m o wl) s₀ fun s => BEnv b wl o m s₀ s ∧
      ∀ k < m, bytesAt s.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 = prf 2 (sig b s₀) (BitVec.ofNat 8 (N₀ + k)) := by
  unfold batch
  refine WP.seq (WP.mono (setup_ok hp hN) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (perm_ok hp h₁) fun s₂ ⟨e₂, l₂⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (extract_ok hp e₂ l₂) fun s₃ ⟨e₃, o₃⟩ => WP.mono (vz_ok s₃) fun s₄ ⟨hm, k⟩ =>
    ⟨⟨k.2.1.trans e₃.rd, k.2.2.trans e₃.wr, fun r hr => (k.gpr List.not_mem_nil).trans (e₃.cs r hr),
      by rw [hm]; exact e₃.frame⟩, fun k hk => ?_⟩
  rw [hm]
  refine bytes_prf (sig_length b s₀) fun j hj => ?_
  have e := o₃ k hk j hj
  rw [Offset.add_add, ← Nat.add_assoc] at e
  rw [Offset.add_add]
  exact e

/-! ## Constant time -/

/-- `batch` leaks only the address in `rbx`: the immediates (the indices
and offsets) are the same in every run, and no address or branch depends on
the data. -/
theorem batch_tr {P : State → State → Prop} (hP : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) (N₀ o wl : Nat)
    {m : Nat} (hm : m ≤ 4) : RelCT isa P (batch N₀ m o wl) fun x y => x.gpr .rbx = y.gpr .rbx := by
  have hx : ((taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (extract m o wl ++ [.vop .vzeroupper]))
      (.block [])).map fun τ' => (RegSet.ofList [Reg.rbx]).subset τ'.regs) = some true := by
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl | rfl <;> kernel_rfl
  unfold batch
  refine RelCT.seq (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx])
    (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP x y h) [.rbx, .rdi, .rsi, .rdx, .rcx]
    (hc := .block []) (by kernel_rfl)) ?_
  refine RelCT.seq (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .rdi, .rsi, .rdx, .rcx])
    (fun x y h => X86_64.Taint.agree_ofRegs h) [.rbx] (by taint_decide)) ?_
  exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx]) (fun x y h => X86_64.Taint.agree_ofRegs h)
    [.rbx] hx) (fun _ _ h => h) fun _ _ h => h _ (List.mem_singleton_self _)

end VG.Proof.MlKem.X86_64.Prf4
