import VerifiedGarbage.Impl.AesGcm.AArch64
import VerifiedGarbage.Proof.Aes.AArch64.Variant
import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
import VerifiedGarbage.Proof.Gcm.AArch64.Ghash
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Stream

/-!
# AES-GCM on AArch64: the functions called

Untrusted: everything here is checked by Lean. What the AES-GCM functions
need of the implementations of `vg_ghash`, `vg_aes_expand_key` and
`vg_aes_ctr32` they call (`GhashImpl`, `KeyImpl`, and the existing
`Ctr32Impl`), and each call from its callee's contract (with `WP.call`), with
the regions it is given: what it needs (`GhCall`, `CtrCall`, `KeyCall`) and
what it leaves (`GhPost`, `CtrPost`, `KeyPost`); and that it is constant time
(`gh_rel`, `ctr_rel`, `key_rel`). A call (`bl`) stores nothing in memory.
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32 aesWith)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- An implementation of `vg_ghash` on AArch64. -/
structure GhashImpl where
  fn : Fn
  noFrames : fn.code.noFrames = true
  ok : ∀ s, Proof.Gcm.ghashAArch64.pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ Proof.Gcm.ghashAArch64.post s s'
  ct : ConstantTime isa Proof.Gcm.ghashAArch64.pre Proof.Gcm.ghashAArch64.pub fn.code
  keepsV : fn.code.allInstrs keepsV = true
  suffix : String
  features : List String

/-- An implementation of `vg_aes_expand_key` on AArch64. -/
structure KeyImpl where
  fn : Fn
  noFrames : fn.code.noFrames = true
  ok : ∀ s, Proof.Aes.expandKeyAArch64.pre s →
    ∃ t s', Exec isa fn.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyAArch64.post s s'
  ct : ConstantTime isa Proof.Aes.expandKeyAArch64.pre Proof.Aes.expandKeyAArch64.pub fn.code
  keepsV : fn.code.allInstrs keepsV = true

namespace GhashImpl

/-- `vg_ghash`, in the baseline ISA. -/
def scalar : GhashImpl where
  fn := ⟨"vg_ghash", Impl.Gcm.AArch64.ghash⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.ghash_correct
  ct := Proof.Gcm.AArch64.ghash_ct
  keepsV := by decide +kernel
  suffix := ""
  features := []

end GhashImpl

namespace KeyImpl

/-- `vg_aes_expand_key`, in the baseline ISA. -/
def scalar : KeyImpl where
  fn := ⟨"vg_aes_expand_key", Impl.Aes.AArch64.expandKey⟩
  noFrames := by decide +kernel
  ok := Proof.Aes.AArch64.expandKey_correct
  ct := Proof.Aes.AArch64.expandKey_ct
  keepsV := by decide +kernel

/-- `vg_aes_expand_key_aes`. -/
def aese : KeyImpl where
  fn := ⟨"vg_aes_expand_key_aes", Impl.Aes.AArch64.Aese.expandKey⟩
  noFrames := by decide +kernel
  ok := Proof.Aes.AArch64.Aese.Key.expandKey_correct
  ct := Proof.Aes.AArch64.Aese.Key.expandKey_ct
  keepsV := by decide +kernel

end KeyImpl

/-! ## Memory -/

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := Proof.Cmac.bytesAt_frame hf hd hn

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, bytesAt_frame hf hd hn]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R :=
  toNat_ofNat_lt (by omega)

theorem callEntry_x0 (s : State) : s.callEntry.gpr .x0 = s.gpr .x0 := s.callEntry_gpr (by decide)
theorem callEntry_x1 (s : State) : s.callEntry.gpr .x1 = s.gpr .x1 := s.callEntry_gpr (by decide)
theorem callEntry_x2 (s : State) : s.callEntry.gpr .x2 = s.gpr .x2 := s.callEntry_gpr (by decide)
theorem callEntry_x3 (s : State) : s.callEntry.gpr .x3 = s.gpr .x3 := s.callEntry_gpr (by decide)
theorem callEntry_x4 (s : State) : s.callEntry.gpr .x4 = s.gpr .x4 := s.callEntry_gpr (by decide)
theorem callEntry_x5 (s : State) : s.callEntry.gpr .x5 = s.gpr .x5 := s.callEntry_gpr (by decide)

/-! ## `vg_ghash` -/

/-- What a call of `vg_ghash` needs: the hash subkey at `H`, the accumulator
at `Y`, `n` blocks at `D` and working space at `S`. -/
structure GhCall (s : State) (H Y D S : Addr) (n : Nat) : Prop where
  x0 : s.gpr .x0 = H
  x1 : s.gpr .x1 = Y
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = BitVec.ofNat 64 n
  x4 : s.gpr .x4 = S
  n_lt : 16 * n < 2 ^ 64
  hy : (⟨H, 16⟩ : Region).Disjoint ⟨Y, 16⟩
  hs : (⟨H, 16⟩ : Region).Disjoint ⟨S, 256⟩
  yd : (⟨Y, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ys : (⟨Y, 16⟩ : Region).Disjoint ⟨S, 256⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 256⟩
  reads : Covers ([⟨H, 16⟩, ⟨D, 16 * n⟩] ++ [⟨Y, 16⟩, ⟨S, 256⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨Y, 16⟩, ⟨S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : Addr) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨Y, 16⟩, ⟨S, 256⟩] s.mem s'.mem
  out : blockAt s'.mem Y = ghashFrom (blockAt s.mem H) (blockAt s.mem Y) (blocksAt s.mem D n)

theorem GhCall.pre {s : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n) :
    Proof.Gcm.ghashAArch64.pre (s.callEntry.withRegions [⟨H, 16⟩, ⟨D, 16 * n⟩] [⟨Y, 16⟩, ⟨S, 256⟩]) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  simp only [Proof.Gcm.ghashAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4, hn]
  exact ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds⟩

theorem gh_call (g : GhashImpl) {s : State} {H Y D S : Addr} {n : Nat} (h : GhCall s H Y D S n) :
    WP isa (.call g.fn.name g.fn.code) s (GhPost s H Y D S n) := by
  have hn := toNat_ofNat_lt (show n < 2 ^ 64 by have := h.n_lt; omega)
  refine WP.call (k := Proof.Gcm.ghashAArch64) g.ok (rd := [⟨H, 16⟩, ⟨D, 16 * n⟩])
    (wr := [⟨Y, 16⟩, ⟨S, 256⟩]) h.pre h.reads h.writes ?_ g.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Gcm.ghashAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hn] at hpost
  exact hpost

theorem gh_rel (g : GhashImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ H Y D S : Addr, ∃ n : Nat,
      GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call g.fn.name g.fn.code) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨H, Y, D, S, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) g.ok g.ct [⟨H, 16⟩, ⟨D, 16 * n⟩] [⟨Y, 16⟩, ⟨S, 256⟩]
    (fun a b hab => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Gcm.ghashAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_ctr32` -/

/-- What a call of `vg_aes_ctr32` needs: the key schedule at `K` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and working space at `S`. -/
structure CtrCall (s : State) (K C D S : Addr) (R n : Nat) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = C
  x3 : s.gpr .x3 = D
  x4 : s.gpr .x4 = BitVec.ofNat 64 n
  x5 : s.gpr .x5 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  n_lt : n < 2 ^ 64
  kc : (⟨K, 240⟩ : Region).Disjoint ⟨C, 16⟩
  kd : (⟨K, 240⟩ : Region).Disjoint ⟨D, 16 * n⟩
  ks : (⟨K, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  cd : (⟨C, 16⟩ : Region).Disjoint ⟨D, 16 * n⟩
  cs : (⟨C, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16 * n⟩ : Region).Disjoint ⟨S, 2048⟩
  reads : Covers ([⟨K, 240⟩] ++ [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.wr

/-- What a call of `vg_aes_ctr32` leaves. -/
structure CtrPost (s : State) (K C D S : Addr) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : blocksAt s'.mem D n = ctr32 (aesWith R (bytesAt s.mem K (16 * (R + 1)))) (blockAt s.mem C)
    (blocksAt s.mem D n)
  ctr : blockAt s'.mem C = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem C)

theorem CtrCall.pre {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    Proof.Aes.ctr32AArch64.pre
      (s.callEntry.withRegions [⟨K, 240⟩] [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  simp only [Proof.Aes.ctr32AArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    callEntry_x5, h.x0, h.x1, h.x2, h.x3, h.x4, h.x5, hR, hn]
  exact ⟨trivial, trivial, h.kc, h.kd, h.ks, h.cd, h.cs, h.ds, h.wrap, h.rounds⟩

theorem ctr_call (v : Ctr32Impl) {s : State} {K C D S : Addr} {R n : Nat} (h : CtrCall s K C D S R n) :
    WP isa (.call v.callee.name v.callee.code) s (CtrPost s K C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hn := toNat_ofNat_lt h.n_lt
  refine WP.call (k := Proof.Aes.ctr32AArch64) v.ok (rd := [⟨K, 240⟩])
    (wr := [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩]) h.pre h.reads h.writes ?_ v.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    hR, hn] at hdata hctr
  exact ⟨hrd, hwr, hsp, hsaved, hf, hdata, hctr⟩

theorem ctr_rel (v : Ctr32Impl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D S : Addr, ∃ R n : Nat,
      CtrCall s₁ K C D S R n ∧ CtrCall s₂ K C D S R n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call v.callee.name v.callee.code) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) v.ok v.ct [⟨K, 240⟩]
    [⟨C, 16⟩, ⟨D, 16 * n⟩, ⟨S, 2048⟩] (fun a b hab => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.ctr32AArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₁.x5, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, h₂.x5, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the `L`-byte key at `K`, the key
schedule at `C` and working space at `S`. -/
structure KeyCall (s : State) (K C S : Addr) (L : Nat) : Prop where
  x0 : s.gpr .x0 = K
  x1 : s.gpr .x1 = BitVec.ofNat 64 L
  x2 : s.gpr .x2 = C
  x3 : s.gpr .x3 = S
  len : L = 16 ∨ L = 24 ∨ L = 32
  kc : (⟨K, L⟩ : Region).Disjoint ⟨C, 240⟩
  ks : (⟨K, L⟩ : Region).Disjoint ⟨S, 512⟩
  cs : (⟨C, 240⟩ : Region).Disjoint ⟨S, 512⟩
  reads : Covers ([⟨K, L⟩] ++ [⟨C, 240⟩, ⟨S, 512⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨C, 240⟩, ⟨S, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure KeyPost (s : State) (K C S : Addr) (L : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨C, 240⟩, ⟨S, 512⟩] s.mem s'.mem
  out : bytesAt s'.mem C (16 * (Spec.Aes.rounds (L / 4) + 1)) = Spec.Aes.expandKey (bytesAt s.mem K L)

theorem KeyCall.pre {s : State} {K C S : Addr} {L : Nat} (h : KeyCall s K C S L) :
    Proof.Aes.expandKeyAArch64.pre (s.callEntry.withRegions [⟨K, L⟩] [⟨C, 240⟩, ⟨S, 512⟩]) := by
  have hL := toNat_ofNat_lt (show L < 2 ^ 64 by rcases h.len with rfl | rfl | rfl <;> decide)
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2,
    h.x3, hL]
  exact ⟨trivial, trivial, h.kc, h.ks, h.cs, h.len⟩

theorem key_call (k : KeyImpl) {s : State} {K C S : Addr} {L : Nat} (h : KeyCall s K C S L) :
    WP isa (.call k.fn.name k.fn.code) s (KeyPost s K C S L) := by
  have hL := toNat_ofNat_lt (show L < 2 ^ 64 by rcases h.len with rfl | rfl | rfl <;> decide)
  refine WP.call (k := Proof.Aes.expandKeyAArch64) k.ok (rd := [⟨K, L⟩]) (wr := [⟨C, 240⟩, ⟨S, 512⟩])
    h.pre h.reads h.writes ?_ k.noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, h.x0, h.x1, h.x2, hL] at hpost
  exact ⟨hrd, hwr, hsp, hsaved, hf, hpost⟩

theorem key_rel (k : KeyImpl) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C S : Addr, ∃ L : Nat,
      KeyCall s₁ K C S L ∧ KeyCall s₂ K C S L ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call k.fn.name k.fn.code) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, C, S, L, h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine RelCT.call (P := fun a b => a = s₁ ∧ b = s₂) k.ok k.ct [⟨K, L⟩] [⟨C, 240⟩, ⟨S, 512⟩]
    (fun a b hab => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  obtain ⟨rfl, rfl⟩ := hab
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.expandKeyAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₂.x0, h₂.x1, h₂.x2, h₂.x3, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-! ## The implementations, together -/

/-- What an AES-GCM function calls: an implementation of `vg_aes_ctr32`, the
`vg_aes_expand_key` for the same CPUs, and one of `vg_ghash`. -/
structure GcmImpl where
  ctr : Ctr32Impl
  key : KeyImpl
  gh : GhashImpl

namespace GcmImpl

variable (v : GcmImpl)

def callees : Callees := ⟨⟨v.ctr.callee.name, v.ctr.callee.code⟩, v.key.fn, v.gh.fn⟩

/-- What the names of the AES-GCM functions end with: once if both
implementations have the same suffix (`_aes`, for the one feature they
need). -/
def suffix : String :=
  if v.gh.suffix = v.ctr.suffix then v.ctr.suffix else v.ctr.suffix ++ v.gh.suffix


end GcmImpl

end VG.Proof.AesGcm.AArch64
