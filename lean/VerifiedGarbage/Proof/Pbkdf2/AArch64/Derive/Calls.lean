import VerifiedGarbage.Proof.Pbkdf2.AArch64.Derive.Common
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Update
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.AArch64.Init
import VerifiedGarbage.Proof.Hmac.AArch64.Finalize
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate

/-!
# PBKDF2-HMAC-SHA-256 on AArch64: the calls

Untrusted: everything here is checked by Lean. Each call of a verified
function, from its proof of `Verified` (with `WP.callF`): what it needs of
the state it is called from (`…_pre`), and what holds when it returns
(`…_call`). The calls are made from the body of our frame, whose stack
pointer is `sp₀ - 16` for the entry stack pointer `sp₀`; the frames they push
are within the 48 bytes below `sp₀` (`frame48`).
-/

namespace VG.Proof.Pbkdf2.AArch64Derive

open VG VG.AArch64
open VG.Spec.Sha256 (bytesAt Repr)
open VG.Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey sha256)

theorem ce0 (s : State) : s.callEntry.gpr .x0 = s.gpr .x0 := State.callEntry_gpr s (by decide)
theorem ce1 (s : State) : s.callEntry.gpr .x1 = s.gpr .x1 := State.callEntry_gpr s (by decide)
theorem ce2 (s : State) : s.callEntry.gpr .x2 = s.gpr .x2 := State.callEntry_gpr s (by decide)
theorem ce3 (s : State) : s.callEntry.gpr .x3 = s.gpr .x3 := State.callEntry_gpr s (by decide)
theorem ce4 (s : State) : s.callEntry.gpr .x4 = s.gpr .x4 := State.callEntry_gpr s (by decide)

theorem sinit_fd : Impl.Sha256.AArch64.Stream.init.fdepth = 0 := by decide +kernel
theorem update_fd : Impl.Sha256.AArch64.Stream.update.fdepth = 1 := by decide +kernel
theorem sfin_fd : Impl.Sha256.AArch64.Stream.finalize.fdepth = 1 := by decide +kernel
theorem hinit_fd : Impl.Hmac.AArch64.init.fdepth = 1 := by decide +kernel
theorem hfin_fd : Impl.Hmac.AArch64.finalize.fdepth = 2 := by decide +kernel
theorem iter_fd : Impl.Pbkdf2.AArch64.iterate.fdepth = 0 := by decide +kernel

/-! ## `vg_sha256_init` -/

theorem sinit_pre {s : State} {St : Addr} (h0 : s.gpr .x0 = St) :
    Proof.Sha256.initAArch64.pre (s.callEntry.withRegions [] [⟨St, 96⟩]) := by
  simp only [Proof.Sha256.initAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce0, h0]
  exact ⟨trivial, trivial⟩

theorem sinit_call {nm : String} {s : State} {sp₀ St : Addr} (hsp : s.sp = sp₀ - 16) (h0 : s.gpr .x0 = St)
    (hc : Covers ([] ++ [⟨St, 96⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨St, 96⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨St, 96⟩, below sp₀ 48] s.mem s'.mem → Repr s'.mem St [] → Q s') :
    WP isa (.call nm Impl.Sha256.AArch64.Stream.init) s Q := by
  refine WP.callF (k := Proof.Sha256.initAArch64) Proof.Sha256.AArch64.Stream.init_verified.1
    (sinit_pre h0) hc hw ?_ (by rw [sinit_fd]; decide)
  intro s' rd wr sp hf cs hpost
  rw [hsp] at hf
  simp only [Proof.Sha256.initAArch64, State.withRegions_gpr, State.withRegions_mem, ce0, h0] at hpost
  exact hQ s' rd wr sp cs (frame48 hf (by rw [sinit_fd]; omega)) hpost

/-! ## `vg_sha256_update` -/

theorem update_pre {s : State} {sp₀ St D Sc : Addr} {n : Nat} (hsp : s.sp = sp₀ - 16)
    (h48 : 16 ≤ (sp₀ - 16).toNat) (h0 : s.gpr .x0 = St) (h2 : s.gpr .x2 = D)
    (h3 : (s.gpr .x3).toNat = n) (h4 : s.gpr .x4 = Sc)
    (d₁ : Region.Disjoint ⟨St, 96⟩ ⟨Sc, 160⟩) (d₂ : Region.Disjoint ⟨D, n⟩ ⟨St, 96⟩)
    (d₃ : Region.Disjoint ⟨D, n⟩ ⟨Sc, 160⟩) (kS : (below sp₀ 48).Disjoint ⟨St, 96⟩)
    (kD : (below sp₀ 48).Disjoint ⟨D, n⟩) (kC : (below sp₀ 48).Disjoint ⟨Sc, 160⟩) :
    Proof.Sha256.updateAArch64.pre (s.callEntry.withRegions [⟨D, n⟩] [⟨St, 96⟩, ⟨Sc, 160⟩]) := by
  simp only [Proof.Sha256.updateAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, ce0, ce2, ce3, ce4, h0, h2, h3, h4, hsp]
  exact ⟨trivial, trivial, d₁, d₂, d₃, h48, kS.sub_left (stk16_sub _), kD.sub_left (stk16_sub _),
    kC.sub_left (stk16_sub _)⟩

theorem update_call {nm : String} {s : State} {sp₀ St D Sc : Addr} {n : Nat} (hsp : s.sp = sp₀ - 16)
    (h48 : 16 ≤ (sp₀ - 16).toNat) (h0 : s.gpr .x0 = St) (h2 : s.gpr .x2 = D)
    (h3 : (s.gpr .x3).toNat = n) (h4 : s.gpr .x4 = Sc)
    (d₁ : Region.Disjoint ⟨St, 96⟩ ⟨Sc, 160⟩) (d₂ : Region.Disjoint ⟨D, n⟩ ⟨St, 96⟩)
    (d₃ : Region.Disjoint ⟨D, n⟩ ⟨Sc, 160⟩) (kS : (below sp₀ 48).Disjoint ⟨St, 96⟩)
    (kD : (below sp₀ 48).Disjoint ⟨D, n⟩) (kC : (below sp₀ 48).Disjoint ⟨Sc, 160⟩)
    (hc : Covers ([⟨D, n⟩] ++ [⟨St, 96⟩, ⟨Sc, 160⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨St, 96⟩, ⟨Sc, 160⟩] s.wr)
    {m : List Byte} (hm : Repr s.mem St m) (h1 : s.gpr .x1 = BitVec.ofNat 64 m.length) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨St, 96⟩, ⟨Sc, 160⟩, below sp₀ 48] s.mem s'.mem →
      Repr s'.mem St (m ++ bytesAt s.mem D n) → Q s') :
    WP isa (.call nm Impl.Sha256.AArch64.Stream.update) s Q := by
  refine WP.callF (k := Proof.Sha256.updateAArch64) Proof.Sha256.AArch64.Stream.Update.update_verified.1
    (update_pre hsp h48 h0 h2 h3 h4 d₁ d₂ d₃ kS kD kC) hc hw ?_ (by rw [update_fd]; decide)
  intro s' rd wr sp hf cs hpost
  rw [hsp] at hf
  simp only [Proof.Sha256.updateAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce0, ce1, ce2, ce3, h0, h1, h2, h3] at hpost
  exact hQ s' rd wr sp cs (frame48 hf (by rw [update_fd]; omega)) (hpost m hm rfl)

/-! ## `vg_sha256_finalize` -/

theorem sfin_pre {s : State} {sp₀ St O Sc : Addr} (hsp : s.sp = sp₀ - 16)
    (h48 : 16 ≤ (sp₀ - 16).toNat) (h0 : s.gpr .x0 = St) (h2 : s.gpr .x2 = O) (h3 : s.gpr .x3 = Sc)
    (d₁ : Region.Disjoint ⟨St, 96⟩ ⟨O, 32⟩) (d₂ : Region.Disjoint ⟨St, 96⟩ ⟨Sc, 160⟩)
    (d₃ : Region.Disjoint ⟨O, 32⟩ ⟨Sc, 160⟩) (kS : (below sp₀ 48).Disjoint ⟨St, 96⟩)
    (kO : (below sp₀ 48).Disjoint ⟨O, 32⟩) (kC : (below sp₀ 48).Disjoint ⟨Sc, 160⟩) :
    Proof.Sha256.finalizeAArch64.pre (s.callEntry.withRegions [] [⟨St, 96⟩, ⟨O, 32⟩, ⟨Sc, 160⟩]) := by
  simp only [Proof.Sha256.finalizeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, ce0, ce2, ce3, h0, h2, h3, hsp]
  exact ⟨trivial, trivial, d₁, d₂, d₃, h48, kS.sub_left (stk16_sub _), kO.sub_left (stk16_sub _),
    kC.sub_left (stk16_sub _)⟩

theorem sfin_call {nm : String} {s : State} {sp₀ St O Sc : Addr} (hsp : s.sp = sp₀ - 16)
    (h48 : 16 ≤ (sp₀ - 16).toNat) (h0 : s.gpr .x0 = St) (h2 : s.gpr .x2 = O) (h3 : s.gpr .x3 = Sc)
    (d₁ : Region.Disjoint ⟨St, 96⟩ ⟨O, 32⟩) (d₂ : Region.Disjoint ⟨St, 96⟩ ⟨Sc, 160⟩)
    (d₃ : Region.Disjoint ⟨O, 32⟩ ⟨Sc, 160⟩) (kS : (below sp₀ 48).Disjoint ⟨St, 96⟩)
    (kO : (below sp₀ 48).Disjoint ⟨O, 32⟩) (kC : (below sp₀ 48).Disjoint ⟨Sc, 160⟩)
    (hc : Covers ([] ++ [⟨St, 96⟩, ⟨O, 32⟩, ⟨Sc, 160⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨St, 96⟩, ⟨O, 32⟩, ⟨Sc, 160⟩] s.wr)
    {m : List Byte} (hm : Repr s.mem St m) (h1 : s.gpr .x1 = BitVec.ofNat 64 m.length) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨St, 96⟩, ⟨O, 32⟩, ⟨Sc, 160⟩, below sp₀ 48] s.mem s'.mem →
      bytesAt s'.mem O 32 = Spec.Sha256.hash m → Q s') :
    WP isa (.call nm Impl.Sha256.AArch64.Stream.finalize) s Q := by
  refine WP.callF (k := Proof.Sha256.finalizeAArch64) Proof.Sha256.AArch64.Stream.Finalize.finalize_verified.1
    (sfin_pre hsp h48 h0 h2 h3 d₁ d₂ d₃ kS kO kC) hc hw ?_ (by rw [sfin_fd]; decide)
  intro s' rd wr sp hf cs hpost
  rw [hsp] at hf
  simp only [Proof.Sha256.finalizeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce0, ce1, ce2, h0, h1, h2] at hpost
  exact hQ s' rd wr sp cs (frame48 hf (by rw [sfin_fd]; omega)) (hpost m hm rfl)

/-! ## `vg_hmac_sha256_init` -/

theorem hinit_pre {s : State} {sp₀ I O K Sc : Addr} {n : Nat} (hsp : s.sp = sp₀ - 16)
    (h48 : 16 ≤ (sp₀ - 16).toNat) (h0 : s.gpr .x0 = I) (h1 : s.gpr .x1 = O)
    (h2 : s.gpr .x2 = K) (h3 : (s.gpr .x3).toNat = n) (h4 : s.gpr .x4 = Sc) (hn : n ≤ 64)
    (d₁ : Region.Disjoint ⟨I, 96⟩ ⟨O, 96⟩) (d₂ : Region.Disjoint ⟨I, 96⟩ ⟨Sc, 160⟩)
    (d₃ : Region.Disjoint ⟨O, 96⟩ ⟨Sc, 160⟩) (d₄ : Region.Disjoint ⟨K, n⟩ ⟨I, 96⟩)
    (d₅ : Region.Disjoint ⟨K, n⟩ ⟨O, 96⟩) (d₆ : Region.Disjoint ⟨K, n⟩ ⟨Sc, 160⟩)
    (kI : (below sp₀ 48).Disjoint ⟨I, 96⟩) (kO : (below sp₀ 48).Disjoint ⟨O, 96⟩)
    (kK : (below sp₀ 48).Disjoint ⟨K, n⟩) (kC : (below sp₀ 48).Disjoint ⟨Sc, 160⟩) :
    Proof.Hmac.initSha256AArch64.pre (s.callEntry.withRegions [⟨K, n⟩] [⟨I, 96⟩, ⟨O, 96⟩, ⟨Sc, 160⟩]) := by
  simp only [Proof.Hmac.initSha256AArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, ce4, h0, h1, h2, h3, h4, hsp]
  exact ⟨hn, trivial, trivial, d₁, d₂, d₃, d₄, d₅, d₆, h48, kI.sub_left (stk16_sub _),
    kO.sub_left (stk16_sub _), kK.sub_left (stk16_sub _), kC.sub_left (stk16_sub _)⟩

theorem hinit_call {nm : String} {s : State} {sp₀ I O K Sc : Addr} {n : Nat} (hsp : s.sp = sp₀ - 16)
    (h48 : 16 ≤ (sp₀ - 16).toNat) (h0 : s.gpr .x0 = I) (h1 : s.gpr .x1 = O)
    (h2 : s.gpr .x2 = K) (h3 : (s.gpr .x3).toNat = n) (h4 : s.gpr .x4 = Sc) (hn : n ≤ 64)
    (d₁ : Region.Disjoint ⟨I, 96⟩ ⟨O, 96⟩) (d₂ : Region.Disjoint ⟨I, 96⟩ ⟨Sc, 160⟩)
    (d₃ : Region.Disjoint ⟨O, 96⟩ ⟨Sc, 160⟩) (d₄ : Region.Disjoint ⟨K, n⟩ ⟨I, 96⟩)
    (d₅ : Region.Disjoint ⟨K, n⟩ ⟨O, 96⟩) (d₆ : Region.Disjoint ⟨K, n⟩ ⟨Sc, 160⟩)
    (kI : (below sp₀ 48).Disjoint ⟨I, 96⟩) (kO : (below sp₀ 48).Disjoint ⟨O, 96⟩)
    (kK : (below sp₀ 48).Disjoint ⟨K, n⟩) (kC : (below sp₀ 48).Disjoint ⟨Sc, 160⟩)
    (hc : Covers ([⟨K, n⟩] ++ [⟨I, 96⟩, ⟨O, 96⟩, ⟨Sc, 160⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨I, 96⟩, ⟨O, 96⟩, ⟨Sc, 160⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨I, 96⟩, ⟨O, 96⟩, ⟨Sc, 160⟩, below sp₀ 48] s.mem s'.mem →
      Repr s'.mem I (xorPad (blockKey sha256 (bytesAt s.mem K n)) ipad) →
      Repr s'.mem O (xorPad (blockKey sha256 (bytesAt s.mem K n)) opad) → Q s') :
    WP isa (.call nm Impl.Hmac.AArch64.init) s Q := by
  refine WP.callF (k := Proof.Hmac.initSha256AArch64) Proof.Hmac.AArch64.Init.init_verified.1
    (hinit_pre hsp h48 h0 h1 h2 h3 h4 hn d₁ d₂ d₃ d₄ d₅ d₆ kI kO kK kC) hc hw ?_ (by rw [hinit_fd]; decide)
  intro s' rd wr sp hf cs hpost
  rw [hsp] at hf
  simp only [Proof.Hmac.initSha256AArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce0, ce1, ce2, ce3, h0, h1, h2, h3] at hpost
  exact hQ s' rd wr sp cs (frame48 hf (by rw [hinit_fd]; omega)) hpost.1 hpost.2

/-! ## `vg_hmac_sha256_finalize` -/

theorem hfin_pre {s : State} {sp₀ I O Sc : Addr} (hsp : s.sp = sp₀ - 16)
    (h48 : 32 ≤ (sp₀ - 16).toNat) (h0 : s.gpr .x0 = I) (h1 : s.gpr .x1 = O) (h3 : s.gpr .x3 = Sc)
    (d₁ : Region.Disjoint ⟨I, 96⟩ ⟨O, 96⟩) (d₂ : Region.Disjoint ⟨I, 96⟩ ⟨Sc, 240⟩)
    (d₃ : Region.Disjoint ⟨O, 96⟩ ⟨Sc, 240⟩)
    (kI : (below sp₀ 48).Disjoint ⟨I, 96⟩) (kO : (below sp₀ 48).Disjoint ⟨O, 96⟩)
    (kC : (below sp₀ 48).Disjoint ⟨Sc, 240⟩) :
    Proof.Hmac.finalizeSha256AArch64.pre (s.callEntry.withRegions [⟨O, 96⟩] [⟨I, 96⟩, ⟨Sc, 240⟩]) := by
  simp only [Proof.Hmac.finalizeSha256AArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce3, h0, h1, h3, hsp]
  exact ⟨trivial, trivial, d₁, d₂, d₃, h48, kI.sub_left (stk32_sub _), kO.sub_left (stk32_sub _),
    kC.sub_left (stk32_sub _)⟩

theorem hfin_call {nm : String} {s : State} {sp₀ I O Sc : Addr} (hsp : s.sp = sp₀ - 16)
    (h48 : 32 ≤ (sp₀ - 16).toNat) (h0 : s.gpr .x0 = I) (h1 : s.gpr .x1 = O) (h3 : s.gpr .x3 = Sc)
    (d₁ : Region.Disjoint ⟨I, 96⟩ ⟨O, 96⟩) (d₂ : Region.Disjoint ⟨I, 96⟩ ⟨Sc, 240⟩)
    (d₃ : Region.Disjoint ⟨O, 96⟩ ⟨Sc, 240⟩)
    (kI : (below sp₀ 48).Disjoint ⟨I, 96⟩) (kO : (below sp₀ 48).Disjoint ⟨O, 96⟩)
    (kC : (below sp₀ 48).Disjoint ⟨Sc, 240⟩)
    (hc : Covers ([⟨O, 96⟩] ++ [⟨I, 96⟩, ⟨Sc, 240⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨I, 96⟩, ⟨Sc, 240⟩] s.wr)
    {k : List Byte} (hk : k.length = 64) {text : List Byte} (hI : Repr s.mem I (xorPad k ipad ++ text))
    (hO : Repr s.mem O (xorPad k opad)) (h2 : s.gpr .x2 = BitVec.ofNat 64 (64 + text.length))
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨I, 96⟩, ⟨Sc, 240⟩, below sp₀ 48] s.mem s'.mem →
      bytesAt s'.mem (Sc + 176) 32 = hmacBlockKey sha256 k text → Q s') :
    WP isa (.call nm Impl.Hmac.AArch64.finalize) s Q := by
  refine WP.callF (k := Proof.Hmac.finalizeSha256AArch64) Proof.Hmac.AArch64.Finalize.finalize_verified.1
    (hfin_pre hsp h48 h0 h1 h3 d₁ d₂ d₃ kI kO kC) hc hw ?_ (by rw [hfin_fd]; decide)
  intro s' rd wr sp hf cs hpost
  rw [hsp] at hf
  simp only [Proof.Hmac.finalizeSha256AArch64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, ce0, ce1, ce2, ce3, h0, h1, h2, h3] at hpost
  exact hQ s' rd wr sp cs (frame48 hf (by rw [hfin_fd])) (hpost k text hk hI rfl hO)

/-! ## `vg_pbkdf2_hmac_sha256_iterate` -/

theorem iter_pre {s : State} {K U T Sc : Addr} (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = U)
    (h3 : s.gpr .x3 = T) (h4 : s.gpr .x4 = Sc)
    (d₁ : Region.Disjoint ⟨K, 192⟩ ⟨T, 32⟩) (d₂ : Region.Disjoint ⟨K, 192⟩ ⟨Sc, 384⟩)
    (d₃ : Region.Disjoint ⟨U, 32⟩ ⟨T, 32⟩) (d₄ : Region.Disjoint ⟨U, 32⟩ ⟨Sc, 384⟩)
    (d₅ : Region.Disjoint ⟨T, 32⟩ ⟨Sc, 384⟩) :
    Proof.Pbkdf2.iterateSha256AArch64.pre
      (s.callEntry.withRegions [⟨K, 192⟩, ⟨U, 32⟩] [⟨T, 32⟩, ⟨Sc, 384⟩]) := by
  simp only [Proof.Pbkdf2.iterateSha256AArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, ce0, ce1, ce3, ce4, h0, h1, h3, h4]
  exact ⟨trivial, trivial, d₁, d₂, d₃, d₄, d₅⟩

theorem iter_call {nm : String} {s : State} {sp₀ K U T Sc : Addr} (hsp : s.sp = sp₀ - 16)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = U) (h3 : s.gpr .x3 = T) (h4 : s.gpr .x4 = Sc)
    (d₁ : Region.Disjoint ⟨K, 192⟩ ⟨T, 32⟩) (d₂ : Region.Disjoint ⟨K, 192⟩ ⟨Sc, 384⟩)
    (d₃ : Region.Disjoint ⟨U, 32⟩ ⟨T, 32⟩) (d₄ : Region.Disjoint ⟨U, 32⟩ ⟨Sc, 384⟩)
    (d₅ : Region.Disjoint ⟨T, 32⟩ ⟨Sc, 384⟩)
    (hc : Covers ([⟨K, 192⟩, ⟨U, 32⟩] ++ [⟨T, 32⟩, ⟨Sc, 384⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨T, 32⟩, ⟨Sc, 384⟩] s.wr)
    {k : List Byte} (hk : k.length = 64) (hI : Repr s.mem K (xorPad k ipad))
    (hO : Repr s.mem (K + 96) (xorPad k opad)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      Frame [⟨T, 32⟩, ⟨Sc, 384⟩, below sp₀ 48] s.mem s'.mem →
      bytesAt s'.mem T 32 = Spec.Pbkdf2.iterate (hmacBlockKey sha256 k) ((s.gpr .x2).setWidth 32).toNat
        (bytesAt s.mem U 32) (bytesAt s.mem T 32) → Q s') :
    WP isa (.call nm Impl.Pbkdf2.AArch64.iterate) s Q := by
  refine WP.callF (k := Proof.Pbkdf2.iterateSha256AArch64) Proof.Pbkdf2.AArch64.iterate_verified.1
    (iter_pre h0 h1 h3 h4 d₁ d₂ d₃ d₄ d₅) hc hw ?_ (by rw [iter_fd]; decide)
  intro s' rd wr sp hf cs hpost
  rw [hsp] at hf
  simp only [Proof.Pbkdf2.iterateSha256AArch64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, ce0, ce1, ce2, ce3, h0, h1, h3] at hpost
  exact hQ s' rd wr sp cs (frame48 hf (by rw [iter_fd]; omega)) (hpost k hk hI hO)

end VG.Proof.Pbkdf2.AArch64Derive
