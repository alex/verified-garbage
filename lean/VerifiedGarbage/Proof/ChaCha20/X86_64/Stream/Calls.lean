import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Bytes
import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant

/-!
# Streaming ChaCha20 on x86-64: the calls

Untrusted: everything here is checked by Lean. The calls of
`vg_chacha20_block` and of an implementation of `vg_chacha20_xor`, from their
proofs of correctness (with `WP.call`), as ChaCha20-Poly1305 makes them.
-/

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)
open VG.Proof.ChaCha20.X86_64.Xor (stateAt_frame)

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

theorem callEntry_gpr' (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

theorem block_call {s : State} {S B : Addr} (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hsB : (below (s.gpr .rsp) 8).Disjoint ⟨B, 256⟩) (hsS : (below (s.gpr .rsp) 8).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨B, 256⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨B, 256⟩, below (s.gpr .rsp) 8] s.mem s'.mem → s'.gpr .rsi = B →
      stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockX86_64) Proof.ChaCha20.X86_64.block_correct
    (Proof.ChaCha20.X86_64.Xor.block_keeps_reg (by simp [Proof.ChaCha20.X86_64.Xor.kept]))
    (by rw [Proof.ChaCha20.X86_64.Xor.block_depth]; decide) (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_
  · simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
      callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi, hrsi]
    exact ⟨trivial, trivial, hdj, hsB⟩
  · intro s' hrd hwr hcs hf hkeep ⟨s₂, hm₂, _, hpost⟩
    rw [Proof.ChaCha20.X86_64.Xor.block_depth] at hf
    refine hQ s' hrd hwr hcs hf (by rw [hkeep .rsi (Proof.ChaCha20.X86_64.Xor.block_keeps_reg
      (by simp [Proof.ChaCha20.X86_64.Xor.kept])), hrsi]) ?_
    simp only [Proof.ChaCha20.blockX86_64, State.withRegions_gpr, State.withRegions_mem,
      callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), hrdi,
      hrsi, hm₂] at hpost
    rwa [stateAt_frame (callEntry_frame s) (by simpa using hsS.symm)] at hpost

theorem below8_24 (s : State) : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 24) :=
  below_sub (by decide) (by decide)

/-- The precondition of the implementation `v` of `vg_chacha20_xor`, called
with 24 bytes of stack below `rsp`: 8 for its return address, and at most 16
for its calls. -/
theorem xor_pre (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩) :
    (Proof.ChaCha20.xorStack v.stack).pre (s.callEntry.withRegions [] [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hk := v.stack_le
  have h8 := below8_24 s
  have hk' : Region.Sub ⟨s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack, v.stack⟩ (below (s.gpr .rsp) 24) := by
    rw [show s.gpr .rsp - 8 - BitVec.ofNat 64 v.stack = s.gpr .rsp - BitVec.ofNat 64 (8 + v.stack) by
      rw [BitVec.sub_sub, BitVec.ofNat_add]; rfl]
    exact Offset.sub_below _ (by omega) (by omega)
  simp only [Proof.ChaCha20.xorStack, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_rsp, callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rcx ≠ .rsp), hrdi, hrsi, hrdx, hrcx, hn']
  exact ⟨trivial, trivial, hSD, hSB, hDB, hsS.sub_left h8, hsD.sub_left h8, hsB.sub_left h8,
    hsS.sub_left hk', hsD.sub_left hk', hsB.sub_left hk', hwrap⟩

/-- A call of the implementation `v` of `vg_chacha20_xor` (see `xor_pre`). -/
theorem xor_call (v : Proof.ChaCha20.X86_64.XorImpl) {s : State} {S D B : Addr} {n : Nat}
    (hrdi : s.gpr .rdi = S) (hrsi : s.gpr .rsi = D)
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 n) (hrcx : s.gpr .rcx = B) (hn : n < 2 ^ 64)
    (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩) (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hwrap : D.toNat + n ≤ 2 ^ 64)
    (hsS : (below (s.gpr .rsp) 24).Disjoint ⟨S, 64⟩) (hsD : (below (s.gpr .rsp) 24).Disjoint ⟨D, n⟩)
    (hsB : (below (s.gpr .rsp) 24).Disjoint ⟨B, 320⟩)
    (hc : Covers ([] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem →
      bytesAt s'.mem D n = List.zipWith (· ^^^ ·) (bytesAt s.mem D n) (keystream (stateAt s.mem S) n) →
      Q s') :
    WP isa (.call v.callee.name v.callee.code) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
  have hd := v.depth_le
  have h8 := below8_24 s
  refine WP.call (k := Proof.ChaCha20.xorStack v.stack) v.ok v.nosp (by omega)
    (xor_pre v hrdi hrsi hrdx hrcx hn hSD hSB hDB hwrap hsS hsD hsB) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost, _⟩
  have hf' : Frame [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩, below (s.gpr .rsp) 24] s.mem s'.mem := by
    refine hf.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .rsp) 24, by simp, below_sub (by omega) (by omega)⟩
  refine hQ s' hrd hwr hcs hf' ?_
  simp only [Proof.ChaCha20.xorX86_64, State.withRegions_gpr, State.withRegions_mem,
    callEntry_gpr' s (by decide : Reg.rdi ≠ .rsp), callEntry_gpr' s (by decide : Reg.rsi ≠ .rsp),
    callEntry_gpr' s (by decide : Reg.rdx ≠ .rsp), hrdi, hrsi, hrdx, hn', hm₂] at hpost
  rw [hpost, bytesAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsD.sub_left h8).symm) (by omega),
    stateAt_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hsS.sub_left h8).symm)]

end VG.Proof.ChaCha20.X86_64.Stream
