import VerifiedGarbage.Proof.Argon2.X86.HPrime.First

/-!
# Argon2 H′ on x86 (32-bit): the chain of 64-byte hashes

`chain_ok`: after the first prefix V₁[0, 32) of a long output, each iteration
hashes the digest again and emits the prefix of the new one, while more than
64 bytes are left. The output is then V₁[0, 32) ‖ `chainPrefixes j V₁` and the
digest `chainDigest j V₁`, with 33 to 64 bytes left.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain leftOff)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_movi wp_movm wp_cmpi)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem chainDigest_succ' (j : Nat) (v : List Byte) :
    chainDigest (j + 1) v = Spec.Argon2.H 64 (chainDigest j v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih => exact ih (Spec.Argon2.H 64 v)

theorem chainPrefixes_succ' (j : Nat) (v : List Byte) :
    chainPrefixes (j + 1) v = chainPrefixes j v ++ (Spec.Argon2.H 64 (chainDigest j v)).take 32 := by
  induction j generalizing v with
  | zero => simp [chainPrefixes, chainDigest]
  | succ j ih =>
    rw [chainPrefixes, ih, chainPrefixes, chainDigest, List.append_assoc]

theorem finalHash_length (h0 : HashValue 64) (d : List Byte) : (finalHash b h0 d).length = 64 := by
  simp only [finalHash, Proof.Argon2.wordList_length, Vector.length_toList]

/-- The output after `j` iterations. -/
abbrev chainOut (V : List Byte) (j : Nat) : List Byte := V.take 32 ++ chainPrefixes j V

theorem chainOut_length {V : List Byte} (hV : V.length = 64) (j : Nat) :
    (chainOut V j).length = 32 + 32 * j := by
  simp only [chainOut, List.length_append, List.length_take, hV, Proof.Argon2.chainPrefixes_length]
  omega

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `cmpLeft`: CF is whether fewer than 65 bytes are left. -/
theorem cmp_ok {s : State} (b : Body s₀ s) {xs : List Byte} (o : Out s₀ s xs) :
    WP isa (.block cmpLeft) s fun t => t.cf = some (decide (ol s₀ - xs.length < 65)) ∧
      Keeps (scr s₀) (esp₀ s₀) s t ∧ t.mem = s.mem := by
  have hs := hp.scr_fits
  have hol : ol s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  unfold cmpLeft
  have rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ =>
    wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ⟨?_, ?_, by rw [f₂.mem, u₁.mem]⟩
  · rw [cf₂, u₁.gpr, o.left, Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega)]; rfl
  · exact Keeps.same (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.gpr, u₁.other _ (by decide)])
      (by rw [f₂.gpr, u₁.other _ (by decide)]) (by rw [f₂.mem, u₁.mem]) (by rw [f₂.rd, u₁.rd])
      (by rw [f₂.wr, u₁.wr])

/-- What the chain keeps between iterations. -/
structure ChainInv (s₀ : State) (e : BitVec 32) (V : List Byte) (j : Nat) (s : State) : Prop where
  body : Body s₀ s
  ebp : s.gpr .ebp = e
  out : Out s₀ s (chainOut V j)
  digest : digest s₀ s = chainDigest j V

/-- One iteration. -/
theorem iter_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 32 + 32 * j + 32 ≤ ol s₀) :
    WP isa (.seq (.block [.mov .edx (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) s
      fun t => ChainInv s₀ e V (j + 1) t ∧
        t.cf = some (decide (ol s₀ - (32 + 32 * (j + 1)) < 65)) := by
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : Keeps (scr s₀) (esp₀ s₀) s s₁ := Keeps.same (u₁.other _ (by decide)) (u₁.other _ (by decide))
    (u₁.other _ (by decide)) u₁.mem u₁.rd u₁.wr
  have b₁ := h.body.keeps hp k₁
  refine WP.seq ((next_ok (b₁.ctx hp) (n := 64) u₁.gpr (by decide) (by decide)).mono
    fun s₂ ⟨d₂, k₂⟩ => ?_)
  have K₂ := k₁.trans k₂
  have b₂ := h.body.keeps hp K₂
  have o₂ := h.out.keeps hp K₂
  have hlen := chainOut_length hV j
  refine WP.seq ((emit_ok hp b₂ o₂ (by rw [hlen]; exact hl)).mono fun s₃ ⟨b₃, e₃, o₃, d₃⟩ => ?_)
  have dg : digest s₀ s₂ = chainDigest (j + 1) V := by
    rw [chainDigest_succ', ← h.digest, Proof.Argon2.H_stream,
      List.take_of_length_le (by rw [finalHash_length])]
    rw [u₁.mem] at d₂
    exact d₂
  have xs₃ : chainOut V j ++ (digest s₀ s₂).take 32 = chainOut V (j + 1) := by
    rw [dg, chainDigest_succ', chainOut, chainOut, chainPrefixes_succ', List.append_assoc]
  rw [xs₃] at o₃
  refine (cmp_ok hp b₃ o₃).mono fun t ⟨cf, k, m⟩ => ⟨⟨b₃.keeps hp k, ?_, o₃.keeps hp k, ?_⟩, ?_⟩
  · rw [k.ebp, e₃, K₂.ebp, h.ebp]
  · show bytesAt _ _ _ = _
    rw [m]
    exact d₃.trans dg
  · rw [cf, chainOut_length hV]

/-- The chain: iterations while more than 64 bytes are left. -/
theorem chain_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 65 ≤ ol s₀ - (32 + 32 * j)) :
    WP isa chain s fun t => ∃ j', ChainInv s₀ e V j' t ∧ 33 ≤ ol s₀ - (32 + 32 * j') ∧
      ol s₀ - (32 + 32 * j') ≤ 64 ∧ 32 + 32 * j' ≤ ol s₀ := by
  unfold chain
  refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ j', m = ol s₀ - (32 + 32 * j') ∧ ChainInv s₀ e V j' t ∧ 65 ≤ m)
    ?_ (ol s₀ - (32 + 32 * j)) s ⟨j, rfl, h, hl⟩
  rintro m t ⟨j', rfl, hi, hm⟩
  refine (iter_ok hp hV hi (by omega)).mono fun u ⟨hu, cf⟩ => ?_
  by_cases hc : ol s₀ - (32 + 32 * (j' + 1)) < 65
  · refine .inl ⟨?_, j' + 1, hu, by omega, by omega, by omega⟩
    show u.cf.map (!·) = some false
    rw [cf]; simp [hc]
  · refine .inr ⟨?_, _, by omega, j' + 1, rfl, hu, by omega⟩
    show u.cf.map (!·) = some true
    rw [cf]; simp [hc]

end

end VG.Proof.Argon2.X86.HPrime
