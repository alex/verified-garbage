import VerifiedGarbage.Proof.AesGcm.Arm.Flush

/-!
# AES-GCM on ARMv7: counter mode over a piece (`crypt`)

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `r5` bytes at `r4`, where `r6` is
`P mod 16` and the state holds the counter block and the keystream block for
`P` bytes (`Proof.Gcm.Ctr`): the rest of the keystream block (`cryptHead`),
whole blocks with `vg_aes_ctr32` (`cryptWhole`), then a new keystream block
for the last bytes (`cryptTail`). The number of rounds is in `r8`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state, `W` and the stack below `sp`. -/
structure DataW (c st w sp k7 k8 : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  ok : DataOk st w sp s D n
  wr : Covers [⟨State.addr D, n⟩] s.wr
  ctx : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr D, n⟩

theorem DataW.of_eq {c st w sp k7 k8 : BitVec 32} {s s' : State} {D : BitVec 32} {n : Nat}
    (h : DataW c st w sp k7 k8 s D n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataW c st w sp k7 k8 s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.sub {c st w sp k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : DataW c st w sp k7 k8 s D n)
    {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : DataW c st w sp k7 k8 s (D + BitVec.ofNat 32 j) k := by
  have ha := h.ok.addr (j := j) (by omega)
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  exact ⟨h.ok.sub hjk hk, by rw [ha]; exact covers_off h.wr hjk h.ok.lt, by rw [ha]; exact h.ctx.sub_right hs⟩

theorem DataW.take {c st w sp k7 k8 : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : DataW c st w sp k7 k8 s D n)
    {k : Nat} (hk : k ≤ n) : DataW c st w sp k7 k8 s D k :=
  ⟨h.ok.take hk, covers_prefix h.wr hk, h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (C : Addr) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m C (16 * (R + 1)))

/-- The regions `crypt` writes. -/
abbrev crFrame (st w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr D, n⟩, ⟨State.addr st + BitVec.ofNat 64 48, 32⟩, ⟨State.addr w + BitVec.ofNat 64 512, 2048⟩,
    below sp]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go, `R`
rounds in `r8`. -/
structure CrIn (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (s : State) :
    Prop where
  env : Env c st w sp k7 k8 s
  r4 : s.gpr .r4 = D
  r5 : s.gpr .r5 = BitVec.ofNat 32 n
  r6 : s.gpr .r6 = BitVec.ofNat 32 (P % 16)
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  data : DataW c st w sp k7 k8 s D n

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  le : j ≤ n
  r4 : s.gpr .r4 = D + BitVec.ofNat 32 j
  r5 : s.gpr .r5 = BitVec.ofNat 32 (n - j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  data : DataW c st w sp k7 k8 s D n
  ctr : Ctr m₀ (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64) (ciphOf m₀ (State.addr c) R)
      icb P →
    Ctr s.mem (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64) (ciphOf m₀ (State.addr c) R)
      icb (P + j)
  done : Ctr m₀ (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64)
      (ciphOf m₀ (State.addr c) R) icb P →
    bytesAt s.mem (State.addr D) j = xorKs (ciphOf m₀ (State.addr c) R) icb P (bytesAt m₀ (State.addr D) j)
  rest : bytesAt s.mem (State.addr D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (State.addr D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame st w sp D n) m₀ s.mem

/-- After `crypt`. -/
structure CrOut (c st w sp k7 k8 : BitVec 32) (R : Nat) (icb : Block) (P : Nat) (D : BitVec 32) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env c st w sp k7 k8 s
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  ctr : Ctr m₀ (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64) (ciphOf m₀ (State.addr c) R)
      icb P →
    Ctr s.mem (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64) (ciphOf m₀ (State.addr c) R)
      icb (P + n)
  out : Ctr m₀ (State.addr st + BitVec.ofNat 64 48) (State.addr st + BitVec.ofNat 64 64)
      (ciphOf m₀ (State.addr c) R) icb P →
    bytesAt s.mem (State.addr D) n = xorKs (ciphOf m₀ (State.addr c) R) icb P (bytesAt m₀ (State.addr D) n)
  frame : Frame (crFrame st w sp D n) m₀ s.mem

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

theorem ctx_crFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataW c st w sp k7 k8 s D n) :
    ∀ r ∈ crFrame st w sp D n, (⟨State.addr c, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

omit L in
theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨State.addr c, 256⟩ : Region).Disjoint r) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    ciphOf m' (State.addr c) R = ciphOf m (State.addr c) R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [ciphOf]
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

end

/-- `[D, D + j)` and `[D + j, D + n)` are apart. -/
theorem split_disj {D : Addr} {j n : Nat} (hj : j ≤ n) (hn : n < 2 ^ 64) :
    (⟨D, j⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 j, n - j⟩ := by
  have := Offset.disjoint D (d := 0) (n := j) (e := j) (k := n - j) (.inl (by omega)) (by omega) (by omega)
  simpa using this

/-- The bytes done so far and the next ones. -/
theorem done_append {m m₀ : Mem} {ciph : Block → Block} {icb : Block} {P : Nat} {D : Addr} {j l : Nat}
    (h₁ : bytesAt m D j = xorKs ciph icb P (bytesAt m₀ D j))
    (h₂ : bytesAt m (D + BitVec.ofNat 64 j) l = xorKs ciph icb (P + j) (bytesAt m₀ (D + BitVec.ofNat 64 j) l)) :
    bytesAt m D (j + l) = xorKs ciph icb P (bytesAt m₀ D (j + l)) := by
  rw [bytesAt_add, bytesAt_add, Proof.Gcm.xorKs_append, h₁, h₂, length_bytesAt]

theorem ctr32_single (ciph : Block → Block) (icb x : Block) : Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

end VG.Proof.AesGcm.Arm
