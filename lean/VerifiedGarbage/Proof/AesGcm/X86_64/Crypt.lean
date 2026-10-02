import VerifiedGarbage.Proof.AesGcm.X86_64.Flush

/-!
# AES-GCM on x86-64: counter mode over a piece (`crypt`)

Untrusted: everything here is checked by Lean. `crypt` XORs the keystream,
from byte `P` of the text on, into the `rbp` bytes at `r12`, where `rbx` is
`P mod 16` and the state holds the counter block and the keystream block for
`P` bytes (`Proof.Gcm.Ctr`): the rest of the keystream block (`cryptHead`),
whole blocks with `vg_aes_ctr32` (`cryptWhole`), then a new keystream block
for the last bytes (`cryptTail`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt aesWith)
open VG.Proof.Gcm (Ctr xorKs)

/-- A buffer of `n` bytes at `D` that the code may read and write, apart from
the context, the state, `W` and the stack below `SP`. -/
structure DataW (Ctx St W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  ok : DataOk St W SP s D n
  wr : Covers [⟨D, n⟩] s.wr
  ctx : (⟨Ctx, 256⟩ : Region).Disjoint ⟨D, n⟩

theorem DataW.of_eq {Ctx St W SP : Addr} {s s' : State} {D : Addr} {n : Nat} (h : DataW Ctx St W SP s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DataW Ctx St W SP s' D n :=
  ⟨h.ok.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.ctx⟩

theorem DataW.drop {Ctx St W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : DataW Ctx St W SP s D n)
    {k : Nat} (hk : k ≤ n) : DataW Ctx St W SP s (D + BitVec.ofNat 64 k) (n - k) :=
  ⟨h.ok.drop hk, covers_off h.wr (by omega) h.ok.lt, h.ctx.sub_right (Offset.sub_base D (by omega))⟩

theorem DataW.take {Ctx St W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : DataW Ctx St W SP s D n)
    {k : Nat} (hk : k ≤ n) : DataW Ctx St W SP s D k :=
  ⟨h.ok.take hk, fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.wr a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩,
   h.ctx.sub_right (Region.sub_prefix hk)⟩

/-- The cipher of the key schedule in the context, for `R` rounds. -/
abbrev ciphOf (m : Mem) (Ctx : Addr) (R : Nat) : Block → Block :=
  aesWith R (bytesAt m Ctx (16 * (R + 1)))

/-- The number of rounds is kept at `W + 176`. -/
def RoundsAt (m : Mem) (W : Addr) (R : Nat) : Prop :=
  m.readW (W + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 R ∧ (R = 10 ∨ R = 12 ∨ R = 14)

/-- The regions `crypt` writes. -/
abbrev crFrame (St W SP D : Addr) (n : Nat) : List Region :=
  [⟨D, n⟩, ⟨St + BitVec.ofNat 64 48, 32⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, below SP 8]

/-- Before `crypt`: `P` bytes of text so far, `n` bytes at `D` to go. -/
structure CrIn (Ctx St W SP : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (s : State) :
    Prop where
  env : Env Ctx St W SP s
  r12 : s.gpr .r12 = D
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  rbx : s.gpr .rbx = BitVec.ofNat 64 (P % 16)
  data : DataW Ctx St W SP s D n
  rounds : RoundsAt s.mem W R

/-- Part of the way: `j` bytes done, from `m₀`. -/
structure CrMid (Ctx St W SP : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (m₀ : Mem)
    (j : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  le : j ≤ n
  r12 : s.gpr .r12 = D + BitVec.ofNat 64 j
  rbp : s.gpr .rbp = BitVec.ofNat 64 (n - j)
  data : DataW Ctx St W SP s D n
  rounds : RoundsAt s.mem W R
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + j)
  done : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D j = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ D j)
  rest : bytesAt s.mem (D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (D + BitVec.ofNat 64 j) (n - j)
  whole : n - j = 0 ∨ (P + j) % 16 = 0
  frame : Frame (crFrame St W SP D n) m₀ s.mem

/-- After `crypt`. -/
structure CrOut (Ctx St W SP : Addr) (R : Nat) (icb : Block) (P : Nat) (D : Addr) (n : Nat) (m₀ : Mem)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  rounds : RoundsAt s.mem W R
  ctr : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    Ctr s.mem (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb (P + n)
  out : Ctr m₀ (St + BitVec.ofNat 64 48) (St + BitVec.ofNat 64 64) (ciphOf m₀ Ctx R) icb P →
    bytesAt s.mem D n = xorKs (ciphOf m₀ Ctx R) icb P (bytesAt m₀ D n)
  frame : Frame (crFrame St W SP D n) m₀ s.mem

section
variable {Ctx St W SP : Addr} (L : Lay Ctx St W SP)
include L

theorem ctx_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W SP s D n) :
    ∀ r ∈ crFrame St W SP D n, (⟨Ctx, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.ctx
  · exact L.cs.sub_right (Lay.stSub (by decide))
  · exact L.cw'.sub_right (Lay.wSub (by decide))
  · exact L.kc.symm

theorem rounds_crFrame {s : State} {D : Addr} {n : Nat} (hd : DataW Ctx St W SP s D n) :
    ∀ r ∈ crFrame St W SP D n, (⟨W + BitVec.ofNat 64 176, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (by decide))).symm
  · exact (L.st_w (by decide) (.inr ⟨by decide, by decide⟩)).symm
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

omit L in
theorem ciph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨Ctx, 256⟩ : Region).Disjoint r)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : ciphOf m' Ctx R = ciphOf m Ctx R := by
  have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  simp only [ciphOf]
  rw [bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega)]

omit L in
theorem rounds_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 176, 8⟩ : Region).Disjoint r) {R : Nat} (h : RoundsAt m W R) :
    RoundsAt m' W R :=
  ⟨by rw [hf.readW (r := ⟨W + BitVec.ofNat 64 176, 8⟩) (Region.contains_self _ _) hd (by decide)]; exact h.1, h.2⟩

end

end VG.Proof.AesGcm.X86_64
