import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
import VerifiedGarbage.Proof.Sha512.Md

/-!
# The SHA-512 family's length field and digest on AArch64, for PBKDF2's iteration

Untrusted: everything here is checked by Lean. The SHA-512 family's streaming
code on AArch64 is not the generic Merkle–Damgård code, so the length field
and digest code PBKDF2's iteration uses (`Impl.Pbkdf2.AArch64.sha512`: the
128-bit big-endian bit count, `len128`, and the eight big-endian 64-bit words
of the hash value, `out64`) are shown to do what `Shape` asks here.
-/

namespace VG.Proof.Pbkdf2.AArch64

open VG VG.AArch64 VG.Proof.MdStream VG.Proof.MdStream.AArch64
open VG.Impl.Pbkdf2.AArch64 (len128 out64)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)

theorem wordBytes_length (x : BitVec 64) : (Spec.Sha512.wordBytes x).length = 8 := by simp [Spec.Sha512.wordBytes]

/-- `out64 n` writes the `n` 64-bit words at `x19` to `x21`, big-endian. -/
theorem out64_ok {n : Nat} (hn : 8 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x19) (8 * n)) (hout : InRegions s₀.wr (s₀.gpr .x21) (8 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .x19, 8 * n⟩ ⟨s₀.gpr .x21, 8 * n⟩) :
    WP isa (.block (out64 n)) s₀ fun s' =>
      (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = writeBytes s₀.mem (s₀.gpr .x21)
        ((List.range n).flatMap fun k => Spec.Sha512.wordBytes (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64)) := by
  let f : Nat → List Byte := fun k => Spec.Sha512.wordBytes (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64)
  have hflat : ∀ k, ((List.range k).flatMap f).length = 8 * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => wordBytes_length _), List.map_const',
      List.sum_replicate_nat, List.length_range, Nat.mul_comm]
  -- Words `[n - j, n)` are left, the others written.
  suffices h : ∀ j ≤ n, ∀ s, (∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.sp = s₀.sp → s.mem = writeBytes s₀.mem (s₀.gpr .x21) ((List.range (n - j)).flatMap f) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap fun k =>
        ([.ldr .x .x9 .x19 (8 * k), .rev .x9 .x9, .str .x .x9 .x21 (8 * k)] : List Instr)))
        s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
          s'.sp = s₀.sp ∧ s'.mem = writeBytes s₀.mem (s₀.gpr .x21) ((List.range n).flatMap f) by
    have := h n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl rfl
      (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
    rwa [Nat.sub_self, List.drop_zero] at this
  intro j
  induction j with
  | zero =>
    intro _ s g rd wr sp m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨g, rd, wr, sp, m⟩
  | succ j ih =>
    intro hj s g rd wr sp m
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range]
    rw [show n - (j + 1) + 1 = n - j by omega]
    have hoff : 8 * (n - (j + 1)) + 8 ≤ 8 * n := by omega
    -- The word read is not yet overwritten.
    have hread : s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64 =
        s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64 := by
      rw [m]
      refine (writeBytes_frame _ _ _ (R := ⟨s₀.gpr .x21, 8 * n⟩) ?_).readW
        (r := ⟨s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1))), 8⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        omega
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset hoff (by omega))
    simp only [List.cons_append, List.nil_append]
    refine wp_ldr (a := s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) ⟨by omega, by omega⟩
      (by rw [g _ (by decide)]) (by rw [rd, wr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
    refine wp_rev fun s₂ u₂ => wp_str (a := s₀.gpr .x21 + BitVec.ofNat 64 (8 * (n - (j + 1))))
      ⟨by omega, by omega⟩ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), g _ (by decide)])
      (by rw [u₂.wr, u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₃ g₃ => ?_
    refine ih (by omega) s₃ (fun r h => by rw [g₃.gpr, u₂.other r h, u₁.other r h, g r h])
      (by rw [g₃.rd, u₂.rd, u₁.rd, rd]) (by rw [g₃.wr, u₂.wr, u₁.wr, wr]) (by rw [g₃.sp, u₂.sp, u₁.sp, sp]) ?_
    rw [g₃.mem, u₂.mem, u₂.gpr, u₁.gpr, u₁.mem, hread,
      show rev64 (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) =
        (if true then rev64 (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) else
          s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) from rfl,
      writeW64, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ,
      List.flatMap_append, List.flatMap_singleton,
      ← writeBytes_append _ _ _ _ (by simp only [hflat, f, wordBytes_length]; omega), hflat]
    rfl

/-- The digest of the SHA-512 family's hash value is its eight words, big-endian. -/
theorem sha512_digest_eq (mem : Mem) (p : Addr) :
    Proof.Sha512.md.digest (Proof.Sha512.md.stateAt mem p) = (List.range 8).flatMap fun k =>
      Spec.Sha512.wordBytes (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
  simp [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ]

/-- `len128 176` stores the 128-bit big-endian bit count of the byte count
in `x22` at `x19 + 176`, the end of the block. -/
theorem len128_ok {s : State} (hout : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 176) 16) :
    WP isa (.block (len128 176)) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 176) (Proof.Sha512.md.lenOf (s.gpr .x22)) := by
  have e184 : s.gpr .x19 + BitVec.ofNat 64 176 + BitVec.ofNat 64 8 = s.gpr .x19 + BitVec.ofNat 64 184 :=
    Offset.add_add _ _ _
  unfold len128
  simp only [List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₁ u₁ => wp_rev fun s₂ u₂ => wp_str (a := s.gpr .x19 + BitVec.ofNat 64 176)
    (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.wr, u₁.wr]; simpa using InRegions.offset (off := 0) (m := 8) hout (by omega) (by omega))
    fun s₃ g₃ => ?_
  have h19 : s₃.gpr .x19 = s.gpr .x19 := by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  have h22 : s₃.gpr .x22 = s.gpr .x22 := by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  refine (len64_ok (d := 184) (be := true) (by decide) (by
    rw [h19, g₃.wr, u₂.wr, u₁.wr, ← e184]; exact InRegions.offset hout (by omega) (by omega))).mono
    fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r h h' => by rw [g r h h', g₃.gpr, u₂.other r h, u₁.other r h],
      by rw [rd, g₃.rd, u₂.rd, u₁.rd], by rw [wr, g₃.wr, u₂.wr, u₁.wr], by rw [sp, g₃.sp, u₂.sp, u₁.sp], ?_⟩
  rw [m, h19, h22, g₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr,
    show rev64 (s.gpr .x22 >>> 61) = (if true then rev64 (s.gpr .x22 >>> 61) else s.gpr .x22 >>> 61) from rfl,
    writeW64, ← e184, show (8 : Nat) = (bytes64 true (s.gpr .x22 >>> 61)).length from rfl,
    writeBytes_append _ _ _ _ (by rw [bytes64_length, bytes64_length]; omega), Proof.Sha512.lenOf_split]
  rfl

/-- The SHA-512 family's length field and digest, as PBKDF2's iteration uses them. -/
theorem sha512_shape : Shape (P := Impl.Pbkdf2.AArch64.sha512) Proof.Sha512.md where
  lenKeepsV := by decide +kernel
  outKeepsV := by decide +kernel
  len _ hout := len128_ok hout
  out _ hin hout hd := by
    refine (out64_ok (n := 8) (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, sp, m⟩ =>
      ⟨g, rd, wr, sp, ?_⟩
    rw [m, sha512_digest_eq]

end VG.Proof.Pbkdf2.AArch64
