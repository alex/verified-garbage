import VerifiedGarbage.Proof.Sha512.X86.Stream.Update
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Sha512.Word64

/-!
# Streaming SHA-512 on x86 (32-bit): `finalize`

The generic `finalize` (`Proof/MdStream/X86/`) for the SHA-512 family, given
what its length field and digest do (`shape`): the length in bits as a 128-bit
big-endian integer, `count >> 61` then `count << 3`, and the words of the hash
value big-endian, each the big-endian bytes of its high half, then of its low
half.
-/

namespace VG.Proof.Sha512.X86.Stream

open VG VG.X86 VG.Proof.MdStream VG.Proof.MdStream.X86
open VG.Impl.MdStream.X86 (len64Of out64)
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append)

/-- `count >> 61`, from the halves of `count`. -/
theorem shr61 (hi lo : BitVec 32) : (hi ++ lo) >>> 61 = (0 : BitVec 32) ++ hi >>> 29 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_append]
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or,
    ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow]
  have := lo.isLt
  omega

/-- The length field: `count >> 61`, then `8 count`, big-endian. -/
theorem lenOf_eq (hi lo : BitVec 32) :
    md.lenOf (hi ++ lo) = bytes32 true 0 ++ bytes32 true (hi >>> 29) ++
      bytes64 true (BitVec.ofNat 64 (8 * (hi ++ lo).toNat)) := by
  have e := Proof.Sha512.lenOf_split (hi ++ lo)
  rw [shr61] at e
  rw [show md.lenOf (hi ++ lo) = Spec.Sha512.wordBytes ((0 : BitVec 32) ++ hi >>> 29) ++
    Spec.Sha512.wordBytes (BitVec.ofNat 64 (8 * (hi ++ lo).toNat)) from e,
    show Spec.Sha512.wordBytes = bytes64 true from rfl, bytes64_halves]
  rfl

theorem len_ok (s : State) (hfit : (s.gpr .ebx).toNat + (params.N + params.B) ≤ 2 ^ 32)
    (hlo : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (params.so + 16)) 4)
    (hhi : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (params.so + 20)) 4)
    (ho : ∀ d, params.N + params.B - params.L ≤ d → d + 4 ≤ params.N + params.B →
      InRegions s.wr (addr (s.gpr .ebx) d) 4) :
    WP isa (.block params.len) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (params.N + params.B - params.L))
        (md.lenOf (s.mem.readW (addr (s.gpr .ebp) (params.so + 20)) 32 ++
          s.mem.readW (addr (s.gpr .ebp) (params.so + 16)) 32)) := by
  have hfit' : (s.gpr .ebx).toNat + 192 ≤ 2 ^ 32 := hfit
  have ho' : ∀ d, 176 ≤ d → d + 4 ≤ 192 → InRegions s.wr (addr (s.gpr .ebx) d) 4 := ho
  show WP isa (.block (Impl.MdStream.X86.loadCount 224 ++ ([.mov .edx (.imm 0), .store (at_ .ebx 176) .edx,
    .mov .edx (.reg .ecx), .shift .shr .edx 29, .bswap .edx, .store (at_ .ebx 180) .edx] ++
    len64Of 184 true))) s fun s' => _ ∧ _ ∧ _ ∧ s'.mem = writeBytes s.mem ((s.gpr .ebx).setWidth 64 +
      BitVec.ofNat 64 176) (md.lenOf (s.mem.readW (addr (s.gpr .ebp) 244) 32 ++
        s.mem.readW (addr (s.gpr .ebp) 240) 32))
  refine loadCount_ok hlo hhi fun s₂ g₂ m₂ rd₂ wr₂ ha hc => ?_
  generalize s.mem.readW (addr (s.gpr .ebp) (224 + 16)) 32 = lo at ha
  generalize s.mem.readW (addr (s.gpr .ebp) (224 + 20)) 32 = hi at hc
  have hb₂ : s₂.gpr .ebx = s.gpr .ebx := g₂ _ (by decide) (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_movi fun s₃ u₃ => wp_store (a := addr (s.gpr .ebx) 176)
    (by show addr (s₃.gpr .ebx) 176 = _; rw [u₃.other _ (by decide), hb₂]) (by rw [u₃.wr, wr₂]; exact ho' 176 (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_mov fun s₅ u₅ => wp_shr (by decide) fun s₆ u₆ => wp_bswap fun s₇ u₇ => ?_
  have g₇ : ∀ r, r ≠ .edx → s₇.gpr r = s₂.gpr r := fun r h => by
    rw [u₇.other r h, u₆.other r h, u₅.other r h, u₄.gpr, u₃.other r h]
  refine wp_store (a := addr (s.gpr .ebx) 180) (by show addr (s₇.gpr .ebx) 180 = _; rw [g₇ _ (by decide), hb₂])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂]; exact ho' 180 (by omega) (by omega)) fun s₈ u₈ => ?_
  have g₈ : ∀ r, r ≠ .edx → s₈.gpr r = s₂.gpr r := fun r h => by rw [u₈.gpr, g₇ r h]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂]
  refine (len64Of_ok (d := 184) (be := true) (hi := hi) (lo := lo) (by rw [g₈ _ (by decide), hb₂]; omega)
    (by rw [g₈ _ (by decide), ha]) (by rw [g₈ _ (by decide), hc])
    (by rw [wr₈, g₈ _ (by decide), hb₂]; exact ho' 184 (by omega) (by omega))
    (by rw [wr₈, g₈ _ (by decide), hb₂]; exact ho' 188 (by omega) (by omega))).mono
    fun s' ⟨g', rd', wr', m'⟩ => ⟨fun r h1 h2 h3 => by rw [g' r h1 h2 h3, g₈ r h3, g₂ r h1 h2],
      by rw [rd', u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂], by rw [wr', wr₈], ?_⟩
  have v₃ : s₃.gpr .edx = bswap 0 := by rw [u₃.gpr]; decide
  have v₇ : s₇.gpr .edx = bswap (hi >>> 29) := by rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), hc]
  have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => writeW32 m a true x
  simp only [ite_true] at w
  have e₀ : addr (s.gpr .ebx) 176 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 176 := addr_eq (by omega)
  have e₁ : addr (s.gpr .ebx) 180 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 176 +
      BitVec.ofNat 64 (bytes32 true 0).length := by rw [addr_eq (by omega), bytes32_length, add_ofNat]
  have e₂ : (s₈.gpr .ebx).setWidth 64 + BitVec.ofNat 64 184 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 176 +
      BitVec.ofNat 64 (bytes32 true 0 ++ bytes32 true (hi >>> 29)).length := by
    rw [g₈ _ (by decide), hb₂, List.length_append, bytes32_length, bytes32_length, add_ofNat]
  rw [m', e₂, u₈.mem, v₇, u₇.mem, u₆.mem, u₅.mem, u₄.mem, v₃, u₃.mem, m₂, w, w, e₀, e₁,
    writeBytes_append _ _ _ _ (by simp [bytes32_length]),
    writeBytes_append _ _ _ _ (by simp [bytes32_length, bytes64_length]), lenOf_eq]

theorem digest_eq (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 32) := by
  have h : md.digest (md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
    simp [md, Spec.Sha512.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, bytes64,
      Spec.Sha512.wordBytes]
  have e : ∀ k, bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) =
      bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k + 4)) 32) ++
        bytes32 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 32) := fun k => by
    rw [Proof.Sha512.Word64.readW64, bytes64_halves, ← add_ofNat]
    rfl
  rw [h]
  exact congrArg (fun f => (List.range 8).flatMap f) (funext e)

theorem shape : Shape (P := params) md where
  len s hfit hlo hhi ho := len_ok s hfit hlo hhi ho
  out _ hbx hax hin hout hd := by
    refine (out64_ok (n := 8) (by decide) hbx hax hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ =>
      ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

namespace Finalize

theorem finalize_verified : Verified X86.target Impl.Sha512.X86.Stream.finalize Proof.Sha512.finalizeX86 :=
  MdStream.X86.Finalize.verified_ro (name := "vg_sha512_compress") dims shape callee
    (VG.Taint.constantTime (A := taint) (MdStream.X86.Finalize.τ₀ params 272)
      (fun _ _ h₁ h₂ hp => MdStream.X86.Finalize.agree₀ dims h₁ h₂ hp) (by taint_decide))

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86.Finalize.satR params 272

end Finalize

end VG.Proof.Sha512.X86.Stream
