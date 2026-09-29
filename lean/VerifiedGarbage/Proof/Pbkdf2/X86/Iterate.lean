import VerifiedGarbage.Proof.Pbkdf2.X86.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256's iteration on x86 (32-bit)

Untrusted: everything here is checked by Lean. The prologue, the epilogue,
and `Verified`. Constant time is proven by the taint analysis: the argument
words holding `t` and `scratch` are the bases of the two writable regions,
and the code keeps them in `ebx` and `ebp` across the calls, so the
registers `vg_sha256_compress` saves in its scratch space and restores are
known to keep their public values. The proof is written against a contract
under which the code only reads its arguments (which it does), and moved to
the shared contract with `Verified.narrowTo`.
-/

namespace VG.Proof.Pbkdf2.X86

open VG VG.X86 VG.Impl.Pbkdf2.X86
open VG.Impl.Sha256.X86 (at_)
open VG.Impl.Sha256.X86.Stream (saved save restore)
open VG.Impl.Hmac.X86 (copyWord)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_test ea_at addr_toNat
  readW_writeW_addr ofNat_beq_zero)
open VG.Proof.Hmac.X86 (copyWords_ok)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self bytesAt_writeBytes_sep)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame writeBytes_nil)
open VG.Proof.Pbkdf2.Memory (frame_bytesAt contains_base writeW_bytes writeBytes_append' iterate_congr
  add_ofNat)
open VG.Spec.Sha256 (bytesAt stateAt Repr)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)

/-! ## Arguments and the return address -/

theorem arg_sub {s₀ : State} (hp : Pre s₀) {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [addr_eq (by omega)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_in {s₀ : State} (hp : Pre s₀) {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by
      rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem ret_stk {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-! ## Saving our caller's registers -/

/-- The memory after saving our caller's registers. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) 112) (s₀.gpr .ebx)).writeW (addr (scr s₀) 116) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 120) (s₀.gpr .edi)).writeW (addr (scr s₀) 124) (s₀.gpr .ebp)

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d, d + 4 ≤ 256 → (scR s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd => by
    rw [addr_off (len := 256) hp.scr_fit (by omega)]; exact contains_offset hd (by omega)
  simp only [saveMem]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 116 (by omega))).writeW (List.mem_singleton_self _) _
    (c 120 (by omega))).writeW (List.mem_singleton_self _) _ (c 124 (by omega))

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  have hs := hp.scr_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 256 → e + 4 ≤ 256 → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  intro p hp'
  have ha : scA s₀ + BitVec.ofNat 64 p.2 = addr (scr s₀) p.2 := by
    have := saved_off hp'
    exact (addr_off (len := 256) hp.scr_fit (by omega)).symm
  rw [ha]
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;> simp only [saveMem]
  · rw [w _ _ 112 124 (by omega) (by omega) (by omega), w _ _ 112 120 (by omega) (by omega) (by omega),
      w _ _ 112 116 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 116 124 (by omega) (by omega) (by omega), w _ _ 116 120 (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · rw [w _ _ 120 124 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-! ## The padding -/

/-- A word stored right after bytes written before. -/
theorem writeW_append (m : Mem) (q : Addr) (xs ys : List Byte) (v : BitVec 32) {a : Addr}
    (ha : a = q + BitVec.ofNat 64 xs.length)
    (hv : ((List.range (32 / 8)).map fun j => (v.setWidth (8 * (32 / 8))).extractLsb' (8 * j) 8) = ys)
    (hl : xs.length + ys.length < 2 ^ 64) :
    (writeBytes m q xs).writeW a v = writeBytes m q (xs ++ ys) := by
  rw [writeW_bytes _ _ v ys hv, writeBytes_append' _ _ _ ha hl]

theorem padding_eq : padding = [.mov .ecx (.imm 0x80), .store (at_ .ebp 224) .ecx, .mov .ecx (.imm 0),
    .store (at_ .ebp 228) .ecx, .store (at_ .ebp 232) .ecx, .store (at_ .ebp 236) .ecx,
    .store (at_ .ebp 240) .ecx, .store (at_ .ebp 244) .ecx, .store (at_ .ebp 248) .ecx,
    .mov .ecx (.imm 0x00030000), .store (at_ .ebp 252) .ecx] := rfl

/-- A store of `ecx` at `[ebp + d]`, within the scratch space. -/
theorem st_ok {s₀ : State} (hp : Pre s₀) {s : State} (hb : s.gpr .ebp = scr s₀) (hwr : s.wr = s₀.wr)
    {d : Nat} (hd : d + 4 ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (scA s₀ + BitVec.ofNat 64 d) (s.gpr .ecx)) → WP isa (.block rest) s' Q) :
    WP isa (.block (.store (at_ .ebp d) .ecx :: rest)) s Q :=
  wp_store (by rw [ea_at, hb]; exact addr_off (len := 256) hp.scr_fit (by omega)) (in_scr hp hwr hd) k

/-- The padding into `scratch[224..256)`. -/
theorem padding_ok {s₀ : State} (hp : Pre s₀) {s : State} (hb : s.gpr .ebp = scr s₀) (hwr : s.wr = s₀.wr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (scA s₀ + BitVec.ofNat 64 224) pad96 → WP isa (.block rest) s' Q) :
    WP isa (.block (padding ++ rest)) s Q := by
  simp only [padding_eq, List.cons_append, List.nil_append]
  let P := scA s₀ + BitVec.ofNat 64 224
  refine wp_movi fun s₁ u₁ => ?_
  have c₁ : s₁.gpr .ebp = scr s₀ := by rw [u₁.other _ (by decide), hb]
  refine st_ok hp c₁ (u₁.wr.trans hwr) (d := 224) (by omega) fun s₂ g₂ => ?_
  refine wp_movi fun s₃ u₃ => ?_
  have c₃ : s₃.gpr .ebp = scr s₀ := by rw [u₃.other _ (by decide), g₂.gpr, c₁]
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, g₂.wr, u₁.wr, hwr]
  have z₃ : s₃.gpr .ecx = 0 := u₃.gpr
  refine st_ok hp c₃ w₃ (d := 228) (by omega) fun s₄ g₄ => ?_
  refine st_ok hp (by rw [g₄.gpr, c₃]) (by rw [g₄.wr, w₃]) (d := 232) (by omega) fun s₅ g₅ => ?_
  refine st_ok hp (by rw [g₅.gpr, g₄.gpr, c₃]) (by rw [g₅.wr, g₄.wr, w₃]) (d := 236) (by omega) fun s₆ g₆ => ?_
  refine st_ok hp (by rw [g₆.gpr, g₅.gpr, g₄.gpr, c₃]) (by rw [g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 240) (by omega)
    fun s₇ g₇ => ?_
  refine st_ok hp (by rw [g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃]) (by rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃])
    (d := 244) (by omega) fun s₈ g₈ => ?_
  refine st_ok hp (by rw [g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃])
    (by rw [g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 248) (by omega) fun s₉ g₉ => ?_
  refine wp_movi fun s₁₀ u₁₀ => ?_
  refine st_ok hp (by rw [u₁₀.other _ (by decide), g₉.gpr, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, c₃])
    (by rw [u₁₀.wr, g₉.wr, g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, w₃]) (d := 252) (by omega) fun s₁₁ g₁₁ => ?_
  have G : ∀ r, r ≠ .ecx → s₁₁.gpr r = s.gpr r := fun r hr => by
    rw [g₁₁.gpr, u₁₀.other r hr, g₉.gpr, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, u₃.other r hr, g₂.gpr,
      u₁.other r hr]
  refine k s₁₁ G (by rw [g₁₁.rd, u₁₀.rd, g₉.rd, g₈.rd, g₇.rd, g₆.rd, g₅.rd, g₄.rd, u₃.rd, g₂.rd, u₁.rd])
    (by rw [g₁₁.wr, u₁₀.wr, g₉.wr, g₈.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, u₃.wr, g₂.wr, u₁.wr]) ?_
  have e : ∀ o : Nat, scA s₀ + BitVec.ofNat 64 (224 + o) = P + BitVec.ofNat 64 o := fun o => (add_ofNat _ _ _).symm
  have e₂ : s₂.mem = writeBytes s.mem P ([] ++ [0x80, 0, 0, 0]) := by
    rw [g₂.mem, u₁.gpr, u₁.mem, ← writeBytes_nil s.mem P]
    exact writeW_append _ _ _ _ _ (by simp [P]) (by decide) (by decide)
  have e₄ : s₄.mem = writeBytes s.mem P ([0x80, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₄.mem, z₃, u₃.mem, e₂]; exact writeW_append _ _ _ _ _ (e 4) (by decide) (by decide)
  have e₅ : s₅.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₅.mem, g₄.gpr, z₃, e₄]; exact writeW_append _ _ _ _ _ (e 8) (by decide) (by decide)
  have e₆ : s₆.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₆.mem, g₅.gpr, g₄.gpr, z₃, e₅]; exact writeW_append _ _ _ _ _ (e 12) (by decide) (by decide)
  have e₇ : s₇.mem = writeBytes s.mem P ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₇.mem, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₆]; exact writeW_append _ _ _ _ _ (e 16) (by decide) (by decide)
  have e₈ : s₈.mem = writeBytes s.mem P
      ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₈.mem, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₇]
    exact writeW_append _ _ _ _ _ (e 20) (by decide) (by decide)
  have e₉ : s₉.mem = writeBytes s.mem P
      ([0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++ [0, 0, 0, 0]) := by
    rw [g₉.mem, g₈.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, z₃, e₈]
    exact writeW_append _ _ _ _ _ (e 24) (by decide) (by decide)
  rw [g₁₁.mem, u₁₀.gpr, u₁₀.mem, e₉]
  exact writeW_append _ _ _ _ _ (e 28) (by decide) (by decide)

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ (fun s => Inv s₀ (nn s₀) s ∧ s.zf = some (decide (nn s₀ = 0))) := by
  have := hp.scr_fit; have := hp.t_fit; have := hp.u_fit; have := hp.sp_fit
  unfold prologue
  simp only [save, saved, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
  have rin : ∀ (s : State), s.rd = s₀.rd → ∀ d, 4 ≤ d → d + 4 ≤ 24 →
      InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
    fun s h₁ d h₃ h₄ => ⟨argR s₀, by simp [h₁, hp.rd], arg_in hp h₃ h₄⟩
  have sin : ∀ (s : State), s.wr = s₀.wr → ∀ d, d + 4 ≤ 256 → InRegions s.wr (addr (scr s₀) d) 4 :=
    fun s h d hd => by rw [addr_off (len := 256) hp.scr_fit (by omega)]; exact in_scr hp h hd
  -- Save our caller's registers.
  refine wp_movm (a := addr (esp₀ s₀) 20) (ea_at _ _ _) (rin _ rfl 20 (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 112) (by rw [ea_at, e₁]) (by rw [u₁.wr]; exact sin _ rfl 112 (by omega))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 116) (by rw [ea_at, u₂.gpr, e₁])
    (by rw [u₂.wr, u₁.wr]; exact sin _ rfl 116 (by omega)) fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) 120) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact sin _ rfl 120 (by omega)) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) 124) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sin _ rfl 124 (by omega)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have m₅ : s₅.mem = saveMem s₀ := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem,
      u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    rfl
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  -- The arguments, which the saves did not change.
  have ld : ∀ e, 4 ≤ e → e + 4 ≤ 24 →
      (saveMem s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => (saveMem_frame hp).readW (Region.contains_self _ _)
      (by simpa using hp.a_s.sub_left (arg_sub hp h₁ h₂)) (by decide)
  refine wp_mov fun s₆ u₆ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, u₆.other _ (by decide), sp₅])
    (by rw [u₆.rd, u₆.wr]; exact rin _ rd₅ 4 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide), sp₅])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact rin _ rd₅ 12 (by omega) (by omega)) fun s₈ u₈ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 16)
    (by rw [ea_at, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), sp₅])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact rin _ rd₅ 16 (by omega) (by omega))
    fun s₉ u₉ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 8)
    (by rw [ea_at, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      sp₅])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact rin _ rd₅ 8 (by omega) (by omega))
    fun s₁₀ u₁₀ => ?_
  have m₁₀ : s₁₀.mem = saveMem s₀ := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  have esp₁₀ : s₁₀.gpr .esp = esp₀ s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), sp₅]
  have ebp₁₀ : s₁₀.gpr .ebp = scr s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      g₅, e₁]
  have esi₁₀ : s₁₀.gpr .esi = key s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.mem, m₅,
      ld 4 (by omega) (by omega)]; rfl
  have edi₁₀ : s₁₀.gpr .edi = arg s₀ 2 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.mem, u₆.mem, m₅,
      ld 12 (by omega) (by omega)]; rfl
  have ebx₁₀ : s₁₀.gpr .ebx = tP s₀ := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.mem, u₇.mem, u₆.mem, m₅, ld 16 (by omega) (by omega)]; rfl
  have edx₁₀ : s₁₀.gpr .edx = uP s₀ := by
    rw [u₁₀.gpr, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅, ld 8 (by omega) (by omega)]; rfl
  -- `U` into the block.
  refine copyWords_ok (src := .edx) (dst := .ebp) (by decide) (by decide) (o₁ := 0) (o₂ := 192) 8 _ s₁₀ _
    edx₁₀ ebp₁₀ (by omega) (by omega)
    (fun j hj => by
      rw [addr_off (d := 0 + 4 * j) (len := 32) hp.u_fit (by omega)]; exact in_u hp rd₁₀ (by omega))
    (fun j hj => by rw [addr_off (d := 192 + 4 * j) (len := 256) hp.scr_fit (by omega)]; exact in_scr hp wr₁₀ (by omega))
    (Region.Disjoint.sep hp.u_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega)))
    fun s₁₁ g₁₁ rd₁₁ wr₁₁ m₁₁ => ?_
  -- `T` into the scratch space.
  refine copyWords_ok (src := .ebx) (dst := .ebp) (by decide) (by decide) (o₁ := 0) (o₂ := 160) 8 _ s₁₁ _
    (by rw [g₁₁ _ (by decide), ebx₁₀]) (by rw [g₁₁ _ (by decide), ebp₁₀]) (by omega) (by omega)
    (fun j hj => by
      rw [addr_off (d := 0 + 4 * j) (len := 32) hp.t_fit (by omega), wr₁₁]; exact InRegions.right (in_t hp wr₁₀ (by omega)))
    (fun j hj => by rw [addr_off (d := 160 + 4 * j) (len := 256) hp.scr_fit (by omega), wr₁₁]; exact in_scr hp wr₁₀ (by omega))
    (Region.Disjoint.sep hp.t_s (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega)))
    fun s₁₂ g₁₂ rd₁₂ wr₁₂ m₁₂ => ?_
  refine padding_ok hp (by rw [g₁₂ _ (by decide), g₁₁ _ (by decide), ebp₁₀]) (by rw [wr₁₂, wr₁₁, wr₁₀])
    fun s₁₃ g₁₃ rd₁₃ wr₁₃ m₁₃ => ?_
  refine wp_test fun s₁₄ f₁₄ z₁₄ => WP.block_nil ?_
  have G : ∀ r, r ≠ .ecx → s₁₄.gpr r = s₁₀.gpr r := fun r h => by rw [f₁₄.gpr, g₁₃ r h, g₁₂ r h, g₁₁ r h]
  simp only [BitVec.add_zero, Nat.reduceMul] at m₁₁ m₁₂
  have hm : s₁₄.mem = writeBytes (writeBytes (writeBytes s₁₀.mem (blkA s₀) (bytesAt s₁₀.mem (uA s₀) 32))
      (TA s₀) (bytesAt s₁₁.mem (tA s₀) 32)) (scA s₀ + BitVec.ofNat 64 224) pad96 := by
    rw [f₁₄.mem, m₁₃, m₁₂, m₁₁]
  have fU : Frame [sR s₀ 192 32, sR s₀ 160 32, sR s₀ 224 32] s₁₀.mem s₁₄.mem := by
    rw [hm]
    exact (((writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono
      (by simp)).trans
      ((writeBytes_frame _ _ _ (R := sR s₀ 160 32) (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))).mono
        (by simp))).trans
      ((writeBytes_frame _ _ _ (R := sR s₀ 224 32) (contains_base (by decide))).mono (by simp))
  have F₁₀ : Frame [scR s₀] s₀.mem s₁₀.mem := by rw [m₁₀]; exact saveMem_frame hp
  have F' : Frame [scR s₀] s₀.mem s₁₄.mem :=
    F₁₀.trans (fU.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨scR s₀, by simp, scr_sub s₀ (by omega)⟩)
  have hU₁₀ : bytesAt s₁₀.mem (uA s₀) 32 = bytesAt s₀.mem (uA s₀) 32 :=
    frame_bytesAt F₁₀ (by simpa using hp.u_s) (by omega)
  have hT₁₁ : bytesAt s₁₁.mem (tA s₀) 32 = bytesAt s₀.mem (tA s₀) 32 := by
    rw [m₁₁, bytesAt_writeBytes_sep _ _ (Region.Disjoint.sep (hp.t_s.sub_right (scr_sub s₀ (o := 192) (n := 32)
      (by omega))) (contains_base (Nat.le_refl _)) (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _)))
      (by omega)]
    exact frame_bytesAt F₁₀ (by simpa using hp.t_s) (by omega)
  have sep : ∀ {a b : Nat}, a + 32 ≤ b ∨ b + 32 ≤ a → a + 32 ≤ 256 → b + 32 ≤ 256 → ∀ xs : List Byte,
      xs.length = 32 → Mem.Sep (scA s₀ + BitVec.ofNat 64 a) 32 (scA s₀ + BitVec.ofNat 64 b) xs.length :=
    fun h ha hb xs hx => Region.Disjoint.sep (scr_disj s₀ h ha hb) (contains_base (Nat.le_refl _))
      (by rw [hx]; exact contains_base (Nat.le_refl _))
  have hB : bytesAt s₁₄.mem (blkA s₀) 32 = bytesAt s₀.mem (uA s₀) 32 := by
    rw [hm, bytesAt_writeBytes_sep _ _ (sep (a := 192) (b := 224) (by omega) (by omega) (by omega) _ rfl) (by omega),
      bytesAt_writeBytes_sep _ _ (sep (a := 192) (b := 160) (by omega) (by omega) (by omega) _
        (bytesAt_length _ _ _)) (by omega)]
    have := bytesAt_writeBytes_self s₁₀.mem (blkA s₀) (bytesAt s₁₀.mem (uA s₀) 32) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [this, hU₁₀]
  have hT : bytesAt s₁₄.mem (TA s₀) 32 = bytesAt s₀.mem (tA s₀) 32 := by
    rw [hm, bytesAt_writeBytes_sep _ _ (sep (a := 160) (b := 224) (by omega) (by omega) (by omega) _ rfl) (by omega)]
    have := bytesAt_writeBytes_self (writeBytes s₁₀.mem (blkA s₀) (bytesAt s₁₀.mem (uA s₀) 32)) (TA s₀)
      (bytesAt s₁₁.mem (tA s₀) 32) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length] at this
    rw [this, hT₁₁]
  have hS : Saved s₀ s₁₄.mem := by
    intro p hp'
    have hb := saved_off hp'
    rw [fU.readW (r := sR s₀ p.2 4) (Region.contains_self _ _) ?_ (by decide), m₁₀]
    · exact saveMem_saved hp p hp'
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact scr_disj s₀ (by omega) (by omega) (by omega)
  have hn : arg s₀ 2 = BitVec.ofNat 32 (nn s₀) := by simp [nn]
  refine ⟨⟨⟨by rw [f₁₄.rd, rd₁₃, rd₁₂, rd₁₁, rd₁₀], by rw [f₁₄.wr, wr₁₃, wr₁₂, wr₁₁, wr₁₀],
    by rw [G _ (by decide), esp₁₀], by rw [G _ (by decide), ebx₁₀], by rw [G _ (by decide), ebp₁₀],
    by rw [G _ (by decide), esi₁₀], F'.mono (by simp)⟩, by rw [G _ (by decide), edi₁₀, hn], hS, ?_,
    (Nat.le_refl _), by rw [hB, hT]⟩, ?_⟩
  · rw [hm]
    exact bytesAt_writeBytes_self _ (scA s₀ + BitVec.ofNat 64 224) pad96 (by decide)
  · rw [z₁₄, ← f₁₄.gpr, G _ (by decide), edi₁₀, BitVec.and_self, hn,
      ofNat_beq_zero (by have := (arg s₀ 2).isLt; simp only [nn]; omega)]

/-! ## The epilogue -/

/-- The postcondition. -/
def Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ Proof.Pbkdf2.iterateSha256X86.post s₀ s'

/-- With the key's streaming states as the contract requires, a step is HMAC-SHA-256. -/
theorem stepM_eq {s₀ : State} {k0 : List Byte} (hk : k0.length = 64)
    (hi : Repr s₀.mem (kA s₀) (xorPad k0 ipad)) (ho : Repr s₀.mem (kA s₀ + 96) (xorPad k0 opad))
    {u : List Byte} (hu : u.length = 32) :
    hmacBlockKey sha256 k0 u = stepM s₀ u := by
  have li : (xorPad k0 ipad).length = 64 := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = 64 := by simp [xorPad, hk]
  have ho1 : stateAt s₀.mem (kA s₀ + BitVec.ofNat 64 96) = _ := ho.1
  rw [hmac_step hk hu, stepM, Hi, Ho, ofNat_zero, hi.1, ho1, li, lo]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ 0 s) :
    WP isa (.block epilogue) s (Post s₀) := by
  have := hp.scr_fit; have := hp.t_fit
  unfold epilogue
  refine copyWords_ok (src := .ebp) (dst := .ebx) (by decide) (by decide) (o₁ := 160) (o₂ := 0) 8 _ s _
    h.ebp h.ebx (by omega) (by omega)
    (fun j hj => by
      rw [addr_off (d := 160 + 4 * j) (len := 256) hp.scr_fit (by omega)]; exact InRegions.right (in_scr hp h.wr (by omega)))
    (fun j hj => by rw [addr_off (d := 0 + 4 * j) (len := 32) hp.t_fit (by omega)]; exact in_t hp h.wr (by omega))
    (Region.Disjoint.sep hp.t_s.symm (contains_offset (by omega) (by omega)) (contains_offset (by omega) (by omega)))
    fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  simp only [BitVec.add_zero, Nat.reduceMul] at m₁
  have fT : Frame [tR s₀] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_base (Nat.le_refl _))
  have sv : ∀ p ∈ saved, s₁.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have hb := saved_off hp'
    rw [← h.saved p hp', addr_off (len := 256) hp.scr_fit (by omega)]
    exact fT.readW (r := sR s₀ p.2 4) (Region.contains_self _ _)
      (by simpa using (hp.t_s.sub_right (scr_sub s₀ (o := p.2) (n := 4) (by omega))).symm) (by decide)
  have rin : ∀ d, d + 4 ≤ 256 → InRegions (s₁.rd ++ s₁.wr) (addr (scr s₀) d) 4 := fun d hd => by
    rw [rd₁, wr₁, addr_off (len := 256) hp.scr_fit (by omega)]; exact InRegions.right (in_scr hp h.wr hd)
  simp only [restore, saved, List.map_cons, List.map_nil]
  refine wp_mov fun s₂ u₂ => ?_
  have e₂ : s₂.gpr .eax = scr s₀ := by rw [u₂.gpr, g₁ _ (by decide), h.ebp]
  refine wp_movm (a := addr (scr s₀) 112) (by rw [ea_at, e₂]) (by rw [u₂.rd, u₂.wr]; exact rin 112 (by omega))
    fun s₃ u₃ => ?_
  refine wp_movm (a := addr (scr s₀) 116) (by rw [ea_at, u₃.other _ (by decide), e₂])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact rin 116 (by omega)) fun s₄ u₄ => ?_
  refine wp_movm (a := addr (scr s₀) 120) (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact rin 120 (by omega)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (scr s₀) 124)
    (by rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact rin 124 (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have hm₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun k0 hk hi ho => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem]
      exact sv (.ebx, 112) (by simp [saved])
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem]
      exact sv (.esi, 116) (by simp [saved])
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem]
      exact sv (.edi, 120) (by simp [saved])
    · rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
      exact sv (.ebp, 124) (by simp [saved])
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), g₁ _ (by decide), h.esp]
  · rw [hm₆]
    refine (h.frame.trans (fT.mono (by simp))).readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_t, hp.ret_s, ret_stk hp]
  · have := h.val
    simp only [Spec.Pbkdf2.iterate] at this
    have e : bytesAt s₆.mem (tA s₀) 32 = bytesAt s.mem (TA s₀) 32 := by
      have := bytesAt_writeBytes_self s.mem (tA s₀) (bytesAt s.mem (TA s₀) 32) (by rw [bytesAt_length]; omega)
      rw [bytesAt_length] at this
      rw [hm₆, m₁, this]
    show bytesAt s₆.mem (tA s₀) 32 = _
    rw [e, ← this]
    exact (iterate_congr (fun u hu => stepM_eq hk hi ho hu) (fun u => Pbkdf2.digest_length _) _ _ _
      (bytesAt_length _ _ _)).symm

/-! ## Correctness -/

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa iterate s₀ (Post s₀) := by
  unfold iterate
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  exact WP.seq (WP.mono (loop_ok hp h₁ z₁) fun s₂ h₂ => epilogue_ok hp h₂)

/-! ## Constant time -/

/-- The initial taint: the stack arguments are public, the words holding `t`
and `scratch` are the base addresses of the writable regions, and the 20
bytes below `esp` are outside them. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 256], argLen := 24,
    argBases := [(16, 0), (20, 1)], room := 20 }

theorem wf₀ {s : State} (h : Proof.Pbkdf2.iterateSha256X86.pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hp := pre_of h
  have ht := hp.t_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.t_s, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_t hp.a_t
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_s hp.a_s
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [k1, k2]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Pbkdf2.iterateSha256X86.pre s₁)
    (h₂ : Proof.Pbkdf2.iterateSha256X86.pre s₂) (hpub : Proof.Pbkdf2.iterateSha256X86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [tR, scR, tA, scA, tP, scr, ha 3 (by omega), ha 4 (by omega)]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    have f₁ : (s₁.gpr .esp).toNat + 24 ≤ 2 ^ 32 := hp₁.sp_fit
    have f₂ : (s₂.gpr .esp).toNat + 24 ≤ 2 ^ 32 := hp₂.sp_fit
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000, 0x5000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else
  if a = 0x4015 then 0x50 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 192⟩, ⟨0x2000, 32⟩, ⟨0x4004, 20⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x5000, 256⟩]

theorem sat_pre : Proof.Pbkdf2.iterateSha256X86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a1 : arg sat 1 = 0x2000 := by decide
  have a3 : arg sat 3 = 0x3000 := by decide
  have a4 : arg sat 4 = 0x5000 := by decide
  have e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Pbkdf2.iterateSha256X86, a0, a1, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, sat] at h₁ h₂
    bv_omega

theorem iterate_correct (s : State) (hs : Proof.Pbkdf2.iterateSha256X86.pre s) :
    ∃ t s', Exec isa iterate s t s' ∧ abiPreserved s s' ∧ Proof.Pbkdf2.iterateSha256X86.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem iterate_ct : ConstantTime isa Proof.Pbkdf2.iterateSha256X86.pre
    Proof.Pbkdf2.iterateSha256X86.pub iterate :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-! ## The shared contract -/

/-- `iterateSha256X86` with the 832 bytes of scratch of the shared contract
(sized for the x86-64 AVX2 compression function), of which the code uses
256, and its arguments writable, as the shared contract lets them be. -/
def iterateWide : Contract isa :=
  { Proof.Pbkdf2.iterateSha256X86 with
    pre := fun s =>
      let key : Region := ⟨(arg s 0).setWidth 64, 192⟩
      let u : Region := ⟨(arg s 1).setWidth 64, 32⟩
      let t : Region := ⟨(arg s 3).setWidth 64, 32⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 832⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [key, u] ∧ s.wr = [t, scratch, args] ∧
      key.Disjoint t ∧ key.Disjoint scratch ∧ u.Disjoint t ∧ u.Disjoint scratch ∧ t.Disjoint scratch ∧
      args.Disjoint t ∧ args.Disjoint scratch ∧ ret.Disjoint t ∧ ret.Disjoint scratch ∧
      stack.Disjoint key ∧ stack.Disjoint u ∧ stack.Disjoint t ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 832 ≤ 2 ^ 32 ∧
      20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

/-- The regions `iterateSha256X86` lets the code read and write. -/
def narrowRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 1).setWidth 64, 32⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region := [⟨(arg s 3).setWidth 64, 32⟩, ⟨(arg s 4).setWidth 64, 256⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Pbkdf2.iterateSha256X86, VG.Proof.Pbkdf2.X86.iterateWide,
    VG.Proof.Pbkdf2.X86.narrowRd, VG.Proof.Pbkdf2.X86.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem iterateWide_pre (s : State) (h : iterateWide.pre s) :
    Proof.Pbkdf2.iterateSha256X86.pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀,
    h₂₁⟩ := h
  narrow
  exact ⟨trivial, trivial, h₃, h₄.sub_right (Region.sub_of_ble rfl), h₅, h₆.sub_right (Region.sub_of_ble rfl),
    h₇.sub_right (Region.sub_of_ble rfl), h₈, h₉.sub_right (Region.sub_of_ble rfl), h₁₀,
    h₁₁.sub_right (Region.sub_of_ble rfl), h₁₂, h₁₃, h₁₄, h₁₅.sub_right (Region.sub_of_ble rfl), h₁₆, h₁₇,
    h₁₈, Region.end_le_of_ble rfl h₁₉, h₂₀, h₂₁⟩

/-- A state satisfying `iterateWide.pre`. -/
def wideSat : State :=
  { sat with rd := [⟨0x1000, 192⟩, ⟨0x2000, 32⟩], wr := [⟨0x3000, 32⟩, ⟨0x5000, 832⟩, ⟨0x4004, 20⟩] }

theorem iterateWide_implies : iterateWide.Implies (Spec.Pbkdf2.iterateSha256Contract X86.abi 20) := by
  have a0 : arg wideSat 0 = 0x1000 := by decide
  have a1 : arg wideSat 1 = 0x2000 := by decide
  have a2 : arg wideSat 2 = 0 := by decide
  have a3 : arg wideSat 3 = 0x3000 := by decide
  have a4 : arg wideSat 4 = 0x5000 := by decide
  have e : argAddr wideSat 0 = 0x4004 := by decide
  have esp : wideSat.gpr .esp = 0x4000 := rfl
  sig_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig, iterateWide,
    Proof.Pbkdf2.iterateSha256X86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp] using wideSat

/-- The proof is written against `iterateSha256X86`, widened to the shared
contract's scratch and to writable arguments. -/
theorem iterate_verified :
    Verified X86.target Impl.Pbkdf2.X86.iterate (Spec.Pbkdf2.iterateSha256Contract X86.abi 20) :=
  have hsat := iterateWide_implies.sat_left
  (Verified.narrowTo (Verified.of_correct iterate_correct iterate_ct (.refl ⟨sat, sat_pre⟩))
    narrowRd narrowWr iterateWide_pre
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
          0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies iterateWide_implies

end VG.Proof.Pbkdf2.X86
