import VerifiedGarbage.Proof.Argon2.X86.HPrime.Body

/-!
# Argon2 H′ on x86 (32-bit): the output

`Out s₀ s xs`: the output so far, `xs`, its pointer and the bytes left.
`emit_ok` writes a 32-byte prefix of the digest, `copyRemaining_ok` the last
bytes.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (copy outOff leftOff emitPrefix copyRemaining)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_movi wp_movm wp_store wp_subi contains_addr)

/-- The output so far. -/
structure Out (s₀ s : State) (xs : List Byte) : Prop where
  ptr : OutPtr s₀ s xs.length
  left : s.mem.readW (addr (scr s₀) leftOff) 32 = BitVec.ofNat 32 (ol s₀ - xs.length)
  bytes : bytesAt s.mem ((op s₀).setWidth 64) xs.length = xs
  len : xs.length ≤ ol s₀

/-- The digest. -/
abbrev digest (s₀ s : State) : List Byte := bytesAt s.mem (P s₀ + 768) 64

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- The output and its slots are kept by the hash macros. -/
theorem Out.keeps {s t : State} {xs : List Byte} (h : Out s₀ s xs)
    (k : Keeps (scr s₀) (esp₀ s₀) s t) : Out s₀ t xs := by
  refine ⟨?_, ?_, ?_, h.len⟩
  · show _ = _; rw [keeps_word hp k (by decide) (by decide)]; exact h.ptr
  · rw [keeps_word hp k (by decide) (by decide)]; exact h.left
  · have kb := k.bytes (R := ⟨(op s₀).setWidth 64, xs.length⟩)
      (by have := h.len; have := hp.out_fits; simp; omega)
      ((hp.out_scr.sub_left (Region.sub_prefix h.len)).sub_right (Region.sub_prefix (by decide)))
      ((hp.stk_out.sub_right (Region.sub_prefix h.len)).symm)
    simp only at kb
    rw [kb]; exact h.bytes

/-- A word of `scratch` outside the output pointer's slot is kept by `copy`. -/
theorem copy_word {s t : State} {k n : Nat} (hkn : k + n ≤ ol s₀)
    (f : Frame [⟨(op s₀).setWidth 64 + BitVec.ofNat 64 k, n⟩, ⟨P s₀ + BitVec.ofNat 64 outOff, 4⟩]
      s.mem t.mem) {d : Nat} (hd : d + 4 ≤ 16384) (hd' : d + 4 ≤ outOff ∨ outOff + 4 ≤ d) :
    t.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
  have ho := hp.out_fits
  refine f.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  rw [scr_addr hp (by omega)]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ((hp.out_scr.sub_left (Offset.sub_base _ (by omega))).sub_right
      (Offset.sub_base _ hd)).symm
  · exact Offset.disjoint _ hd' (by omega) (by simp only [outOff]; omega)

/-- Emit `n` digest bytes after the output `xs`. -/
theorem copyOut_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs) {n : Nat}
    (hn : s.gpr .esi = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : xs.length + n ≤ ol s₀) :
    WP isa copy s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (xs.length + n) = xs ++ (digest s₀ s).take n ∧
      OutPtr s₀ t (xs.length + n) ∧
      t.mem.readW (addr (scr s₀) leftOff) 32 = s.mem.readW (addr (scr s₀) leftOff) 32 ∧
      digest s₀ t = digest s₀ s := by
  have ho := hp.out_fits
  refine (copy_ok hp b h.ptr hn hn₁ hn₂ hkn).mono ?_
  rintro t ⟨bt, pt, bytes, ebp, f⟩
  refine ⟨bt, ebp, ?_, pt, copy_word hp hkn f (by decide) (by decide), ?_⟩
  swap
  · refine Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := ⟨P s₀ + 768, 64⟩) (fun r hr => ?_)
      (by simp) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ((hp.out_scr.sub_left (Offset.sub_base _ (d := xs.length) (n := n) (k := ol s₀) (by omega))).sub_right
        (Offset.sub_base (P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
    · exact Offset.disjoint (P s₀) (d := 768) (n := 64) (e := outOff) (k := 4) (by decide) (by decide)
        (by decide)
  have old : bytesAt t.mem ((op s₀).setWidth 64) xs.length = bytesAt s.mem ((op s₀).setWidth 64) xs.length := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := ⟨(op s₀).setWidth 64, xs.length⟩)
      (fun r hr => ?_) (by have := h.len; simp; omega) hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.base_disjoint _ (by omega) (by omega)
    · exact (hp.out_scr.sub_left (Region.sub_prefix (by omega))).sub_right
        (Offset.sub_base _ (by decide))
  rw [Proof.Blake2.bytesAt_add, bytes, bytesAt_take _ _ _ _ hn₂, old, h.bytes]

/-- Emit a 32-byte prefix of the digest. -/
theorem emit_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hkn : xs.length + 32 ≤ ol s₀) :
    WP isa emitPrefix s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      Out s₀ t (xs ++ (digest s₀ s).take 32) ∧ digest s₀ t = digest s₀ s := by
  have ho := hp.out_fits
  have hs := hp.scr_fits
  unfold emitPrefix
  refine WP.seq (wp_movi fun s₁ u₁ => WP.block_nil ?_)
  have b₁ : Body s₀ s₁ := ⟨by rw [u₁.other _ (by decide), b.ebx], by rw [u₁.other _ (by decide), b.esp],
    by rw [u₁.rd, b.rd], by rw [u₁.wr, b.wr], by rw [u₁.mem]; exact b.frame,
    fun q hq => by rw [u₁.mem]; exact b.saved q hq, by rw [u₁.mem]; exact b.pfx⟩
  have h₁ : Out s₀ s₁ xs := ⟨by show _ = _; rw [u₁.mem]; exact h.ptr, by rw [u₁.mem]; exact h.left,
    by rw [u₁.mem]; exact h.bytes, h.len⟩
  refine WP.seq ((copyOut_ok hp b₁ h₁ u₁.gpr (by decide) (by decide) hkn).mono
    fun s₂ ⟨b₂, e₂, by₂, p₂, l₂, d₂⟩ => ?_)
  have rl : InRegions (s₂.rd ++ s₂.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b₂.rd, b₂.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine wp_movm (VG.Proof.Sha512.X86.ea_of b₂.ebx leftOff) rl fun s₃ u₃ => wp_subi fun s₄ u₄ _ => ?_
  have ebx₄ : s₄.gpr .ebx = scr s₀ := by rw [u₄.other _ (by decide), u₃.other _ (by decide), b₂.ebx]
  have wl : InRegions s₄.wr (addr (scr s₀) leftOff) 4 := by
    rw [u₄.wr, u₃.wr, b₂.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine wp_store (VG.Proof.Sha512.X86.ea_of ebx₄ leftOff) wl fun s₅ u₅ => WP.block_nil ?_
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have d₁ : digest s₀ s₁ = digest s₀ s := by simp only [digest, u₁.mem]
  have v₄ : s₄.gpr .eax = BitVec.ofNat 32 (ol s₀ - (xs.length + 32)) := by
    rw [u₄.gpr, u₃.gpr, l₂, u₁.mem, h.left]
    exact (Proof.Sha256.X86.Stream.sub_ofNat (a := ol s₀ - xs.length) (b := 32) (by omega)).trans
      (by congr 1)
  have e₅ : s₅.mem = s₂.mem.writeW (P s₀ + BitVec.ofNat 64 leftOff) (BitVec.ofNat 32 (ol s₀ - (xs.length + 32))) := by
    rw [u₅.mem, m₄, v₄, scr_addr hp (by decide)]
  have F : Frame [⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩] s₂.mem s₅.mem := by
    rw [e₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have keepW : ∀ d, d + 4 ≤ 16384 → (d + 4 ≤ leftOff ∨ leftOff + 4 ≤ d) →
      s₅.mem.readW (addr (scr s₀) d) 32 = s₂.mem.readW (addr (scr s₀) d) 32 := fun d hd hd' => by
    rw [e₅, scr_addr hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ hd' (by omega) (by simp only [leftOff]; omega)) (by decide)
  have keepB : ∀ R : Region, R.len ≤ 2 ^ 64 → R.Disjoint ⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩ →
      bytesAt s₅.mem R.base R.len = bytesAt s₂.mem R.base R.len := fun R hR hd =>
    Proof.Blake2.bytesAt_congr fun i hi => F.bytes (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) hR hi
  have slotScr : Region.Sub ⟨P s₀ + BitVec.ofNat 64 leftOff, 4⟩ (scrR s₀) := Offset.sub_base _ (by decide)
  have len' : (xs ++ (digest s₀ s).take 32).length = xs.length + 32 := by
    simp [digest, bytesAt]
  refine ⟨⟨by rw [u₅.gpr, ebx₄], by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), b₂.esp],
      by rw [u₅.rd, u₄.rd, u₃.rd, b₂.rd], by rw [u₅.wr, u₄.wr, u₃.wr, b₂.wr],
      b₂.frame.trans (F.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, slotScr⟩),
      fun q hq => ?_, ?_⟩,
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), e₂, u₁.other _ (by decide)], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have hb : 832 ≤ q.2 ∧ q.2 + 4 ≤ leftOff := by
      simp only [Impl.Argon2.X86.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [keepW _ (by simp only [leftOff] at hb; omega) (.inl hb.2)]; exact b₂.saved q hq
  · rw [keepB ⟨P s₀ + 832, 4⟩ (by simp) (Offset.disjoint (P s₀) (d := 832) (n := 4) (e := leftOff) (k := 4)
      (by decide) (by decide) (by decide))]
    exact b₂.pfx
  · show _ = _
    rw [len', keepW _ (by decide) (by decide)]; exact p₂
  · rw [len', e₅, scr_addr hp (by decide), Mem.readW_writeW_self32]
  · rw [len']
    have k₁ := keepB ⟨(op s₀).setWidth 64, xs.length + 32⟩ (by simp; omega)
      ((hp.out_scr.sub_left (Region.sub_prefix (by omega))).sub_right slotScr)
    simp only at k₁
    rw [k₁, by₂, d₁]
  · rw [len']; exact hkn
  · have k₂ := keepB ⟨P s₀ + 768, 64⟩ (by simp) (Offset.disjoint (P s₀) (d := 768) (n := 64)
      (e := leftOff) (k := 4) (by decide) (by decide) (by decide))
    simp only at k₂
    show bytesAt _ _ _ = bytesAt _ _ _
    rw [k₂]; exact d₂.trans d₁

/-- Copy the bytes left. -/
theorem copyRemaining_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hn₁ : xs.length < ol s₀) (hn₂ : ol s₀ - xs.length ≤ 64) :
    WP isa copyRemaining s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (ol s₀) = xs ++ (digest s₀ s).take (ol s₀ - xs.length) := by
  have hs := hp.scr_fits
  unfold copyRemaining
  have rl : InRegions (s.rd ++ s.wr) (addr (scr s₀) leftOff) 4 := by
    rw [b.rd, b.wr]; exact ⟨scrR s₀, by simp [hp.wr], contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of b.ebx leftOff) rl fun s₁ u₁ => WP.block_nil ?_)
  have b₁ : Body s₀ s₁ := ⟨by rw [u₁.other _ (by decide), b.ebx], by rw [u₁.other _ (by decide), b.esp],
    by rw [u₁.rd, b.rd], by rw [u₁.wr, b.wr], by rw [u₁.mem]; exact b.frame,
    fun q hq => by rw [u₁.mem]; exact b.saved q hq, by rw [u₁.mem]; exact b.pfx⟩
  have h₁ : Out s₀ s₁ xs := ⟨by show _ = _; rw [u₁.mem]; exact h.ptr, by rw [u₁.mem]; exact h.left,
    by rw [u₁.mem]; exact h.bytes, h.len⟩
  refine (copyOut_ok hp b₁ h₁ (n := ol s₀ - xs.length) (by rw [u₁.gpr, h.left]) (by omega) hn₂
    (by omega)).mono fun t ⟨bt, et, byt, _, _, _⟩ => ⟨bt, by rw [et, u₁.other _ (by decide)], ?_⟩
  rw [show xs.length + (ol s₀ - xs.length) = ol s₀ by omega] at byt
  rw [byt]; simp only [digest, u₁.mem]

end

end VG.Proof.Argon2.X86.HPrime
