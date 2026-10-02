import VerifiedGarbage.Proof.AesGcm.X86.OneTag

/-!
# AES-GCM on x86: `vg_aes_gcm_seal`

Untrusted: everything here is checked by Lean. The entry (`oneEntry_pc`),
`J₀` and the additional data (`oneAad_pc`), the data encrypted
(`oneCrypt_pc`), the tag into `W` (`oneTag_pc`) and the exit, as one `Pc`
(`seal_pc`): correct (`seal_correct`) and constant time (`seal_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph zeros padLen inc32 ghash ghashFrom blocks toBytes ofBytes gctr
  fullTag encryptWith)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock)

/-- The padded input of GHASH, as `seal` and `open` absorb it: the
additional data padded, then the data, padded. -/
theorem padded_eq (a c : List Byte) :
    Proof.Gcm.padded a c = a ++ zeros (padLen a.length) ++ c ++
      zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) := by
  by_cases hc : c = []
  · subst hc
    have h0 : padLen (a ++ zeros (padLen a.length)).length = 0 := by
      have := Proof.Gcm.length_pad_mod a.length
      simp only [List.length_append, Proof.Gcm.length_zeros, padLen] at this ⊢; omega
    simp only [Proof.Gcm.padded, Proof.Gcm.ghashInput_nil, List.append_nil, h0]
    simp [zeros]
  · simp only [Proof.Gcm.padded, Proof.Gcm.ghashInput_of_ne hc]

theorem toBytes_take16 (x : Block) : (toBytes x).take 16 = toBytes x :=
  List.take_of_length_le (by rw [Proof.Cmac.toBytes_length])

section
variable {p : BitVec 32 × (Nat → BitVec 32)} (G : OL p)
include G

/-- A block of the state before the counter block, apart from what `crypt` writes. -/
theorem st_crFrameO {d : Nat} (hd : d + 16 ≤ 48) :
    ∀ r ∈ crFrame (stOf (p.2 8)) (p.2 8) p.1 28 (p.2 6) (p.2 7).toNat,
      (⟨w64 (stOf (p.2 8)) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (G.d_w.sub_right (by rw [st_eq G]; exact Lay.wSub (by omega))).symm
  · exact Lay.st_st (.inl (by omega)) (by omega) (by decide)
  · exact G.L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  · exact (G.L.stk_st (by omega)).symm

/-- The data, apart from the regions of `W` and the stack the pieces write. -/
theorem d_oF : ∀ r ∈ oF p, (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.d_w.sub_right (Lay.wSub (by decide))
  · exact G.k_d.symm

theorem d_woF {o : Nat} (ho : o + 16 ≤ 2560) :
    ∀ r ∈ ⟨w64 (p.2 8) + BitVec.ofNat 64 o, 16⟩ :: oF p, (⟨w64 (p.2 6), (p.2 7).toNat⟩ : Region).Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact G.d_w.sub_right (Lay.wSub ho)
  · exact d_oF G r hr

end

theorem seal_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => onePre 9 s₀ ∧ pubOf 9 s₀ = p ∧ s = s₀) «seal»
      (fun s₀ s' => abiPreserved s₀ s' ∧ sealX86.post s₀ s') := by
  by_cases hex : ∃ s₀, onePre 9 s₀ ∧ pubOf 9 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have G : OL p := (op_of hz).ol (by decide) hzp
  have L := G.L
  -- The entry, `J₀` and the additional data.
  refine Pc.seq (oneEntry_pc 9 (.inl rfl) [] (.inl rfl) (fun h => absurd rfl h) (onePre 9) (fun _ h => op_of h) p G
    (by taint_decide)) ?_
  refine Pc.seq (Pc.lift (oneAad_pc G) (fun s₀ s => (s₀, s)) fun s₀ s h => ⟨h.1, rfl⟩) ?_
  -- The data encrypted.
  refine Pc.seq (Pc.lift (oneCrypt_pc G (fun s₀ => inc32 (jOf p s₀))) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨_, _, ⟨ha, _⟩, _⟩ => ⟨⟨ha.o, Proof.Gcm.ctr_zero _ _ _ _ ha.cb⟩, rfl⟩) ?_
  -- The tag.
  refine Pc.seq (Pc.lift (oneTag_pc G (o := 0) (.inl rfl)) (fun s₀ s => (s₀, s))
    fun s₀ s ⟨s₂, ⟨_, _, ⟨ha, _⟩, _⟩, ⟨o', _, fC⟩, _⟩ => ⟨⟨o', ?_, ?_⟩, rfl⟩) ?_
  · have := blockAt_frame fC (st_crFrameO G (d := 0) (by decide))
    rw [BitVec.add_zero] at this
    rw [this]; exact ha.j
  · have hl : (xA p s₀).length % 16 = 0 := by
      simp only [xA, List.length_append, length_bytesAt, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    exact ha.y.congr (blockAt_frame fC (st_crFrameO G (by decide))) (by rw [hl]; rfl)
  -- The exit.
  refine Pc.taint [.ebp] (fun s₀ s ⟨s₃, ⟨s₂, ⟨sE, ⟨hE, _, hpub, _⟩, ⟨_, fA⟩, _⟩, ⟨_, hc, _⟩, _⟩, ⟨o₄, ht, fT⟩, _⟩ => ?_)
    (fun _ _ s₁ s₂ ⟨_, _, ⟨o₁, _⟩, _⟩ ⟨_, _, ⟨o₂, _⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [o₁.env.ebp, o₂.env.ebp]) (by taint_decide)
  have esp := pubOf_esp hpub
  have a : ∀ i, i < 9 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
  refine WP.mono (exit_ok o₄.env.ebp (by rw [o₄.env.esp, esp]) (covers_left o₄.env.wW) L.fw o₄.saved
    (by rw [esp]; exact o₄.ret)) fun s' ⟨abi, m', _, _, _⟩ => ⟨abi, ?_⟩
  have hD₂ : bytesAt s₂.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat := by
    rw [bytesAt_frame fA (d_oF G) (by have := G.fd; omega)]; exact hE.data
  have hD₄ : bytesAt s.mem (w64 (p.2 6)) (p.2 7).toNat = bytesAt s₃.mem (w64 (p.2 6)) (p.2 7).toNat :=
    bytesAt_frame (oT_oF fT) (d_woF G (by decide)) (by have := G.fd; omega)
  have hcg : gctr (ctxCiph s₀.mem (w64 (p.2 0)) (p.2 1).toNat) (inc32 (jOf p s₀))
      (bytesAt s₀.mem (w64 (p.2 6)) (p.2 7).toNat) = bytesAt s₃.mem (w64 (p.2 6)) (p.2 7).toNat := by
    rw [hc, hD₂, Proof.Gcm.gctr_eq]
  simp only [sealX86]
  rw [a 0 (by decide), a 1 (by decide), a 2 (by decide), a 3 (by decide), a 4 (by decide), a 5 (by decide),
    a 6 (by decide), a 7 (by decide), a 8 (by decide), m']
  simp only [encryptWith]
  rw [hcg, hD₄, Prod.mk.injEq]
  refine ⟨rfl, ?_⟩
  rw [BitVec.add_zero] at ht
  rw [ht, Proof.Gcm.fullTag_eq, toBytes_take16, padded_eq, length_bytesAt, length_bytesAt]

theorem seal_correct (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' :=
  (seal_pc (pubOf 9 s)).wp s s ⟨hs, rfl, rfl⟩

theorem seal_ct : ConstantTime isa sealX86.pre sealX86.pub «seal» :=
  Pc.constantTime (pubOf 9) (fun _ _ _ _ h => pubOf_eq h) seal_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86
