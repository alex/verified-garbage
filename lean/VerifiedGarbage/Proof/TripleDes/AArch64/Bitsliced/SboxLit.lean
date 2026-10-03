import VerifiedGarbage.Impl.TripleDes.AArch64.Bitsliced
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # The AdvSIMD S-box circuits' and transposition's code, and the circuits' output registers, as literals -/

namespace VG.Impl.TripleDes.AArch64.BitsliceNeon

open VG.AArch64

def sbox0 : Prog isa := .block (sboxCode 0)
def sbox1 : Prog isa := .block (sboxCode 1)
def sbox2 : Prog isa := .block (sboxCode 2)
def sbox3 : Prog isa := .block (sboxCode 3)
def sbox4 : Prog isa := .block (sboxCode 4)
def sbox5 : Prog isa := .block (sboxCode 5)
def sbox6 : Prog isa := .block (sboxCode 6)
def sbox7 : Prog isa := .block (sboxCode 7)

materialize_code sbox0
materialize_code sbox1
materialize_code sbox2
materialize_code sbox3
materialize_code sbox4
materialize_code sbox5
materialize_code sbox6
materialize_code sbox7

def transposeProg : Prog isa := .block transpose

materialize_code transposeProg

end VG.Impl.TripleDes.AArch64.BitsliceNeon

namespace VG

materialize_value Impl.TripleDes.AArch64.BitsliceNeon.outRegsTable

end VG
